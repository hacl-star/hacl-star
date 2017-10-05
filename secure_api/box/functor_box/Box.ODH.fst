(**
   TODO: - Documentation, some cleanup.
*)
module Box.ODH
open FStar.Set
open FStar.HyperHeap
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Monotonic.RRef
open FStar.Seq
open FStar.Monotonic.Seq
open FStar.List.Tot

open Crypto.Symmetric.Bytes

open Box.Flags

module MR = FStar.Monotonic.RRef
module MM = MonotoneMap
module HS = FStar.HyperStack
module HH = FStar.HyperHeap
module HSalsa = Spec.HSalsa20
module Curve = Spec.Curve25519
module Plain = Box.Plain
module Key = Box.Key
module ID = Box.Index
module LE = FStar.Endianness

let smaller' n i1 i2 =
  let i1' = LE.little_endian i1 in
  let i2' = LE.little_endian i2 in
  i1' < i2'

let smaller om i1 i2 = smaller' om.dh_share_length i1 i2

//let share_from_exponent' dh_exp = Curve.scalarmult dh_exp Curve.base_point

let hash_fun om = om.hash
let dh_exponentiate om = om.exponentiate
let share_from_exponent om exp = om.exponentiate exp om.base_point

noeq abstract type pkey' (om:odh_module) =
  | PKEY: pk_share:dh_share om-> pkey' om

noeq abstract type skey' (om:odh_module) =
  | SKEY: sk_exp:dh_exponent om -> pk:pkey' om{pk.pk_share = om.exponentiate sk_exp om.base_point} -> skey' om

let skey = skey'
let pkey = pkey'

let get_pkey om sk = sk.pk

#set-options "--z3rlimit 300 --max_ifuel 1 --max_fuel 0"
let compatible_keys om sk pk =
  sk.pk =!= pk

let get_hash_length om = om.hash_length
let get_dh_share_length om = om.dh_share_length
let get_dh_exponent_length om = om.dh_exponent_length
let get_base_point om = om.base_point
let get_index_module om = om.im
let get_key_index_module om = om.kim
let get_key_module om kim = om.km

#set-options "--z3rlimit 300 --max_ifuel 0 --max_fuel 0"
let total_order_lemma om i1 i2 =
  let i1:dh_share om = i1 in
  let i2:dh_share om = i2 in
  LE.lemma_little_endian_bij i1 i2

#set-options "--z3rlimit 300 --max_ifuel 1 --max_fuel 0"
let create hash_len dh_share_len dh_exp_len hash_fun exponentiate base_point im kim km rgn =
  ODH rgn hash_len dh_share_len dh_exp_len hash_fun exponentiate base_point im kim km

let pk_get_share om k = k.pk_share

let lemma_pk_get_share_inj om pk = ()

let get_skeyGT om sk =
  sk.sk_exp

let sk_get_share om sk =
  let pk_sh = sk.pk.pk_share in
  assert(pk_sh = (dh_exponentiate om) (sk.sk_exp) om.base_point);
  admit();
  sk.pk.pk_share

#set-options "--z3rlimit 300 --max_ifuel 1 --max_fuel 0"
let leak_skey om sk =
  sk.sk_exp

assume val boundless_random_bytes: n:nat -> lbytes n

let keygen om =
  let dh_exponent = boundless_random_bytes om.dh_exponent_length in
  let dh_pk = PKEY (share_from_exponent om dh_exponent) in
  let dh_sk = SKEY dh_exponent dh_pk in
  dh_pk,dh_sk

let coerce_pkey om dh_sh =
  PKEY dh_sh

let coerce_keypair om dh_ex =
  let dh_sh = share_from_exponent om dh_ex in
  let pk = PKEY dh_sh in
  let sk = SKEY dh_ex pk in
  pk,sk

let compose_ids om s1 s2 =
  if smaller om s1 s2 then
     let i = (s1,s2) in
     i
  else
    (total_order_lemma om s1 s2;
    let i = (s2,s1) in
    i)

let prf_odhGT om sk pk =
  let raw_k = (dh_exponentiate om) sk.sk_exp pk.pk_share in
  let k = (hash_fun om) raw_k in
  k

let lemma_shares om sk = ()


let prf_odh om sk pk =
  let i1 = pk.pk_share in
  let i2 = sk.pk.pk_share in
  let i = compose_ids om i1 i2 in
  ID.recall_log om.im;
  ID.recall_log om.kim;
  ID.lemma_honest_or_dishonest om.kim i;
  let honest_i = ID.get_honest om.kim i in
  match honest_i && Flags.prf_odh with
  | true ->
    let k = Key.gen om.kim om.km i in
    k
  | false ->
    //let raw_k = Curve.scalarmult sk.sk_exp pk.pk_share in
    let raw_k = om.exponentiate sk.sk_exp pk.pk_share in
    //let hashed_raw_k = HSalsa.hsalsa20 raw_k zero_nonce in
    let hashed_raw_k = om.hash raw_k in
    if not honest_i then
      Key.coerce om.kim om.km i hashed_raw_k
    else
      Key.set om.kim om.km i hashed_raw_k
