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
open Box.Key
open Box.Index
open Box.Plain

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

let dh_element_size = HSalsa.keylen // is equal to scalar lenght in Spec.Curve25519
let dh_exponent_size = 32 // Size of scalar in Curve25519. Replace with constant in spec?
let dh_share = Curve.serialized_point //
let dh_basepoint = [
    0x09uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
    0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
    0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
    0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
    ]

let dh_exponent = Curve.scalar // is equal to Curve.serialized_point

let smaller i1 i2 =
  let i1' = LE.little_endian i1 in
  let i2' = LE.little_endian i2 in
  i1' < i2'

#set-options "--z3rlimit 300 --max_ifuel 0 --max_fuel 0"
let total_order_lemma i1 i2 = admit()

//val total_order_lemma': (i1:dh_share -> i2:dh_share -> Lemma
//  (requires True)
//  (ensures
//    (b2t (smaller i1 i2) ==> (forall i. i <> i1 /\ i <> i2 /\ b2t (smaller i i1) ==> b2t (smaller i i2)))
//    /\ (~ (b2t (smaller i1 i2)) <==> (i1 = i2 \/ b2t (smaller i2 i1)))))
(**
Nonce to use with HSalsa.hsalsa20.
*)
private let zero_nonce = Seq.create HSalsa.noncelen (UInt8.uint_to_t 0)

let share_from_exponent dh_exp = Curve.scalarmult dh_exp (createL dh_basepoint)

abstract noeq type odh_module' (im:index_module) (imk:key_index_module) (km:key_module imk) = // require subId type to be dh_share?
  | ODH:
    rgn:(r:HH.rid) ->
    odh_module' im imk km

let odh_module = odh_module'

let create im imk km rgn =
  ODH rgn

noeq abstract type pkey' =
  | PKEY: pk_share:dh_share -> pkey'

let pkey = pkey'

noeq abstract type skey' =
  | SKEY: sk_exp:dh_exponent -> pk:pkey{pk.pk_share = share_from_exponent sk_exp} -> skey'

let skey = skey'

let get_pkey sk = sk.pk

#set-options "--z3rlimit 300 --max_ifuel 1 --max_fuel 0"
let compatible_keys sk pk =
  sk.pk =!= pk

let pk_get_share k = k.pk_share

let lemma_pk_get_share_inj pk = ()

let get_skeyGT sk =
  sk.sk_exp

let sk_get_share sk = sk.pk.pk_share

#set-options "--z3rlimit 300 --max_ifuel 1 --max_fuel 0"
let leak_skey im sk =
  sk.sk_exp

let keygen () =
  let dh_exponent = random_bytes (UInt32.uint_to_t 32) in
  let dh_pk = PKEY (share_from_exponent dh_exponent) in
  let dh_sk = SKEY dh_exponent dh_pk in
  dh_pk,dh_sk

let coerce_pkey im dh_sh =
  PKEY dh_sh

let coerce_keypair im dh_ex =
  let dh_sh = share_from_exponent dh_ex in
  let pk = PKEY dh_sh in
  let sk = SKEY dh_ex pk in
  pk,sk

let compose_ids s1 s2 =
  if smaller s1 s2 then
     let i = (s1,s2) in
     i
  else
    (total_order_lemma s1 s2;
    let i = (s2,s1) in
    i)

let prf_odhGT sk pk =
  let i = compose_ids pk.pk_share sk.pk.pk_share in
  let raw_k = Curve.scalarmult sk.sk_exp pk.pk_share in
  let k = HSalsa.hsalsa20 raw_k zero_nonce in
  k

let lemma_shares sk = ()


#reset-options
#set-options "--z3refresh --z3rlimit 1000 --max_ifuel 2 --max_fuel 2"
let prf_odh im imk km om sk pk = 
  let i1 = pk.pk_share in
  let i2 = sk.pk.pk_share in
  let i = compose_ids i1 i2 in
  recall_log im;
  lemma_honest_or_dishonest im i;
  match get_honest imk i with
  | true ->
    let k = Key.gen imk km i in
    k
  | false ->
    let raw_k = Curve.scalarmult sk.sk_exp pk.pk_share in
    let hashed_raw_k = HSalsa.hsalsa20 raw_k zero_nonce in
    let k=Key.coerce imk km i hashed_raw_k in
    k
