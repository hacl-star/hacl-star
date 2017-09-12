(**
  This module represents the PKAE cryptographic security game expressed in terms of the underlying cryptobox construction.
*)
module Box.PKAE


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
module SPEC = Spec.SecretBox
module Plain = Box.Plain
module Key = Box.Key
module ID = Box.Index
module ODH = Box.ODH
module AE = Box.AE
module LE = FStar.Endianness

let nonce = AE.nonce
let cipher = AE.cipher
let sub_id = ODH.dh_share
let key_id = ODH.key_id 

#set-options "--z3rlimit 600 --max_ifuel 1 --max_fuel 1"
let compose_ids i1 i2 = ODH.compose_ids i1 i2
let valid_length = AE.valid_length
let plain_t = AE.ae_plain
let length = AE.length

//let message_log_range (im:index_module) = AE.message_log_range im
//let message_log_inv (im:index_module) (pm:plain_module) (f:MM.map' (message_log_key im) (message_log_range im pm)) = AE.message_log_inv im pm f

let pkey = ODH.pkey
let skey = ODH.skey

let pkey_from_skey sk = ODH.get_pkey sk
let compatible_keys sk pk = ODH.compatible_keys sk pk


private noeq type aux_t' (im:index_module) (kim:key_index_module) (pm:plain_module) (rgn:log_region kim) =
  | AUX:
    am:AE.ae_module kim ->
    km:Key.key_module kim{km == AE.instantiate_km am} ->
    om:ODH.odh_module im kim km ->
    aux_t' im kim pm rgn

let aux_t im kim pm = aux_t' im kim pm

#set-options "--z3rlimit 600 --max_ifuel 1 --max_fuel 1"
val message_log_lemma: im:key_index_module -> rgn:log_region im -> Lemma
  (requires True)
  (ensures message_log im rgn === AE.message_log im rgn)
let message_log_lemma im rgn =
  assert(FStar.FunctionalExtensionality.feq (message_log_value im) (AE.message_log_value im));
  assert(FStar.FunctionalExtensionality.feq (message_log_range im) (AE.message_log_range im));
  let inv = message_log_inv im in
  let map_t =MM.map' (message_log_key im) (message_log_range im) in
  let inv_t = map_t -> Type0 in
  let ae_inv = AE.message_log_inv im in
  let ae_inv:map_t -> Type0 = ae_inv in
  assert(FStar.FunctionalExtensionality.feq
    #map_t #Type
    inv ae_inv);
  assert(message_log im rgn == AE.message_log im rgn);
  ()


#set-options "--z3rlimit 100 --max_ifuel 1 --max_fuel 0"
let get_message_log_region pkm = AE.get_message_log_region pkm.aux.am

val coerce: t1:Type -> t2:Type{t1 == t2} -> x:t1 -> t2
let coerce t1 t2 x = x

let get_message_logGT pkm =
  let (ae_log:AE.message_log pkm.kim (get_message_log_region pkm)) = AE.get_message_logGT #pkm.kim pkm.aux.am in
  let (ae_rgn:log_region pkm.kim) = AE.get_message_log_region pkm.aux.am in
  message_log_lemma pkm.kim ae_rgn;
  let log:message_log pkm.kim ae_rgn = coerce (AE.message_log pkm.kim ae_rgn) (message_log pkm.kim ae_rgn) ae_log in
  log

val create_aux: (im:index_module) -> (kim:key_index_module) -> (pm:plain_module{Plain.get_plain pm == plain_t /\ Plain.valid_length #pm == valid_length}) -> rgn:log_region kim -> St (aux_t im kim pm rgn)
let create_aux im kim pm rgn =
  assert(FStar.FunctionalExtensionality.feq (valid_length) (AE.valid_length));
  let am = AE.create kim pm rgn in
  let km = AE.instantiate_km am in
  let om = ODH.create im kim km rgn in
  AUX am km om

assume val lemma_compatible_length: n:nat -> Lemma
  (requires valid_length n)
  (ensures n / Spec.Salsa20.blocklen < pow2 32)

val enc (im:ODH.index_module): plain_t -> n:nonce -> pk:pkey -> sk:skey{ODH.compatible_keys sk pk} -> GTot cipher
let enc im p n pk sk = 
  lemma_compatible_length (length p);
  SPEC.secretbox_easy p (ODH.prf_odhGT sk pk) n

assume val dec: c:cipher -> n:nonce -> pk:pkey -> sk:skey -> Tot (option plain_t) 

let create rgn =
  let id_log_rgn : ID.id_log_region = new_region rgn in
//  let key_id_log_rgn : ID.id_log_region = new_region rgn in
  let im = ID.create id_log_rgn sub_id in
  let kim = ID.compose id_log_rgn im ODH.smaller in 
  let pm = Plain.create plain_t AE.valid_length AE.length in
    let kim: im:ID.index_module{ID.id im == i:(ODH.dh_share * ODH.dh_share){b2t (ODH.smaller (fst i) (snd i))}} = kim in
  let log_rgn : log_region kim = new_region rgn in
  assert(FStar.FunctionalExtensionality.feq (valid_length) (AE.valid_length));
  let aux = create_aux im kim pm log_rgn in
  PKAE im kim pm log_rgn (enc im) (dec) aux

type key (pkm:pkae_module) = AE.key pkm.kim

let zero_bytes = AE.create_zero_bytes

let pkey_to_subId #pkm pk = ODH.pk_get_share pk
let pkey_to_subId_inj #pkm pk = ODH.lemma_pk_get_share_inj pk

let nonce_is_fresh (pkm:pkae_module) (i:ID.id pkm.kim) (n:nonce) (h:mem) =
  AE.nonce_is_fresh pkm.aux.am i n h

let invariant pkm =
  Key.invariant pkm.kim pkm.aux.km

let gen pkm =
  ODH.keygen()

#set-options "--z3rlimit 600 --max_ifuel 1 --max_fuel 1"
let encrypt pkm #i n sk pk m =
  let k = ODH.prf_odh pkm.im pkm.kim pkm.aux.km pkm.aux.om sk pk in
  let c = AE.encrypt pkm.aux.am #i n k m in
  let h = get() in assert(Key.invariant pkm.kim pkm.aux.km h);
  ID.lemma_honest_or_dishonest pkm.kim i;
  let honest_i = ID.get_honest pkm.kim i in
  if not honest_i then ( 
    assert(ID.dishonest pkm.kim i);
    assert(Key.leak pkm.kim pkm.aux.km k = ODH.prf_odhGT sk pk );
    //assert(c = SPEC.secretbox_easy (Plain.repr #pkm.kim #pkm.pm #i m) (Key.get_rawGT pkm.kim pkm.aux.km k) n);
    //assert( eq2 #cipher c (pkm.enc (Plain.repr #pkm.kim #pkm.pm #i m) n pk sk));
    ()
  );
  let h = get() in
  assert(FStar.FunctionalExtensionality.feq (message_log_range pkm.kim) (AE.message_log_range pkm.kim));
  MM.contains_eq_compat (get_message_logGT pkm) (AE.get_message_logGT pkm.aux.am) (n,i) (c,m) h;
  MM.contains_stable (get_message_logGT pkm) (n,i) (c,m);
  MR.witness (get_message_logGT pkm) (MM.contains (get_message_logGT pkm) (n,i) (c,m));
  c

let decrypt pkm #i n sk pk c =
  let k = ODH.prf_odh pkm.im pkm.kim pkm.aux.km pkm.aux.om sk pk in
  let m = AE.decrypt pkm.aux.am #i n k c in
  m
