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
module SPEC = Spec.CryptoBox
module Plain = Box.Plain
module Key = Box.Key
module ID = Box.Index
module ODH = Box.ODH
module AE = Box.AE
module LE = FStar.Endianness

#set-options "--z3rlimit 600 --max_ifuel 1 --max_fuel 0"
let nonce = AE.nonce
let cipher = AE.cipher
let sub_id  = lbytes Curve.serialized_point_length
let key_id = (i:(lbytes Curve.serialized_point_length*lbytes Curve.serialized_point_length){b2t (ODH.smaller' Curve.serialized_point_length (fst i) (snd i))})
let plain = AE.ae_plain


let valid_plain_length = AE.valid_plain_length
let valid_cipher_length = AE.valid_cipher_length

let zero_nonce = Seq.create HSalsa.noncelen (UInt8.uint_to_t 0)
let hsalsa20_hash input = HSalsa.hsalsa20 input zero_nonce

let base_point:lbytes Curve.serialized_point_length = Curve.base_point

#set-options "--z3rlimit 600 --max_ifuel 1 --max_fuel 0"
private noeq type aux_t' (im:index_module) (kim:plain_index_module) (pm:Plain.plain_module) (rgn:log_region) =
  | AUX:
    am:AE.ae_module kim{extends (AE.get_message_log_region #kim am) rgn /\ AE.get_pm am == pm} ->
    om:ODH.odh_module{ODH.get_hash_length om = HSalsa.keylen
                      /\ ODH.get_dh_share_length om = Curve.serialized_point_length
                      /\ ODH.get_dh_exponent_length om = Curve.scalar_length
                      /\ ODH.dh_exponentiate om == Curve.scalarmult
                      /\ ODH.hash_fun om == hsalsa20_hash
                      /\ ODH.get_base_point om = base_point
                      /\ ODH.get_index_module om == im
                      /\ ODH.get_key_index_module om == kim
                      } ->
    km:Key.key_module kim{
                          km == ODH.get_key_module om kim
                          /\ km == AE.instantiate_km am
                          /\ Key.get_keylen kim km == ODH.get_hash_length om
                          /\ extends (Key.get_log_region kim km) rgn} ->
    aux_t' im kim pm rgn

let aux_t im kim pm rgn = aux_t' im kim pm rgn

let skey pkm = ODH.skey pkm.aux.om
let pkey pkm = ODH.pkey pkm.aux.om

let pkey_from_skey pkm sk = ODH.get_pkey pkm.aux.om sk
let compatible_keys pkm sk pk = ODH.compatible_keys pkm.aux.om sk pk

let enc pkm p n pk sk =
  SPEC.cryptobox p n (ODH.pk_get_share pkm.aux.om pk) (ODH.get_skeyGT pkm.aux.om sk)

let dec pkm c n pk sk =
  let p = SPEC.cryptobox_open c n (ODH.pk_get_share pkm.aux.om pk) (ODH.get_skeyGT pkm.aux.om sk) in
  match p with
  | Some p' ->
    let p'':plain = p' in
    Some p''
  | None -> None

#set-options "--z3rlimit 600 --max_ifuel 1 --max_fuel 1"
let compose_ids pkm i1 i2 = ODH.compose_ids pkm.aux.om i1 i2

let length pkm = AE.length


let key_index_module = plain_index_module
let plain_module = pm:Plain.plain_module{Plain.get_plain pm == plain /\ Plain.valid_length #pm == valid_plain_length}

#set-options "--z3rlimit 600 --max_ifuel 1 --max_fuel 1"
val message_log_lemma: im:key_index_module -> rgn:log_region{disjoint (ID.get_rgn im) rgn} -> Lemma
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
  let (ae_log:AE.message_log pkm.pim (get_message_log_region pkm)) = AE.get_message_logGT #pkm.pim pkm.aux.am in
  let (ae_rgn:log_region) = AE.get_message_log_region pkm.aux.am in
  message_log_lemma pkm.pim ae_rgn;
  let log:message_log pkm.pim ae_rgn = coerce (AE.message_log pkm.pim ae_rgn) (message_log pkm.pim ae_rgn) ae_log in
  log

#set-options "--z3rlimit 1000 --max_ifuel 2 --max_fuel 1"
val create_aux: (im:index_module) ->
                (kim:ID.index_module{ID.id kim == key_id /\ disjoint (ID.get_rgn im) (ID.get_rgn kim)}) ->
                (pm:Plain.plain_module{Plain.get_plain pm == AE.ae_plain /\ Plain.valid_length #pm == AE.valid_plain_length}) ->
                rgn:rid{disjoint rgn (ID.get_rgn kim)/\ disjoint rgn (ID.get_rgn im)} ->
                ST (aux_t im kim pm rgn)
                (requires (fun h0 -> True))
                (ensures (fun h0 aux h1 -> True))
let create_aux im kim pm rgn =
  let am = AE.create kim pm rgn in
  let km = AE.instantiate_km #kim am in
  let om = ODH.create HSalsa.keylen Curve.serialized_point_length Curve.scalar_length hsalsa20_hash Curve.scalarmult Curve.base_point im kim km rgn in
  AUX am om km

val lemma_type_equality: t1:Type0 -> t2:Type0 -> pred:(t2 -> t2 -> bool) -> Lemma
  (requires t1 == t2)
  (ensures (t1 == t2 ==> i:(t1*t1){pred (fst i) (snd i)} == i:(t2*t2){pred (fst i) (snd i)}))
let lemma_type_equality t1 t2 pred = ()

#set-options "--z3rlimit 100 --max_ifuel 1 --max_fuel 0"
let create rgn =
  let im_id_log_rgn = new_region rgn in
  let kim_id_log_rgn = new_region rgn in
  let im = ID.create im_id_log_rgn sub_id in
  let dh_share_length = Curve.serialized_point_length in
  lemma_type_equality (sub_id) (lbytes Curve.serialized_point_length) (ODH.smaller' dh_share_length);
  lemma_type_equality (sub_id) (ID.id im) (ODH.smaller' dh_share_length);
  let kim = ID.compose kim_id_log_rgn im (ODH.smaller' dh_share_length) in
  assert(sub_id == lbytes Curve.serialized_point_length);
  assert(key_id == i:(sub_id*sub_id){b2t (ODH.smaller' dh_share_length (fst i) (snd i))});
  assert(disjoint im_id_log_rgn kim_id_log_rgn);
  assert(ID.id kim == key_id);
  let pm = Plain.create plain AE.valid_plain_length AE.length in
  assert(FunctionalExtensionality.feq (Plain.valid_length #pm) valid_plain_length);
  let log_rgn = new_region rgn in
  let aux = create_aux im kim pm log_rgn in
  PKAE im kim pm log_rgn aux

let key (pkm:pkae_module) = AE.key pkm.pim

let zero_bytes = AE.create_zero_bytes

let pkey_to_subId #pkm pk = ODH.pk_get_share pkm.aux.om pk
let pkey_to_subId_inj #pkm pk = ODH.lemma_pk_get_share_inj pkm.aux.om pk

let nonce_is_fresh (pkm:pkae_module) (i:ID.id pkm.pim) (n:nonce) (h:mem) =
  AE.nonce_is_fresh pkm.aux.am i n h

let invariant pkm =
  Key.invariant pkm.pim pkm.aux.km

let gen pkm =
  ODH.keygen pkm.aux.om

#set-options "--z3rlimit 1000 --max_ifuel 0 --max_fuel 0"
let encrypt pkm n sk pk m =
  let i = compose_ids pkm (pkey_to_subId #pkm pk) (pkey_to_subId #pkm (pkey_from_skey pkm sk)) in
  let k = ODH.prf_odh pkm.aux.om sk pk in
  let c = AE.encrypt pkm.aux.am #i n k m in
  let h = get() in
  ID.lemma_honest_or_dishonest pkm.pim i;
  let honest_i = ID.get_honest pkm.pim i in
  assert(FStar.FunctionalExtensionality.feq (message_log_range pkm.pim) (AE.message_log_range pkm.pim));
  MM.contains_stable (get_message_logGT pkm) (n,i) (c,m);
  MR.witness (get_message_logGT pkm) (MM.contains (get_message_logGT pkm) (n,i) (c,m));
  c

let decrypt pkm n sk pk c =
  let i = compose_ids pkm (pkey_to_subId #pkm pk) (pkey_to_subId #pkm (pkey_from_skey pkm sk)) in
  let k = ODH.prf_odh pkm.aux.om sk pk in
  let m = AE.decrypt pkm.aux.am #i n k c in
  m

(* low-level wrapper *)

open FStar.Buffer
module U64 = FStar.UInt64
type u64   = FStar.UInt64.t

let uint8_p = buffer Hacl.UInt8.t

val encrypt_low:
  c:uint8_p ->
  m:uint8_p ->
  mlen:u64{let len = U64.v mlen in length c = len /\ len = length m}  ->
  n:uint8_p ->
  pk:uint8_p ->
  sk:uint8_p{disjoint sk pk} ->
  Stack u32
    (requires (fun h -> live h c /\ live h m /\ live h n /\ live h pk /\ live h sk))
    (ensures  (fun h0 z h1 -> modifies_1 c h0 h1 /\ live h1 c))
let encrypt_low c m mlen n pk sk =
  admit()
  // let mlen' = Int.Cast.uint64_to_uint32 mlen in
  // Math.Lemmas.modulo_lemma (U64.v mlen) (pow2 32);
  // crypto_box_detached (sub c 16ul mlen') (sub c 0ul 16ul) (sub m 0ul mlen') mlen n pk sk


val decrypt_low:
  m:uint8_p ->
  c:uint8_p ->
  mlen:u64  ->
  n:uint8_p ->
  pk:uint8_p->
  sk:uint8_p{disjoint sk pk} ->
  Stack u32
    (requires (fun h -> live h c /\ live h m /\ live h n /\ live h pk /\ live h sk))
    (ensures  (fun h0 z h1 -> modifies_1 m h0 h1 /\ live h1 m))
let decrypt_low m c mlen n pk sk =
  admit()
  // let mlen' = Int.Cast.uint64_to_uint32 mlen in
  // Math.Lemmas.modulo_lemma (U64.v mlen) (pow2 32);
  // let mac = sub c 0ul 16ul in
  // crypto_box_open_detached m (sub c 16ul (U32.(mlen' -^ 16ul))) mac (U64.(mlen -^ 16uL)) n pk sk
