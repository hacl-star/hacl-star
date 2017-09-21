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

let nonce = AE.nonce
let cipher = AE.cipher
let sub_id = ODH.dh_share' Curve.serialized_point_length
let key_id = ODH.key_id' Curve.serialized_point_length
let plain = AE.ae_plain
let skey = ODH.skey
let pkey = ODH.pkey

let valid_plain_length = AE.valid_plain_length
let valid_cipher_length = AE.valid_cipher_length

#set-options "--z3rlimit 600 --max_ifuel 1 --max_fuel 0"
private noeq type aux_t' (skey:Type0) (pkey:Type0) (im:index_module) (kim:plain_index_module) (pm:Plain.plain_module) (rgn:log_region kim) =
  | AUX:
    am:AE.ae_module kim ->
    om:ODH.odh_module{ODH.get_hash_length om = HSalsa.keylen
                      /\ ODH.get_dh_share_length om = Curve.serialized_point_length
                      /\ ODH.get_dh_exponent_length om = Curve.scalar_length
                      /\ ODH.get_index_module om == im
                      /\ ODH.get_key_index_module om == kim
                      /\ ODH.skey == skey
                      /\ ODH.pkey == pkey
                      } ->
    km:Key.key_module kim{km == AE.instantiate_km am
                          /\ km == ODH.get_key_module om
                          /\ Key.get_keylen kim km == ODH.get_hash_length om} ->
    aux_t' skey pkey im kim pm rgn

let aux_t skey pkey im kim pm = aux_t' skey pkey im kim pm

#set-options "--z3rlimit 600 --max_ifuel 1 --max_fuel 1"
let compose_ids pkm i1 i2 = ODH.compose_ids pkm.aux.om i1 i2
let length pkm = AE.length

let pkey_from_skey sk = ODH.get_pkey sk
let compatible_keys sk pk = ODH.compatible_keys sk pk

let key_index_module = plain_index_module
let plain_module = pm:Plain.plain_module{Plain.get_plain pm == plain /\ Plain.valid_length #pm == valid_plain_length}

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
  let (ae_log:AE.message_log pkm.pim (get_message_log_region pkm)) = AE.get_message_logGT #pkm.pim pkm.aux.am in
  let (ae_rgn:log_region pkm.pim) = AE.get_message_log_region pkm.aux.am in
  message_log_lemma pkm.pim ae_rgn;
  let log:message_log pkm.pim ae_rgn = coerce (AE.message_log pkm.pim ae_rgn) (message_log pkm.pim ae_rgn) ae_log in
  log

val create_aux: (skey:Type0) ->
                (pkey:Type0) ->
                (im:index_module) ->
                (kim:key_index_module) ->
                (pm:plain_module) ->
                rgn:log_region kim ->
                St (aux_t skey pkey im kim pm rgn)
let create_aux skey pkey im kim pm rgn =
  assert(FStar.FunctionalExtensionality.feq (valid_plain_length) (AE.valid_plain_length));
  let am = AE.create kim pm rgn in
  let km = AE.instantiate_km am in
  let om = ODH.create HSalsa.keylen Curve.serialized_point_length Curve.scalar_length im kim km rgn in
  AUX am om km

val enc (im:index_module) (kim:key_index_module) (pm:plain_module) (rgn:log_region kim) (aux:aux_t ODH.skey ODH.pkey im kim pm rgn): plain -> n:nonce -> pk:ODH.pkey -> sk:ODH.skey{ODH.compatible_keys aux.om sk pk} -> GTot cipher
let enc im kim pm rgn aux p n pk sk =
  SPEC.cryptobox p n (ODH.pk_get_share aux.om pk) (ODH.get_skeyGT aux.om sk)

val dec (im:index_module) (kim:key_index_module) (pm:plain_module) (rgn:log_region kim) (aux:aux_t ODH.skey ODH.pkey im kim pm rgn): c:cipher -> n:nonce -> pk:ODH.pkey -> sk:ODH.skey{ODH.compatible_keys aux.om sk pk} -> GTot (option (b:plain))
let dec im kim pm rgn aux c n pk sk =
  SPEC.cryptobox_open c n (ODH.pk_get_share aux.om pk) (ODH.get_skeyGT aux.om sk)

//type plain_index_module = im:ID.index_module{ID.id im == key_id'}
//let key_id' = ODH.key_id' Curve.serialized_point_length
// ODH.key_id' sh = i:(dh_share' dh_share_length * dh_share' dh_share_length){b2t (smaller' dh_share_length (fst i) (snd i))}

//Subtyping check failed; expected type Box.PKAE.plain_index_module; got type (im':Box.Index.index_module{ Box.Index.id im' ==
//          (i:(Box.Index.id im * Box.Index.id im){ Prims.b2t (Box.ODH.smaller' Spec.Curve25519.serialized_point_length
//                           (FStar.Pervasives.Native.fst i)
//                           (FStar.Pervasives.Native.snd i)) }) })

#set-options "--z3rlimit 100 --max_ifuel 1 --max_fuel 0"
let create rgn =
  let id_log_rgn : ID.id_log_region = new_region rgn in
  let im = ID.create id_log_rgn sub_id in
  let kim = ID.compose id_log_rgn im (ODH.smaller' Curve.serialized_point_length) in
  //assert(FStar.FunctionalExtensionality.feq ())
  assert(ID.id kim == i:(ID.id im * ID.id im){b2t (ODH.smaller' Curve.serialized_point_length (fst i) (snd i))});
  assert(ID.id im == ODH.dh_share' Curve.serialized_point_length);
  assert(ID.id im * ID.id im == ODH.dh_share' Curve.serialized_point_length * ODH.dh_share' Curve.serialized_point_length);
  assert(key_id == i:(ODH.dh_share' Curve.serialized_point_length * ODH.dh_share' Curve.serialized_point_length){b2t (ODH.smaller' Curve.serialized_point_length (fst i) (snd i))});
  //assert(i:(ID.id im * ID.id im){b2t (ODH.smaller' Curve.serialized_point_length (fst i ) (snd i))} == i:(ODH.dh_share' Curve.serialized_point_length * ODH.dh_share' Curve.serialized_point_length){b2t (ODH.smaller' Curve.serialized_point_length (fst i) (snd i))});
  //assert(ID.id kim == i:(ODH.dh_share' Curve.serialized_point_length * ODH.dh_share' Curve.serialized_point_length){b2t (ODH.smaller' Curve.serialized_point_length (fst i) (snd i))});
  let kid = ODH.key_id' Curve.serialized_point_length in
  let kid' = kid in
  //assert(key_id' == i:(ID.id im * ID.id im){b2t (ODH.smaller' Curve.serialized_point_length (fst i) (snd i))});
  admit();
  let pm = Plain.create plain AE.valid_plain_length AE.length in
  //admit();
  //let kim: im:ID.index_module{ID.id im == i:(ODH.dh_share * ODH.dh_share){b2t (ODH.smaller (fst i) (snd i))}} = kim in
  let log_rgn : log_region kim = new_region rgn in
  assert(FStar.FunctionalExtensionality.feq (valid_plain_length) (AE.valid_plain_length));
  let aux = create_aux ODH.skey ODH.pkey im kim pm log_rgn in
  PKAE (ODH.get_pkey aux.om) (ODH.compatible_keys aux.om) im kim pm log_rgn (enc im kim pm rgn aux) (dec im kim pm rgn aux) aux

let key (pkm:pkae_module) = AE.key pkm.pim

let zero_bytes = AE.create_zero_bytes

let pkey_to_subId #pkm pk = ODH.pk_get_share pkm.aux.om pk
let pkey_to_subId_inj #pkm pk = ODH.lemma_pk_get_share_inj pkm.aux.om pk

let nonce_is_fresh (pkm:pkae_module) (i:ID.id pkm.pim) (n:nonce) (h:mem) =
  AE.nonce_is_fresh pkm.aux.am i n h


let invariant pkm =
  Key.invariant pkm.pim pkm.aux.km

//  Subtyping check failed; expected type (keypair:(PKAE?.pkey pkm * PKAE?.skey pkm){ FStar.Pervasives.Native.fst keypair ==
//            PKAE?.pkey_from_skey pkm (FStar.Pervasives.Native.snd keypair) }); got type (dh_pair:(Box.ODH.pkey * Box.ODH.skey){ FStar.Pervasives.Native.fst dh_pair ==
//            Box.ODH.get_pkey (AUX?.om (PKAE?.aux pkm)) (FStar.Pervasives.Native.snd dh_pair) })
let gen pkm =
  assert(FStar.FunctionalExtensionality.feq (ODH.get_pkey) (pkey_from_skey));
  ODH.keygen pkm.aux.om

val encrypt: pkm:pkae_module ->
             n:nonce ->
             sk:skey ->
             pk:pkey -> //{pkm.compatible_keys sk pk} ->
             m:(Plain.protected_plain_t pkm.pim (Plain.get_plain pkm.pm) (compose_ids pkm (pkey_to_subId #pkm pk) (pkey_to_subId #pkm (pkm.pkey_from_skey sk)))) ->
             ST cipher
  (requires (fun h0 -> True
    //let i = compose_ids pkm (pkey_to_subId #pkm pk) (pkey_to_subId #pkm (pkm.pkey_from_skey sk)) in
    //registered pkm i
    ///\ nonce_is_fresh pkm i n h0
    ///\ invariant pkm h0
  ))
  (ensures  (fun h0 c h1 ->
    let i = compose_ids pkm (pkey_to_subId #pkm pk) (pkey_to_subId #pkm (pkm.pkey_from_skey sk)) in
    modifies (Set.singleton pkm.rgn) h0 h1 // stateful changes even if the id is dishonest.
    /\ ((honest pkm i /\ b2t pkae) // Ideal behaviour if the id is honest and the assumption holds
               ==> eq2 #cipher c (pkm.enc (zero_bytes (Plain.length #pkm.pim #pkm.pm #i m)) n pk sk))
    /\ ((dishonest pkm i \/ ~(b2t pkae)) // Concrete behaviour otherwise.
                  ==> eq2 #cipher c (pkm.enc (Plain.repr #pkm.pim #pkm.pm #i m) n pk sk))
    // The message is added to the log. This also guarantees nonce-uniqueness.
    /\ MR.m_contains #(get_message_log_region pkm)(get_message_logGT pkm) h1
    /\ MR.witnessed (MM.contains #(get_message_log_region pkm) (get_message_logGT pkm) (n,i) (c,m))
    /\ MR.m_sel #(get_message_log_region pkm) h1 (get_message_logGT pkm)== MM.upd (MR.m_sel #(get_message_log_region pkm) h0 (get_message_logGT pkm)) (n,i) (c,m)
    /\ invariant pkm h1
  ))

#set-options "--z3rlimit 10000 --max_ifuel 0 --max_fuel 0"
let encrypt pkm n sk pk m =
  assert(False);
  admit();
  let i = compose_ids (pkey_to_subId #pkm pk) (pkey_to_subId #pkm (pkm.pkey_from_skey sk)) in
  let k = ODH.prf_odh pkm.aux.om sk pk in
  let c = AE.encrypt pkm.aux.am #i n k m in
  assert(Game3? current_game <==> (b2t pkae /\ ~prf_odh));
  //assert((honest pkm i /\ b2t pkae) // Ideal behaviour if the id is honest and the assumption holds
  //  ==> c == pkm.enc (zero_bytes (Plain.length #pkm.pim #pkm.pm #i m)) n pk sk);
  let h = get() in
  assert(Key.invariant pkm.pim pkm.aux.km h);
  ID.lemma_honest_or_dishonest pkm.pim i;
  let honest_i = ID.get_honest pkm.pim i in
  if not honest_i then (
    assert(ID.dishonest pkm.pim i);
    //assert(Key.leak pkm.pim pkm.aux.km k = ODH.prf_odhGT sk pk );
    //assert(c = SPEC.secretbox_easy (Plain.repr #pkm.kim #pkm.pm #i m) (Key.get_rawGT pkm.kim pkm.aux.km k) n);
    //assert( eq2 #cipher c (pkm.enc (Plain.repr #pkm.kim #pkm.pm #i m) n pk sk));
    ()
  );
  let h = get() in
  assert(FStar.FunctionalExtensionality.feq (message_log_range pkm.pim) (AE.message_log_range pkm.pim));
  MM.contains_eq_compat (get_message_logGT pkm) (AE.get_message_logGT pkm.aux.am) (n,i) (c,m) h;
  MM.contains_stable (get_message_logGT pkm) (n,i) (c,m);
  MR.witness (get_message_logGT pkm) (MM.contains (get_message_logGT pkm) (n,i) (c,m));
  c

let decrypt pkm n sk pk c =
  assert(False);
  let i = compose_ids (pkey_to_subId #pkm pk) (pkey_to_subId #pkm (pkm.pkey_from_skey sk)) in
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
