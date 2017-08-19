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
open Box.Indexing
open Box.Plain

module MR = FStar.Monotonic.RRef
module MM = MonotoneMap
module HS = FStar.HyperStack
module HH = FStar.HyperHeap
module HSalsa = Spec.HSalsa20
module Curve = Spec.Curve25519
module Plain = Box.Plain
module Key = Box.Key
module ID = Box.Indexing

let dh_element_size = HSalsa.keylen // is equal to scalar lenght in Spec.Curve25519
let dh_exponent_size = 32 // Size of scalar in Curve25519. Replace with constant in spec?
type dh_share = Curve.serialized_point //
let dh_basepoint = [
    0x09uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
    0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
    0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
    0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
    ]

type dh_exponent = Curve.scalar // is equal to Curve.serialized_point
(**
Nonce to use with HSalsa.hsalsa20.
                  *)
private let zero_nonce = Seq.create HSalsa.noncelen (UInt8.uint_to_t 0)

val share_from_exponent: dh_exponent -> Tot dh_share
let share_from_exponent dh_exp = Curve.scalarmult dh_exp (createL dh_basepoint)

type index_module = im:ID.index_module{get_subId im == dh_share}

abstract noeq type odh_module (im:index_module) (km:key_module im) = // require subId type to be dh_share?
  | ODH:
    rgn:(r:HH.rid) ->
    odh_module im km

(**
  A DH public key containing its raw byte representation. All ids of DH keys have to be unfresh and registered (e.g. marked as either honest
    or dishonest).
    TODO: Does the public key have to be abstract?
*)
noeq abstract type pkey =
  | PKEY: pk_share:dh_share -> pkey

(**
  A DH secret key containing its raw byte representation. All ids of DH keys have to be unfresh and registered (e.g. marked as either honest
  or dishonest).
*)
noeq abstract type skey =
  | SKEY: sk_exp:dh_exponent -> pk:pkey{pk.pk_share = share_from_exponent sk_exp} -> skey

let compatible_keys sk pk =
  sk.pk.pk_share <> pk.pk_share

(**
  A helper function to obtain the raw bytes of a DH public key.
*)
val pk_get_share: pk:pkey -> Tot (dh_sh:dh_share{dh_sh = pk.pk_share})
let pk_get_share k = k.pk_share

(**
   A helper function to obtain the share that corresponds to a DH secret key.
*)
val sk_get_share: sk:skey -> Tot (dh_sh:dh_share{dh_sh = share_from_exponent sk.sk_exp})
let sk_get_share sk = sk.pk.pk_share

val get_skey: sk:skey -> GTot (raw:dh_exponent{raw=sk.sk_exp})
let get_skey sk =
  sk.sk_exp


#set-options "--z3rlimit 300 --max_ifuel 1 --max_fuel 0"
val leak_skey: im:index_module -> sk:skey{dishonest im (SUBID sk.pk.pk_share)} -> Tot (raw:dh_exponent{raw=sk.sk_exp})
let leak_skey im sk =
  sk.sk_exp

val get_skeyGT: sk:skey -> Tot (raw:dh_exponent{raw=sk.sk_exp})
let get_skeyGT sk =
  sk.sk_exp


val keygen: unit -> ST (dh_pair:(pkey * skey){fst dh_pair == (snd dh_pair).pk})
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
let keygen () =
  let dh_exponent = random_bytes (UInt32.uint_to_t 32) in
  let dh_pk = PKEY (share_from_exponent dh_exponent) in
  let dh_sk = SKEY dh_exponent dh_pk in
  dh_pk,dh_sk


val coerce_pkey: im:index_module -> dh_sh:dh_share{dishonest im (SUBID dh_sh)} -> Tot (pk:pkey{pk.pk_share=dh_sh})
let coerce_pkey im dh_sh =
  PKEY dh_sh

(**
   coerce_keypair allows the adversary to coerce a DH exponent into a DH private key. The corresponding DH public key
   is generated along with it. Both keys are considered dishonest and the id is considered unfresh after coercion.
*)
val coerce_keypair: im:index_module -> dh_exp:dh_exponent{dishonest im (SUBID (share_from_exponent dh_exp))} -> Tot (dh_pair:(k:pkey{k.pk_share = share_from_exponent dh_exp}) * (k:skey{k.sk_exp=dh_exp}))
let coerce_keypair im dh_ex =
  let dh_sh = share_from_exponent dh_ex in
  let pk = PKEY dh_sh in
  let sk = SKEY dh_ex pk in
  pk,sk


(**
  GTot specification of the prf_odh function for use in type refinements.
*)
val prf_odhGT: im:index_module -> skey -> pkey -> GTot aes_key
let prf_odhGT im sk pk =
  let i = compose_ids im pk.pk_share sk.pk.pk_share in
  let raw_k = Curve.scalarmult sk.sk_exp pk.pk_share in
  let k = HSalsa.hsalsa20 raw_k zero_nonce in
  k


#reset-options
#set-options "--z3rlimit 500 --max_ifuel 1 --max_fuel 0"
val prf_odh: im:index_module -> km:key_module im -> om:odh_module im km  -> sk:skey -> pk:pkey{sk.pk.pk_share <> pk.pk_share} -> ST (k:Key.get_keytype im km{Key.get_index im km k = (ID.compose_ids im pk.pk_share sk.pk.pk_share)} )
  (requires (fun h0 ->
    let i = ID.compose_ids im pk.pk_share sk.pk.pk_share in
    registered im (ID i)
    /\ km_invariant im km h0
  ))
  (ensures (fun h0 k h1 ->
    let i = ID.compose_ids im pk.pk_share sk.pk.pk_share in
    (honest im (ID i) ==> True)
    /\ (dishonest im (ID i) ==>
                        (Key.leak im km k = prf_odhGT im sk pk
                        /\ h0 == h1
                        ))
    /\ km_invariant im km h1
  ))
let prf_odh im km om sk pk =
  let i1 = pk.pk_share in
  let i2 = sk.pk.pk_share in
  let i = ID.compose_ids im i1 i2 in
  recall_log im;
  lemma_honest_or_dishonest im (ID i);
  let h = get_reg_honesty im (ID i) in
  match h with
  | HONEST ->
    let k = Key.gen im km i in
    k
  | DISHONEST ->
    let raw_k = Curve.scalarmult sk.sk_exp pk.pk_share in
    let hashed_raw_k = HSalsa.hsalsa20 raw_k zero_nonce in
    let k=Key.coerce im km i hashed_raw_k in
    k
