(**
   TODO: - Documentation, some cleanup.
*)
module Box.ODH
open FStar.Set
open FStar.HyperHeap
open FStar.HyperHeap.ST
open FStar.HyperStack
open FStar.Monotonic.RRef
open FStar.Seq
open FStar.Monotonic.Seq
open FStar.List.Tot

open Crypto.Symmetric.Bytes

open Box.Flags
open Box.Key

module MR = FStar.Monotonic.RRef
module MM = MonotoneMap
module HS = FStar.HyperStack
module HH = FStar.HyperHeap
module HSalsa = Spec.HSalsa20
module Curve = Spec.Curve25519


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

// ToDo: Implement these properly
val honest: sh:dh_share -> Type0
let honest sh =
  True

val dishonest: sh:dh_share -> Type0
let dishonest sh =
  True

val honestST: sh:dh_share -> ST bool
  (requires (fun h0 -> True))
  (ensures (fun h0 b h1 -> True))  // b <==> honest pk /\ b <==> ~(dishonest pk)
let honestST sh =
  true


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


val leak_skey: sk:skey{dishonest sk.pk.pk_share} -> Tot (raw:dh_exponent{raw=sk.sk_exp})
let leak_skey sk =
  sk.sk_exp

val get_skeyGT: sk:skey -> Tot (raw:dh_exponent{raw=sk.sk_exp})
let get_skeyGT sk =
  sk.sk_exp


val keygen: unit -> HyperStack.ST.ST (dh_pair:(pkey * skey){fst dh_pair == (snd dh_pair).pk})
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> HS.modifies Set.empty h0 h1))
let keygen () =
  let dh_exponent = random_bytes (UInt32.uint_to_t 32) in
  let dh_pk = PKEY (share_from_exponent dh_exponent) in
  let dh_sk = SKEY dh_exponent dh_pk in
  dh_pk,dh_sk


val coerce_pkey: dh_sh:dh_share{dishonest dh_sh} -> Tot (pk:pkey{pk.pk_share=dh_sh})
let coerce_pkey dh_sh =
  PKEY dh_sh

(**
   coerce_keypair allows the adversary to coerce a DH exponent into a DH private key. The corresponding DH public key
   is generated along with it. Both keys are considered dishonest and the id is considered unfresh after coercion.
*)
val coerce_keypair: dh_exp:dh_exponent{dishonest (share_from_exponent dh_exp)} -> Tot (dh_pair:(k:pkey{k.pk_share = share_from_exponent dh_exp}) * (k:skey{k.sk_exp=dh_exp}))
let coerce_keypair dh_ex =
  let dh_sh = share_from_exponent dh_ex in
  let pk = PKEY dh_sh in
  let sk = SKEY dh_ex pk in
  pk,sk


type dh_key_log_key (km:key_module) = i:getIt km
type dh_key_log_value (km:key_module) (i:getIt km) = (Key.key #(Key.getIt km) i)
let dh_key_log_range (km:key_module)= fun (k:dh_key_log_key km) -> dh_key_log_value km k
type dh_key_log_inv (km:key_module) (f:MM.map' (dh_key_log_key km) (dh_key_log_range km)) = True

type dh_key_log_region= (r:HH.rid{ extends r root
                       /\ is_eternal_region r
                       /\ is_below r root
                       })

abstract noeq type odh_module (km:key_module) =
  | ODH:
    rgn:(r:dh_key_log_region{disjoint r (Key.get_region km)}) ->
    composeKMId: (dh_share -> dh_share -> (getIt km)) -> // Ids should be independent of the order of pk1 pk2
    dh_key_log: (MM.t rgn (dh_key_log_key km) (dh_key_log_range km) (dh_key_log_inv km)) ->
    odh: (sk:skey -> pk:pkey -> ST (Key.key (composeKMId pk.pk_share sk.pk.pk_share))
      (requires (fun h0 -> True))
      (ensures (fun h0 k h1 -> True))) ->
    odh_module km

val compose_id: km:key_module -> odh_module km -> dh_share -> dh_share -> getIt km
let compose_id km om sh1 sh2 =
  om.composeKMId sh1 sh2


//val honesty_invariant: (km:key_module) -> (om:odh_module km) -> (h:mem) -> Type0
let honesty_invariant km om =
  forall i1 i2 . ((honest i1 /\ honest i2) ==> Key.honest km (compose_id km om i1 i2))
            /\ (dishonest i1 /\ honest i2 ==> Key.dishonest km (compose_id km om i1 i2))


#reset-options
#set-options "--z3rlimit 300 --max_ifuel 1 --max_fuel 0"
val prf_odh: km:key_module -> om:odh_module km -> sk:skey -> pk:pkey -> ST (Key.key #(getIt km) (compose_id km om pk.pk_share sk.pk.pk_share) )
  (requires (fun h0 -> honesty_invariant km om))
  (ensures (fun h0 k h1 -> honesty_invariant km om))
let prf_odh km om sk pk =
  let id = compose_id km om pk.pk_share sk.pk.pk_share in
  let is_honestST = Key.honestST km id in
  let is_dishonestST = Key.dishonestST km id in
  if is_dishonestST then (
    let raw_k = Curve.scalarmult sk.sk_exp pk.pk_share in
    let hashed_raw_k = HSalsa.hsalsa20 raw_k zero_nonce in
    let k=Key.coerce km id hashed_raw_k in
    k
  ) else (
    Key.make_honest km id;
    Key.gen km id
  )
