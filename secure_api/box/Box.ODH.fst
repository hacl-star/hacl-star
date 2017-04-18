(**
   TODO: - Documentation, some cleanup.
*)
module Box.ODH

open FStar.Set
open FStar.HyperHeap
open FStar.HyperStack
open FStar.Monotonic.RRef
open FStar.Seq
open FStar.Monotonic.Seq
open FStar.List.Tot

open Crypto.Symmetric.Bytes

open Box.Indexing
open Box.Flags

module MR = FStar.Monotonic.RRef
module MM = MonotoneMap
module HS = FStar.HyperStack
module HH = FStar.HyperHeap
module HSalsa = Spec.HSalsa20
module Curve = Spec.Curve25519
module Key = Box.AE.Key

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

val share_from_exponent: dh_exponent -> Tot dh_share
let share_from_exponent dh_exp = Curve.scalarmult dh_exp (createL dh_basepoint)

(**
   Nonce to use with HSalsa.hsalsa20.
*)
private let zero_nonce = Seq.create HSalsa.noncelen (UInt8.uint_to_t 0)

type aes_key = Key.aes_key

assume val dh_key_log_region: (r:HH.rid{ extends r root
           /\ is_eternal_region r
           /\ is_below r root
           /\ disjoint r Key.ae_log_region
           /\ disjoint r id_log_region
           /\ disjoint r id_honesty_log_region
           })

type dh_key_log_key = i:id{AE_id? i /\ honest i}
type dh_key_log_value = (AE.key)
type dh_key_log_range = fun (i:dh_key_log_key) -> (k:dh_key_log_value{AE.get_index k = i})
type dh_key_log_inv (f:MM.map' dh_key_log_key dh_key_log_range) = True

(**
   The dh_key_log is a monotone map that maps ids to AE keys. Keys that are generated/computed by prf_odh are random if both DH keys
   that serve as its input are honest. Such honest keys are stored in the dh_key_log to ensure that only one AE key is generated for each
   pair of DH keys. This is ensured by the monotone nature of the log and the composition of AE ids through DH ids.
*)
assume val dh_key_log: MM.t dh_key_log_region dh_key_log_key dh_key_log_range dh_key_log_inv
//assume val dh_key_log: MM.t dh_key_log_region (i:id{AE_id? i /\ honest i}) dh_key_log_range dh_key_log_inv


(**
   A DH public key containing its raw byte representation. All ids of DH keys have to be unfresh and registered (e.g. marked as either honest
   or dishonest).
   TODO: Does the public key have to be abstract?
*)
noeq abstract type dh_pkey =
  | DH_pkey: pk_share:dh_share -> dh_pkey

(**
   A DH secret key containing its raw byte representation. All ids of DH keys have to be unfresh and registered (e.g. marked as either honest
   or dishonest).
*)
noeq abstract type dh_skey =
  | DH_skey: sk_exp:dh_exponent -> pk:dh_pkey{pk.pk_share = share_from_exponent sk_exp} -> dh_skey

(**
   A helper function to obtain the raw bytes of a DH public key.
*)
val pk_get_share: pk:dh_pkey -> Tot (dh_sh:dh_share{dh_sh = pk.pk_share})
let pk_get_share k = k.pk_share

(**
   A helper function to obtain the share that corresponds to a DH secret key.
*)
val sk_get_share: sk:dh_skey -> Tot (dh_sh:dh_share{dh_sh = share_from_exponent sk.sk_exp})
let sk_get_share sk = sk.pk.pk_share

val get_skey: sk:dh_skey -> GTot (raw:dh_exponent{raw=sk.sk_exp})
let get_skey sk =
  sk.sk_exp


val leak_skey: sk:dh_skey{dishonest (DH_id sk.pk.pk_share)} -> Tot (raw:dh_exponent{raw=sk.sk_exp})
let leak_skey sk =
  sk.sk_exp


val keygen: unit -> ST (dh_pair:(dh_pkey * dh_skey){fst dh_pair == (snd dh_pair).pk})
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> modifies Set.empty h0 h1))
let keygen () =
  let h0 = ST.get() in
  let dh_exponent = random_bytes (UInt32.uint_to_t 32) in
  let h1 = ST.get() in
  let dh_pk = DH_pkey (share_from_exponent dh_exponent) in
  let dh_sk = DH_skey dh_exponent dh_pk in
  dh_pk,dh_sk


val coerce_pkey: dh_sh:dh_share{dishonest (DH_id dh_sh)} -> Tot (pk:dh_pkey{pk.pk_share=dh_sh})
let coerce_pkey dh_sh =
  DH_pkey dh_sh

(**
   coerce_keypair allows the adversary to coerce a DH exponent into a DH private key. The corresponding DH public key
   is generated along with it. Both keys are considered dishonest and the id is considered unfresh after coercion.
*)
val coerce_keypair: dh_exp:dh_exponent{dishonest (DH_id (share_from_exponent dh_exp))} -> Tot (dh_pair:(k:dh_pkey{k.pk_share = share_from_exponent dh_exp}) * (k:dh_skey{k.sk_exp=dh_exp}))
let coerce_keypair dh_ex =
  let dh_sh = share_from_exponent dh_ex in
  let pk = DH_pkey dh_sh in
  let sk = DH_skey dh_ex pk in
  pk,sk

(**
   GTot specification of the prf_odh function for use in type refinements.
*)
val prf_odhGT: dh_skey -> dh_pkey -> GTot aes_key
let prf_odhGT dh_sk dh_pk =
  let i = generate_ae_id (DH_id dh_pk.pk_share) (DH_id dh_sk.pk.pk_share) in
  let raw_k = Curve.scalarmult dh_sk.sk_exp dh_pk.pk_share in
  let k = HSalsa.hsalsa20 raw_k zero_nonce in
  k


#reset-options
#set-options "--z3rlimit 300 --max_ifuel 1 --max_fuel 0"
val prf_odh: sk:dh_skey -> pk:dh_pkey -> ST (Key.key)
  ( requires (fun h0 ->
    let i = generate_ae_id (DH_id pk.pk_share) (DH_id sk.pk.pk_share) in
    ((AE_id? i /\ honest i /\ MM.fresh dh_key_log i h0) ==>  fresh i h0)
    /\ MR.m_contains id_log h0
    /\ MR.m_contains dh_key_log h0
    /\ registered i
  ))
  ( ensures (fun h0 k h1 ->
    let i = generate_ae_id (DH_id pk.pk_share) (DH_id sk.pk.pk_share) in
    let regions_modified_dishonest:Set.set (r:HH.rid) = (Set.singleton id_log_region) in
    let regions_modified_honest = Set.union regions_modified_dishonest (Set.singleton dh_key_log_region) in
    (i = Key.ae_key_get_index k)
    /\ (honest i \/ dishonest i)
    /\ (honest i ==> (let current_log = MR.m_sel h0 dh_key_log in
           MR.witnessed (MM.contains dh_key_log i k)
           /\ MM.contains dh_key_log i k h1
           /\ MM.defined dh_key_log i h1
           /\ (MM.fresh dh_key_log i h0 ==> (MR.m_sel h1 dh_key_log == MM.upd current_log i k // if the key is not yet in the dh_key_log, it will be afterwards
                  /\ makes_unfresh_just i h0 h1
                  /\ modifies regions_modified_honest h0 h1))
           /\ (MM.defined dh_key_log i h0 ==> (MR.m_sel h0 dh_key_log == MR.m_sel h1 dh_key_log // if the key is in the dh_key_log, the dh_key_log will not be modified
                    /\ h0==h1))       // and the log of the key will be the same as before.
      ))
    /\ (dishonest i
      ==> (modifies regions_modified_dishonest h0 h1
         /\ Key.leak_key k = prf_odhGT sk pk
         /\ makes_unfresh_just i h0 h1
         /\ MR.m_sel h0 dh_key_log == MR.m_sel h1 dh_key_log))
    /\ (modifies regions_modified_honest h0 h1
      \/ h0 == h1
      \/ modifies regions_modified_dishonest h0 h1)
    /\ ~(fresh i h1)
    /\ MR.m_contains dh_key_log h1
  ))
let prf_odh dh_sk dh_pk =
  let h0 = ST.get() in
  let i = generate_ae_id (DH_id dh_pk.pk_share) (DH_id dh_sk.pk.pk_share) in
  let honest_i = is_honest i in
  MR.m_recall dh_key_log;
  MR.m_recall id_log;
  MR.m_recall id_honesty_log;
  if honest_i then (
    lemma_honest_not_dishonest i;
    match MM.lookup dh_key_log i with
    | Some  k ->
      MR.m_recall id_log;
      fresh_unfresh_contradiction i;
      k
    | None ->
      let h0 = ST.get() in
      let k = Key.keygen i in
      MR.m_recall dh_key_log;
      MR.m_recall id_log;
      MM.extend dh_key_log i k;
      fresh_unfresh_contradiction i;
      k
  ) else (
    lemma_dishonest_not_honest i;
    MR.m_recall id_log;
    MR.m_recall id_honesty_log;
    MR.m_recall dh_key_log;
    let raw_k = Curve.scalarmult dh_sk.sk_exp dh_pk.pk_share in
    let hashed_raw_k = HSalsa.hsalsa20 raw_k zero_nonce in
    let k=Key.coerce_key i hashed_raw_k in
    fresh_unfresh_contradiction i;
    k
  )
