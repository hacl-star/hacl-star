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

open CoreCrypto

open Box.Indexing
open Box.Flags

module MR = FStar.Monotonic.RRef
module MM = MonotoneMap
module HS = FStar.HyperStack
module HH = FStar.HyperHeap
module HSalsa = Spec.HSalsa20
module Curve = Spec.Curve25519
module Key = Box.AE.Key

#set-options "--z3rlimit 100 --lax"
let dh_element_size = HSalsa.keylen // is equal to scalar lenght in Spec.Curve25519
let dh_exponent_size = 32 //TODO: replace with constant from Spec.Curve25519
type dh_element = HSalsa.key
type dh_share = Curve.serialized_point //
assume val dh_base : dh_element
type dh_exponent = Curve.scalar // is equal to Curve.serialized_point

(**
   Nonce to use with HSalsa.hsalsa20.
*)
private let zero_nonce = Seq.create HSalsa.noncelen (UInt8.uint_to_t 0)

assume val dh_gen_key: unit -> ST (dh_share*dh_exponent)
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 ->
    h0==h1
  ))

type aes_key = Key.aes_key 


assume val dh_key_log_region: (r:HH.rid{ extends r root 
					 /\ is_eternal_region r 
					 /\ is_below r root 
					 /\ disjoint r Key.ae_key_region
					 /\ disjoint r id_log_region
					 /\ disjoint r id_honesty_log_region
					 })
type dh_key_log_key = i:id{AE_id? i /\ honest i}
type dh_key_log_value = (AE.key)
type dh_key_log_range = fun (i:dh_key_log_key) -> (k:dh_key_log_value{AE.get_index k = i})
type dh_key_log_inv (f:MM.map' dh_key_log_key dh_key_log_range) = True

//private type dh_key_log_key = k_id:id{AE_id? k_id}
//private type dh_key_log_value = 

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
noeq type dh_pkey = 
  | DH_pkey: #pk_id:id{DH_id? pk_id /\ unfresh pk_id /\ registered pk_id} -> rawpk:dh_share -> dh_pkey

(**
   A DH secret key containing its raw byte representation. All ids of DH keys have to be unfresh and registered (e.g. marked as either honest
   or dishonest).
*)
noeq abstract type dh_skey =
  | DH_skey: #sk_id:id{DH_id? sk_id /\ unfresh sk_id /\ registered sk_id} -> rawsk:dh_exponent -> pk:dh_pkey{pk.pk_id=sk_id} -> dh_skey 

(**
   A helper function to obtain the index of a DH secret key.
*)
val sk_get_index: sk:dh_skey -> Tot (i:id{i = sk.sk_id})
let sk_get_index k = k.sk_id

(**
   A helper function to obtain the index of a DH public key.
*)
val pk_get_index: pk:dh_pkey -> Tot (i:id{i = pk.pk_id})
let pk_get_index k = k.pk_id


val get_skey: sk:dh_skey -> GTot (raw:dh_exponent{raw=sk.rawsk})
let get_skey sk = 
  sk.rawsk

(**
   This function provides access to the raw byte representation of a DH public key.
   TODO: If the key is not abstract, we do not need this any longer.
*)
val pk_get_rawpk: pk:dh_pkey -> Tot (raw:dh_share{raw=pk.rawpk})
let pk_get_rawpk pk =
  pk.rawpk

val leak_skey: sk:dh_skey{dishonest sk.sk_id} -> Tot (raw:dh_exponent{raw=sk.rawsk})
let leak_skey sk = 
  sk.rawsk

// TODO: Replace this with curve25519 scalar multiplication.
assume val dh_exponentiate: dh_element -> dh_exponent -> Tot dh_element

(**
   keygen generates a pair of DH keys with the same id. It requires that the id associated with the keys
   is registered. The id is considered unfresh after key generation.
*)
val keygen: #i:id{DH_id? i} -> ST (dh_pair:(k:dh_pkey{k.pk_id=i}) * (k:dh_skey{k.sk_id=i}))
  (requires (fun h -> 
    fresh i h
    /\ registered i
  ))
  (ensures (fun h0 k h1 -> 
    unfresh i
    /\ modifies (Set.singleton id_log_region) h0 h1
  ))
let keygen #i =
  make_unfresh i;
  let dh_share,dh_exponent = dh_gen_key() in
  let dh_pk = DH_pkey #i dh_share in
  let dh_sk = DH_skey #i dh_exponent dh_pk in
  dh_pk,dh_sk

(**
   coerce_pkey allows the adversary to coerce any DH share into a DH public key. Such a coerced key has
   to be dishonest. Also, the id is considered unfresh after coercion.
*)
val coerce_pkey: #i:id{DH_id? i /\ dishonest i} -> dh_share -> ST (pk:dh_pkey{pk.pk_id=i})
  (requires (fun h0 -> 
    fresh i h0
    /\ registered i
  ))
  (ensures (fun h0 pk h1 -> 
    unfresh i
  ))
let coerce_pkey #i dh_sh =
  make_unfresh i;
  DH_pkey #i dh_sh
(**
   coerce_keypair allows the adversary to coerce a DH exponent into a DH private key. The corresponding DH public key
   is generated along with it. Both keys are considered dishonest and the id is considered unfresh after coercion.
*)
val coerce_keypair: #i:id{DH_id? i /\ dishonest i} -> dh_exponent -> ST (dh_pair:(k:dh_pkey{k.pk_id=i}) * (k:dh_skey{k.sk_id=i}))
  (requires (fun h0 -> 
    fresh i h0
    /\ registered i
  ))
  (ensures (fun h0 pk h1 -> 
    unfresh i
  ))
let coerce_keypair #i dh_ex =
  make_unfresh i;
  let dh_sh = dh_exponentiate dh_base dh_ex in
  let pk = DH_pkey #i dh_sh in
  let sk = DH_skey #i dh_ex pk in
  pk,sk

(**
   GTot specification of the prf_odh function for use in type refinements.
*)
val prf_odhGT: dh_skey -> dh_pkey -> GTot aes_key
let prf_odhGT dh_sk dh_pk =
  let pk_id = dh_pk.pk_id in
  let sk_id = dh_sk.sk_id in
  let i = generate_ae_id pk_id sk_id in
  let raw_k = Curve.scalarmult dh_sk.rawsk dh_pk.rawpk in
  let k = HSalsa.hsalsa20 raw_k zero_nonce in
  k


#reset-options
#set-options "--z3rlimit 100"
val handle_honest_i: i:id{AE_id? i /\ honest i} -> ST (k:Key.key)
  (requires (fun h0 -> 
    ((AE_id? i /\ honest i) ==> (MM.defined dh_key_log i h0 \/ fresh i h0))
  ))
  (ensures (fun h0 k h1 ->
    let regions_modified_honest = Set.union (Set.singleton id_log_region) (Set.singleton dh_key_log_region) in
    let k_log = Key.get_logGT k in
    let current_log = MR.m_sel h0 dh_key_log in
    i = Key.ae_key_get_index k
    /\ MR.m_contains k_log h1
    /\ (fresh i h0 ==> (MR.m_sel h1 (Key.get_logGT k) == Key.empty_log i))
    /\ MR.witnessed (MM.contains dh_key_log i k)
    /\ (MM.fresh dh_key_log i h0 ==> (MR.m_sel h1 dh_key_log == MM.upd current_log i k // if the key is not yet in the dh_key_log, it will be afterwards
    			          /\ MR.m_sel h1 k_log == Key.empty_log i     // and the log of the key will be empty.
    				  /\ makes_unfresh_just i h0 h1
				  /\ HS.modifies regions_modified_honest h0 h1))
    /\ (MM.defined dh_key_log i h0 ==> (MR.m_sel h0 dh_key_log == MR.m_sel h1 dh_key_log // if the key is in the dh_key_log, the dh_key_log will not be modified
    			            /\ MR.m_sel h0 k_log == MR.m_sel h1 k_log
				    /\ h0 == h1))       // and the log of the key will be the same as before.
    /\ MM.contains dh_key_log i k h1
  ))
let handle_honest_i i = 
  //lemma_honest_not_dishonest i;
  MR.m_recall dh_key_log;
  match MM.lookup dh_key_log i with
  | Some  k' ->
    Key.recall_log k'; 
    MR.m_recall id_log;
    fresh_unfresh_contradiction i;
    k'
  | None ->
    let h0 = ST.get() in
    let k' = Key.keygen i in
    MR.m_recall dh_key_log;
    MR.m_recall id_log;
    MM.extend dh_key_log i k';
    Key.recall_log k';
    fresh_unfresh_contradiction i;
    k'

#reset-options
#set-options "--z3rlimit 100"
val handle_dishonest_i:  dh_sk:dh_skey 
		       -> dh_pk:dh_pkey 
		       -> i:id{dishonest i /\ AE_id? i /\ i = generate_ae_id dh_pk.pk_id dh_sk.sk_id} 
		       -> ST (k:Key.key{Key.ae_key_get_index k = i})
  (requires (fun h0 -> registered i))
  (ensures (fun h0 k h1 -> 
    let regions_modified_dishonest:Set.set (r:HH.rid) = (Set.singleton id_log_region) in
    let k_log = Key.get_logGT k in
    HS.modifies regions_modified_dishonest h0 h1
    /\ Key.leak_key k = prf_odhGT dh_sk dh_pk
    /\ MR.m_contains k_log h1
    /\ makes_unfresh_just i h0 h1
    /\ i = Key.ae_key_get_index k 
    /\ MR.m_sel h1 (Key.get_logGT k) == Key.empty_log i
  ))
let handle_dishonest_i dh_sk dh_pk i =
    lemma_dishonest_not_honest i;
    let raw_k = Curve.scalarmult dh_sk.rawsk dh_pk.rawpk in
    let hashed_raw_k = HSalsa.hsalsa20 raw_k zero_nonce in
    let k=Key.coerce_key i hashed_raw_k in
    fresh_unfresh_contradiction i;
    k


// This everifies now. Inlining handler functions for honest and dishonest case breaks things...
val prf_odh: sk:dh_skey -> pk:dh_pkey -> ST (Key.key)
  ( requires (fun h0 -> 
    let i = generate_ae_id pk.pk_id sk.sk_id in
    ((AE_id? i /\ honest i /\ MM.fresh dh_key_log i h0) ==>  fresh i h0)
    /\ m_contains id_log h0
    /\ registered i
  ))
  ( ensures (fun h0 k h1 ->
    let i = generate_ae_id pk.pk_id sk.sk_id in
    let regions_modified_dishonest:Set.set (r:HH.rid) = (Set.singleton id_log_region) in
    let regions_modified_honest = Set.union regions_modified_dishonest (Set.singleton dh_key_log_region) in
    let k_log = Key.get_logGT k in
    (i = Key.ae_key_get_index k)
    /\ MR.m_contains k_log h1
    /\ (fresh i h0 ==> (MR.m_sel h1 (Key.get_logGT k) == Key.empty_log i))
    /\ (honest i ==> (let current_log = MR.m_sel h0 dh_key_log in
    		   MR.witnessed (MM.contains dh_key_log i k)
		   /\ MM.contains dh_key_log i k h1
    		   /\ (MM.fresh dh_key_log i h0 ==> (MR.m_sel h1 dh_key_log == MM.upd current_log i k // if the key is not yet in the dh_key_log, it will be afterwards
    						  /\ MR.m_sel h1 k_log == Key.empty_log i // and the log of the key will be empty.
						  /\ makes_unfresh_just i h0 h1
    						  /\ modifies regions_modified_honest h0 h1))
    		   /\ (MM.defined dh_key_log i h0 ==> (MR.m_sel h0 dh_key_log == MR.m_sel h1 dh_key_log // if the key is in the dh_key_log, the dh_key_log will not be modified
    						    /\ MR.m_sel h0 k_log == MR.m_sel h1 k_log
						    /\ h0==h1))       // and the log of the key will be the same as before.
      ))
    /\ (dishonest i
    	==> (modifies regions_modified_dishonest h0 h1
    	   /\ Key.leak_key k = prf_odhGT sk pk
	   /\ makes_unfresh_just i h0 h1))
  ))
let prf_odh dh_sk dh_pk =
  let h0 = ST.get() in
  let i = generate_ae_id dh_pk.pk_id dh_sk.sk_id in
  let honest_i = is_honest i in
  MR.m_recall dh_key_log;
  MR.m_recall id_log;
  MR.m_recall id_honesty_log;
  if honest_i then (
    // This branch checks out!
    lemma_honest_not_dishonest i;
    let k = handle_honest_i i in
    k
//    MR.m_recall dh_key_log;
//    match MM.lookup dh_key_log i with
//    | Some  k' ->
//	Key.recall_log k'; 
//	fresh_unfresh_contradiction i;
//        k'
//    | None ->
//        let k' = Key.keygen i in
//        MM.extend dh_key_log i k';
//	fresh_unfresh_contradiction i;
//        k'
  ) else (
    // Getting an "unknown assertion failed" error in this branch
    lemma_dishonest_not_honest i;
    let k = handle_dishonest_i dh_sk dh_pk i in
    k
//    let raw_k = Curve.scalarmult dh_sk.rawsk dh_pk.rawpk in
//    let hashed_raw_k = HSalsa.hsalsa20 raw_k zero_nonce in
//    let k=Key.coerce_key i hashed_raw_k in
//    fresh_unfresh_contradiction i;
//    k
  )
