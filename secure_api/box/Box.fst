(**
   Top level module of the verified implementation of NaCl's Crypto_box function.
   This module contains the implementation of the actual crypto_box and crypto_box_open functions,
   as well as some related types and helper functions.
   Additionally, this module contains two tables that represent state in the modelling of PKAE.
*)
module Box

open FStar.HyperHeap
open FStar.HyperStack
open Box.Flags
open Box.AE
open Box.ODH
open Box.PlainBox
open Box.Indexing

module MR = FStar.Monotonic.RRef
module MM = MonotoneMap
module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module SPEC = Spec.SecretBox
module AE = Box.AE
module ODH = Box.ODH
module PlainBox = Box.PlainBox

#set-options "--z3rlimit 100"

(**
   The type of the ciphertext that box and box_open use.
*)
type c = AE.cipher

assume val box_log_region: (r:MR.rid{ extends r root 
					 /\ is_eternal_region r 
					 /\ is_below r root 
					 /\ disjoint r ae_log_region 
					 /\ disjoint r dh_key_log_region
					 /\ disjoint r id_log_region
					 /\ disjoint r id_honesty_log_region
					 })

assume val box_key_log_region: (r:MR.rid{ extends r root 
					 /\ is_eternal_region r 
					 /\ is_below r root 
					 /\ disjoint r ae_log_region 
					 /\ disjoint r dh_key_log_region
					 /\ disjoint r id_honesty_log_region
					 /\ disjoint r id_log_region
					 /\ disjoint r box_log_region
					 })
					 

//type box_log_key = (nonce*(i:id{AE_id? i /\ honest i}))
//type box_log_value = (cipher*protected_pkae_plain)
//type box_log_range = fun box_log_key -> box_log_value
//type box_log_inv (f:MM.map' box_log_key box_log_range) = True

type box_log_key = AE.ae_log_key
type box_log_value = AE.ae_log_value
type box_log_range = AE.ae_log_range
type box_log_inv (f:MM.map' ae_log_key ae_log_range) = True
(**
   This monotone map maps a tuple of (nonce*ciphertext) to a plaintext message. It is used if a message is
   encrypted under an honest key while PKAE is idealized. During encryption, the plaintext will be stored in the log, indexed by the id and the nonce.
   Upon decryption with an honest key, a lookup is performed in the log using the received pair of nonce and ciphertext as index. The log and its monotonic nature
   guarantee the following properties, provided PKAE is idealized and the key is honest:
   * Authenticity: Only the actors in posession of the (honest) key can insert things into the log under a certain id. Anyone who decrypts a message with a key is thus
     guaranteed that it was previously encrypted by an actor in the posession of that key.
   * Uniqueness of nonces: Only one entry can exist for any combination of nonce and key. This means that a nonce can not be used a second time with the
     same key.
*)
assume val box_log: MM.t box_log_region box_log_key box_log_range box_log_inv
//let box_log = MM.alloc #pkae_table_region #pkae_table_key #pkae_table_range #pkae_table_inv

//type box_key_log_key = i:id{AE_id? i /\ honest i}
//type box_key_log_value = (AE.key)
//type box_key_log_range = fun (i:box_key_log_key) -> (k:box_key_log_value{AE.get_index k = i})
//type box_key_log_inv (f:MM.map' box_key_log_key box_key_log_range) = True

type box_key_log_key = ODH.dh_key_log_key
type box_key_log_value = ODH.dh_key_log_value
type box_key_log_range = ODH.dh_key_log_range
type box_key_log_inv (f:MM.map' box_key_log_key box_key_log_range) = True
(**
   This monotone map maps an AE id to a key. It is used when box_beforenm generates a key using an honest DH-public key and an honest DH-private key.
   If PKAE is idealized, box_beforenm generates a random key instead of computing it from its DH components. We thus need this monotone log to guarantee that 
   for a given set of DH ids a single unique key is generated.
*)
assume val box_key_log:  MM.t box_key_log_region ODH.dh_key_log_key ODH.dh_key_log_range ODH.dh_key_log_inv
//let box_key_log = MM.alloc #pkae_table_region #pkae_table_key #pkae_table_range #pkae_table_inv

(**
   A PKAE public key, containing a DH public key.
*)
type pkae_pkey = dh_pkey

(**
   A PKAE private key, containing a DH private key.
*)
type pkae_skey = dh_skey

(**
   Generate a PKAE keypair, consisting of a public and a private key.
*)
let keygen = ODH.keygen

(**
   Log invariant: WIP
*)

//#set-options "--z3rlimit 300 --max_ifuel 12 --max_fuel 12"
// TODO - invariants:
// Remove indexing table. If we do this, we have to separate honesty tables and either (1) restrict the usage of the honesty oracle until after ODH is idealized or (2) implement a set_honest
// funtion that allows communicating to the Key (AE) module which keys are honest.
// Use a functional style instead of the logical (replace forall quantifiers).
// Use "views" -> see StreamAE. Go via ODH to reason about keys in the ODH log to get rid of the "forall" quantifiers above.
let log_invariant (h:mem) (i:id) =
  MR.m_contains box_key_log h
  /\ MR.m_contains dh_key_log h
  /\ MR.m_contains box_log h
  /\ MR.m_contains ae_log h
  /\ MR.m_sel h box_key_log == MR.m_sel h dh_key_log
  /\ MR.m_sel h box_log == MR.m_sel h ae_log
  /\ ((AE_id? i /\ honest i) ==> (MM.fresh dh_key_log i h <==> fresh i h)) // dh_key_log and box_key_log are in sync
  // Do we need this?
  /\ ((AE_id? i /\ honest i) ==> (MM.fresh dh_key_log i h ==> (forall n. MM.fresh box_log (n,i) h)))

	    
#reset-options
//#set-options "--z3rlimit 300 --max_ifuel 12 --max_fuel 12"
#set-options "--z3rlimit 100 --max_ifuel 1 --max_fuel 1"


//val unchanging_log_lemma: h0:mem -> h1:mem -> i:id -> Lemma
//  (requires (
//    let regions_modified_dishonest = [id_log_region] in
//    let regions_modified_honest_set = Set.as_set (regions_modified_dishonest @ [dh_key_log_region;box_key_log_region]) in
//    let regions_modified_dishonest_set:Set.set (r:HH.rid) = Set.as_set regions_modified_dishonest in
//    log_invariant h0 i
//    /\ MR.m_sel h0 box_log == MR.m_sel h1 box_log
//    /\ ((AE_id? i /\ honest i) ==> ((forall n. MM.fresh box_log (n,i) h0))) // for fresh keys, all nonces are fresh
//  ))
//  (ensures (
//    ((AE_id? i /\ honest i) ==> (MM.fresh dh_key_log i h1 ==> (forall n. MM.fresh box_log (n,i) h1))) // for fresh keys, all nonces are fresh
//  ))
//let unchanging_log_lemma h0 h1 i = ()


val beforenm_memory_equality_framing_lemma: h0:mem -> h1:mem -> i:id -> Lemma
  (requires (
    let regions_modified_dishonest = [id_log_region] in
    let regions_modified_honest_set = Set.as_set (regions_modified_dishonest @ [dh_key_log_region;box_key_log_region]) in
    let regions_modified_dishonest_set:Set.set (r:HH.rid) = Set.as_set regions_modified_dishonest in
    log_invariant h0 i
    /\ (modifies regions_modified_honest_set h0 h1
      \/ h0 == h1
      \/ modifies regions_modified_dishonest_set h0 h1)
    /\ MR.m_sel h0 box_log == MR.m_sel h1 box_log
  ))
  (ensures (
    MR.m_sel h1 box_log == MR.m_sel h1 ae_log  // ae_log and box_log are in sync
  ))
let beforenm_memory_equality_framing_lemma h0 h1 i = ()


#reset-options
#set-options "--z3rlimit 100 --max_ifuel 1 --max_fuel 1"
val beforenm_freshness_equality_framing_lemma: h0:mem -> h1:mem -> i:id -> k:AE.key{AE.get_index k = i} -> Lemma
  (requires (
    log_invariant h0 i
    /\ MR.m_contains id_log h0
    /\ MR.m_contains id_log h1
    /\ MR.m_contains dh_key_log h0
    /\ MR.m_contains dh_key_log h1
    /\ ((AE_id? i /\ honest i /\ MM.fresh dh_key_log i h0) ==> (MR.m_sel h1 dh_key_log == MM.upd (MR.m_sel h0 dh_key_log) i k))
    /\ ((AE_id? i /\ honest i /\ MM.defined dh_key_log i h0) ==> (MR.m_sel h1 dh_key_log == MR.m_sel h0 dh_key_log))
    /\ ((AE_id? i /\ honest i) ==> MM.defined id_log i h1)
  ))
  (ensures (
    ((AE_id? i /\ honest i) ==> (MM.fresh dh_key_log i h1 <==> fresh i h1)) // all keys that are not in the dh_key_log are fresh
  ))
let beforenm_freshness_equality_framing_lemma h0 h1 i k = ()


val beforenm_nonce_freshness_framing_lemma: h0:mem -> h1:mem -> i:id -> k:AE.key{AE.get_index k = i} -> Lemma
  (requires (
    let regions_modified_dishonest = [id_log_region] in
    let regions_modified_honest_set = Set.as_set (regions_modified_dishonest @ [dh_key_log_region;box_key_log_region]) in
    let regions_modified_dishonest_set:Set.set (r:HH.rid) = Set.as_set regions_modified_dishonest in
    log_invariant h0 i
    /\ MR.m_contains id_log h0
    /\ MR.m_contains id_log h1
    /\ MR.m_contains dh_key_log h0
    /\ MR.m_contains dh_key_log h1
    /\ ((AE_id? i /\ honest i /\ MM.fresh dh_key_log i h0) ==> (MR.m_sel h1 dh_key_log == MM.upd (MR.m_sel h0 dh_key_log) i k))
    /\ ((AE_id? i /\ honest i /\ MM.defined dh_key_log i h0) ==> (MR.m_sel h1 dh_key_log == MR.m_sel h0 dh_key_log))
    /\ (modifies regions_modified_honest_set h0 h1
      \/ h0 == h1
      \/ modifies regions_modified_dishonest_set h0 h1)
    /\ MR.m_sel h0 box_log == MR.m_sel h1 box_log
  ))
  (ensures (
    ((honest i) ==> (MM.fresh dh_key_log i h0 ==> (forall n. MM.fresh box_log (n,i) h0))) // for fresh keys, all nonces are fresh
  ))
let beforenm_nonce_freshness_framing_lemma h0 h1 i k = ()

 
#set-options "--z3rlimit 300 --max_ifuel 1 --max_fuel 0"
(**
   box_beforenm is used to generate a key using a DH public and private key. The AE id of the resulting key is a combination of the DH ids of the
   DH keys used to generate it. If idealized, the key resulting from this function will be random if both DH key ids are honest. To ensure that
   only one key is generated per DH id pair, it is stored in the box_key_log and a lookup is performed before each key is generated.
*)
val box_beforenm: pk:pkae_pkey -> 
	          sk:pkae_skey ->
		  ST (k:AE.key)
  (requires (fun h0 -> 
    let i = generate_ae_id (DH_id (pk_get_share pk)) (DH_id (sk_get_share sk)) in
    registered i
    ///\ log_invariant h0 i
    /\ MR.m_contains box_key_log h0
    /\ MR.m_contains dh_key_log h0
    /\ MR.m_contains box_log h0
    /\ MR.m_contains ae_log h0
    /\ (honest i \/ dishonest i)
    /\ MR.m_sel h0 box_key_log == MR.m_sel h0 dh_key_log  // dh_key_log and box_key_log are in sync
    /\ MR.m_sel h0 box_log == MR.m_sel h0 ae_log  // ae_log and box_log are in sync
    /\ ((AE_id? i /\ honest i) ==> (MM.fresh dh_key_log i h0 <==> fresh i h0)) // all keys that are not in the dh_key_log are fresh
    /\ ((AE_id? i /\ honest i) ==> (MM.fresh dh_key_log i h0 ==> (forall n. MM.fresh box_log (n,i) h0))) // for fresh keys, all nonces are fresh
  ))
  (ensures (fun h0 k h1 -> 
    let i = generate_ae_id (DH_id (pk_get_share pk)) (DH_id (sk_get_share sk)) in
    let regions_modified_dishonest = [id_log_region] in
    let regions_modified_honest_set = Set.as_set (regions_modified_dishonest @ [dh_key_log_region;box_key_log_region]) in
    let regions_modified_dishonest_set:Set.set (r:HH.rid) = Set.as_set regions_modified_dishonest in
    // Id sanity
    (AE.get_index k = generate_ae_id (DH_id (pk_get_share pk)) (DH_id (sk_get_share sk)))
    /\ MR.m_contains dh_key_log h1
    /\ MR.m_contains id_log h1
    /\ MR.m_contains box_key_log h1
    /\ MR.m_contains box_log h1
    /\ MR.m_contains ae_log h1
    /\ (modifies regions_modified_honest_set h0 h1
      \/ h0 == h1
      \/ modifies regions_modified_dishonest_set h0 h1)
    ///\ log_invariant h1 i
    /\ MR.m_sel h1 box_key_log == MR.m_sel h1 dh_key_log (*x*)  // dh_key_log and box_key_log are in sync
    // Use the framing lemma for this!
    /\ ((AE_id? i /\ honest i) ==> (MM.fresh dh_key_log i h1 <==> fresh i h1)) (*x*) // all keys that are not in the dh_key_log are fresh
    // Do we need this?
    ///\ ((AE_id? i /\ honest i) ==> (MM.fresh dh_key_log i h1 ==> (forall n. MM.fresh box_log (n,i) h1))) // for fresh keys, all nonces are fresh
    // If honest, something is inserted into the log
    /\ ((honest i /\ MM.fresh box_key_log i h0) ==> (MR.m_sel h1 box_key_log == MM.upd (MR.m_sel h0 box_key_log) i k))
    /\ ((honest i /\ MM.fresh box_key_log i h0) ==> (makes_unfresh_just i h0 h1))
    /\ ((honest i /\ MM.fresh box_key_log i h0) ==> (modifies regions_modified_honest_set h0 h1))
    /\ ((honest i /\ MM.defined box_key_log i h0) ==> (MR.m_sel h0 box_key_log == MR.m_sel h1 box_key_log))
    /\ ((honest i /\ MM.defined box_key_log i h0) ==> (h0==h1))
    /\ ((honest i) ==> (MR.witnessed (MM.contains box_key_log i k)))
    /\ ((honest i) ==> (MM.contains box_key_log i k h1))
    					        ///\ makes_unfresh_just i h0 h1)))
    					 ///\ modifies regions_modified_honest_set h0 h1))))
    	 ///\ (MM.defined box_key_log i h0 ==> (//MR.m_sel h0 box_key_log == MR.m_sel h1 box_key_log))))
    	 //				   h0 == h1))))
    	 ///\ MR.witnessed (MM.contains box_key_log i k)
    	 ///\ MM.contains box_key_log i k h1))
    // If dishonest, the returned key is actually computed from both DH keys.
    /\ (dishonest i (*x*)
      ==> (modifies regions_modified_dishonest_set h0 h1
         /\ leak_key k = ODH.prf_odhGT sk pk))
    //// id is fresh if it is in the box_key_log, 
    //// sync between box_key_log and dh_key_log and
    //// if id is fresh, then there are no entries for it in the box_log
    ///\ log_invariant h1 i (*x*)
    ////// Liveness of global logs and local key log of the returned key.
    ///\ MR.m_contains id_log h1 (*x*)
    ///\ MR.m_contains id_honesty_log h1 (*x*)
    ///\ MR.m_contains box_log h1 (*x*)
    ///\ MR.m_contains box_key_log h1 (*x*)
    ///\ MR.m_contains dh_key_log h1 (*x*)
  ))
 
let box_beforenm pk sk =
  MR.m_recall id_log;
  MR.m_recall id_honesty_log;
  MR.m_recall dh_key_log;
  MR.m_recall box_key_log;
  MR.m_recall box_log;
  MR.m_recall ae_log;
  let h0 = ST.get() in
  let i = generate_ae_id (DH_id (pk_get_share pk)) (DH_id (sk_get_share sk)) in
  let k = prf_odh sk pk in
  MR.m_recall id_log;
  MR.m_recall id_honesty_log;
  MR.m_recall dh_key_log;
  MR.m_recall box_key_log;
  MR.m_recall box_log;
  MR.m_recall ae_log;
  (if is_honest i then (
    match MM.lookup box_key_log i with
    | Some _ ->
      ()
    | None -> 
      MM.extend box_key_log i k;
      ()
  ));
  MR.m_recall id_log;
  MR.m_recall id_honesty_log;
  MR.m_recall dh_key_log;
  MR.m_recall box_key_log;
  MR.m_recall box_log;
  MR.m_recall ae_log;
  let h1 = ST.get() in
  //assert((honest i /\ MM.fresh box_key_log i h0) ==> makes_unfresh_just i h0 h1);
  //assert((honest i /\ MM.fresh box_key_log i h0) ==> (MR.m_sel h1 box_key_log == MM.upd (MR.m_sel h0 box_key_log) i k));
  k


#set-options "--z3rlimit 100 --max_ifuel 0 --max_fuel 0"
val afternm_memory_equality_framing_lemma: h0:mem -> h1:mem -> i:id -> Lemma
  (requires (
    let modified_regions:Set.set (r:HH.rid) = Set.singleton ae_log_region in
    log_invariant h0 i
    /\ (modifies modified_regions h0 h1 \/ h0 == h1)
    /\ MR.m_contains id_log h0
    /\ MR.m_contains id_log h1
  ))
  (ensures (
    MR.m_sel h1 box_key_log == MR.m_sel h1 dh_key_log
    /\ MR.m_sel h0 id_log == MR.m_sel h1 id_log
    /\ ((AE_id? i /\ honest i) ==> (MM.fresh dh_key_log i h1 <==> fresh i h1)) // dh_key_log and box_key_log are in sync
  ))
let afternm_memory_equality_framing_lemma h0 h1 i = ()


#set-options "--z3rlimit 100 --max_ifuel 0 --max_fuel 0"
assume val afternm_log_append_framing_lemma: h0:mem -> h1:mem -> i:id{AE_id? i} -> n:nonce -> c:c -> p:protected_pkae_plain{PlainBox.get_index p = i} -> Lemma
  (requires (
    let m = AE.message_wrap #i p in
    let key = (n,i) in
    let value = (c,m) in
    MR.m_contains ae_log h0
    /\ MR.m_contains ae_log h1
    /\ MR.m_contains box_log h0
    /\ MR.m_contains box_log h1
    /\ MR.m_sel h0 ae_log == MR.m_sel h0 box_log
    /\ MR.m_sel h1 box_log == MM.upd (MR.m_sel h0 box_log) key value
    /\ MR.m_sel h1 ae_log == MM.upd (MR.m_sel h0 ae_log) key value
  ))
  (ensures (
    MR.m_sel h1 box_log == MR.m_sel h1 ae_log
  ))
//let afternm_log_append_framing_lemma h0 h1 i  c k n p = ()


#set-options "--z3rlimit 100 --max_ifuel 0 --max_fuel 0"
val afternm_nonce_freshness_framing_lemma: h0:mem -> h1:mem -> i:id{AE_id? i} -> n:nonce -> c:c -> p:protected_pkae_plain{PlainBox.get_index p = i} -> Lemma
  (requires (
    let m = AE.message_wrap #i p in
    let key = (n,i) in
    let value = (c,m) in
    let modified_regions:Set.set (r:HH.rid) = Set.singleton ae_log_region in
    honest i
    /\ MR.m_contains ae_log h0
    /\ MR.m_contains ae_log h1
    /\ MR.m_contains box_log h0
    /\ MR.m_contains box_log h1
    /\ MR.m_contains dh_key_log h0
    /\ MR.m_contains dh_key_log h1
    /\ (modifies modified_regions h0 h1 \/ h0 == h1)
    /\ (honest i ==> MR.m_sel h0 ae_log == MR.m_sel h0 box_log)
    /\ (honest i ==> MR.m_sel h1 box_log == MR.m_sel h1 ae_log)
    /\ (honest i ==> MR.m_sel h1 ae_log == MM.upd (MR.m_sel h0 ae_log) key value)
    /\ (honest i ==> MR.m_sel h1 box_log == MM.upd (MR.m_sel h0 box_log) key value)
    /\ ((AE_id? i /\ honest i /\ MM.fresh dh_key_log i h0) ==> (forall (n:nonce) . (MM.fresh box_log (n,i) h0))) // if it is not in the box_key_log, then there should be no nonces recorded in the box_log
    /\ MM.defined dh_key_log i h0
    /\ MM.defined dh_key_log i h1
  ))
  (ensures (
    ((AE_id? i /\ honest i /\ MM.fresh dh_key_log i h1) ==> (forall (n:nonce) . (MM.fresh box_log (n,i) h1))) // if it is not in the box_key_log, then there should be no nonces recorded in the box_log
  ))
let afternm_nonce_freshness_framing_lemma h0 h1 i n c p = ()


#reset-options
#set-options "--z3rlimit 200 --max_ifuel 1 --max_fuel 1"
(**
   box_afternm is used to encrypt a plaintext under an AE key using a nonce. If idealized and if the AE id is honest,
   the plaintext is stored in the box_log indexed by the AE id and the nonce.
*)
val box_afternm: k:AE.key ->
		     n:nonce ->
		     p:protected_pkae_plain{PlainBox.get_index p = AE.get_index k} ->
		     ST c
  (requires (fun h0 -> 
    let i = AE.get_index k in
    // Liveness of global logs and local key log of the returned key.
    MR.m_contains id_log h0
    /\ MR.m_contains id_honesty_log h0
    /\ MR.m_contains ae_log h0
    /\ MR.m_contains box_log h0
    /\ MR.m_contains box_key_log h0
    /\ MR.m_contains dh_key_log h0
    ///\ log_invariant h0 i
    // Nonce freshness
    /\ ((honest i) ==> MM.fresh box_log (n,i) h0)
    // If the key is honest, it needs to be in the box_key_log
    /\ ((honest i) ==> MM.defined box_key_log i h0)
    // The key isn't fresh
    /\ ~(fresh i h0)
    /\ MR.m_sel h0 box_key_log == MR.m_sel h0 dh_key_log
    /\ MR.m_sel h0 ae_log == MR.m_sel h0 box_log
    /\ ((AE_id? i /\ honest i) ==> (MM.fresh dh_key_log i h0 <==> fresh i h0)) // dh_key_log and box_key_log are in sync
    /\ ((AE_id? i /\ honest i /\ MM.fresh box_key_log i h0) ==> (forall (n:nonce) . (MM.fresh box_log (n,i) h0))) // if it is not in the box_key_log, then there should be no nonces recorded in the box_log
  ))
  (ensures (fun h0 c h1 -> 
    let i = AE.get_index k in
    let modified_regions:Set.set (r:HH.rid) = Set.union (Set.singleton box_log_region) (Set.singleton ae_log_region) in
    let k_raw = get_keyGT k in
    // If dishonest or not idealizing, then we encrypt the actual message.
    ((~(b2t pkae_ind_cpa) \/ dishonest i)
      ==> (c = SPEC.secretbox_easy (PlainBox.repr p) (AE.get_keyGT k) n))
    // If honest and idealizing, we encrypt zeros.
    /\ ((b2t pkae /\ honest i)
      ==> (c == SPEC.secretbox_easy (AE.create_zero_bytes (length p)) (AE.get_keyGT k) n))
    //// We have put the message both in the local key log and in the box_log
    /\ ((honest i) ==> (MR.witnessed (MM.contains box_log (n,i) (c,(AE.message_wrap #i p)))
                                /\ MR.m_sel h1 box_log == MM.upd (MR.m_sel h0 box_log) (n,i) (c,(AE.message_wrap #i p))))
    /\ ((dishonest i) ==> h0 == h1)
    /\ ((honest i) ==> modifies modified_regions h0 h1)
    //// Liveness of global logs and the local key log.
    ///\ MR.m_contains id_log h1
    ///\ MR.m_contains id_honesty_log h1
    ///\ MR.m_contains box_log h1
    ///\ MR.m_contains box_key_log h1
    ///\ MR.m_contains dh_key_log h1
    ///\ log_invariant h1 i
    // Both of these done via framing lemma.
    ///\ MR.m_sel h1 box_key_log == MR.m_sel h1 dh_key_log
    ///\ MR.m_sel h1 ae_log == MR.m_sel h1 box_log
    ///\ ((AE_id? i /\ honest i) ==> (MM.fresh dh_key_log i h0 <==> fresh i h0)) // dh_key_log and box_key_log are in sync
    ///\ ((AE_id? i /\ honest i /\ MM.fresh dh_key_log i h1) ==> (forall (n:nonce) . (MM.fresh box_log (n,i) h1))) // if it is not in the box_key_log, then there should be no nonces recorded in the box_log
  ))


let box_afternm k n p =
  MR.m_recall id_honesty_log;
  MR.m_recall box_key_log;
  MR.m_recall id_log;
  MR.m_recall dh_key_log;
  MR.m_recall box_log;
  let i = AE.get_index k in
  fresh_unfresh_contradiction i;
  let c = AE.encrypt #i n k (AE.message_wrap #i p) in
  MR.m_recall id_honesty_log;
  MR.m_recall box_key_log;
  MR.m_recall id_log;
  MR.m_recall dh_key_log;
  MR.m_recall box_log;
  let honest_i = is_honest i in
  (if honest_i then (
    //lemma_honest_not_dishonest i;
    MM.extend box_log (n,i) (c,AE.message_wrap #i p)
  ) else (
    //lemma_dishonest_not_honest i;
    ()));
  MR.m_recall id_honesty_log;
  MR.m_recall box_key_log;
  MR.m_recall id_log;
  MR.m_recall dh_key_log;
  MR.m_recall box_log;
  c
  

val box: pk:pkae_pkey -> 
	     sk:pkae_skey -> 
	     n:nonce -> 
	     p:protected_pkae_plain{PlainBox.get_index p = generate_ae_id (DH_id (pk_get_share pk)) (DH_id (sk_get_share sk))} 
	     -> ST c
  (requires (fun h0 ->
    let i = generate_ae_id (DH_id (pk_get_share pk)) (DH_id (sk_get_share sk)) in
    registered i
    /\ (honest i \/ dishonest i)
    // Liveness of global logs
    /\ MR.m_contains id_log h0
    /\ MR.m_contains id_honesty_log h0
    /\ MR.m_contains box_log h0
    /\ MR.m_contains ae_log h0
    /\ MR.m_contains box_key_log h0
    /\ MR.m_contains dh_key_log h0
    // Make sure that log_invariants hold.
    ///\ log_invariant h0 i
    // Make sure that nonce is fresh
    /\ MM.fresh box_log (n,i) h0
    /\ MR.m_sel h0 box_key_log == MR.m_sel h0 dh_key_log  // dh_key_log and box_key_log are in sync
    /\ MR.m_sel h0 box_log == MR.m_sel h0 ae_log  // ae_log and box_log are in sync
    /\ ((AE_id? i /\ honest i) ==> (MM.fresh dh_key_log i h0 <==> fresh i h0)) // all keys that are not in the dh_key_log are fresh
    /\ ((AE_id? i /\ honest i) ==> (MM.fresh dh_key_log i h0 ==> (forall n. MM.fresh box_log (n,i) h0))) // for fresh keys, all nonces are fresh
  ))
  (ensures (fun h0 c h1 -> 
    let i = generate_ae_id (DH_id (pk_get_share pk)) (DH_id (sk_get_share sk)) in
    // Make sure that log_invariants hold. Would like to ensure "all_keys" variant, but too expensive to verify currently.
    log_invariant h1 i
    /\ ((~(b2t pkae_ind_cpa) \/ dishonest i)
      ==> (c = SPEC.secretbox_easy (PlainBox.repr p) (prf_odhGT sk pk) n))
    // If honest and idealizing, we encrypt zeros.
    // TODO: How to get hold of the key?
    ///\ ((b2t pkae /\ honest i)
    //  ==> (c == SPEC.secretbox_easy (AE.create_zero_bytes (length p)) (AE.get_keyGT k) n))
    //// We have put the message both in the local key log and in the box_log
    /\ ((honest i) ==> (MR.witnessed (MM.contains box_log (n,i) (c,(AE.message_wrap #i p)))
                                /\ MR.m_sel h1 box_log == MM.upd (MR.m_sel h0 box_log) (n,i) (c,(AE.message_wrap #i p))))
    /\ MR.m_contains id_log h1
    /\ MR.m_contains id_honesty_log h1
    /\ MR.m_contains box_log h1
    /\ MR.m_contains box_key_log h1
    /\ MR.m_contains dh_key_log h1
  ))


#set-options "--z3rlimit 300 --max_ifuel 0 --max_fuel 0"
let box pk sk n p =
  let i = generate_ae_id (DH_id (pk_get_share pk)) (DH_id (sk_get_share sk)) in
  let h0 = ST.get() in
  let k = box_beforenm pk sk in
  let h1 = ST.get() in
  beforenm_memory_equality_framing_lemma h0 h1 i;
  beforenm_freshness_equality_framing_lemma h0 h1 i k;
  beforenm_nonce_freshness_framing_lemma h0 h1 i k;
  admit()
  // It verifies until here. Continue here.

  let h0 = ST.get() in
  let c = box_afternm k n p in
  let h1 = ST.get() in
  afternm_memory_equality_framing_lemma h0 h1 i;
  afternm_log_append_framing_lemma h0 h1 i;
  afternm_nonce_freshness_framing_lemma h0 h1 i n c p;
  c


//val box_open: #(sk_id:id{DH_id? sk_id}) -> 
//	     #(pk_id:id{DH_id? pk_id}) -> 
//	     n:nonce ->  
//	     sk:pkae_skey sk_id{registered sk_id} ->
//	     pk:pkae_pkey pk_id{registered pk_id} -> 
//	     c:cipher ->
//	     ST(option (p:protected_pkae_plain))
//  (requires (fun h0 ->
//    let i = generate_ae_id (DH_id (pk_get_share pk)) (DH_id (sk_get_share sk)) in
//    registered i
//    // Liveness of global logs
//    /\ MR.m_contains box_log h0
//    /\ MR.m_contains id_log h0
//    /\ MR.m_contains box_key_log h0
//    /\ MR.m_contains dh_key_log h0
//    // Make sure that log_invariant holds.
//    /\ log_invariant h0 i
//  ))
//  (ensures (fun h0 p h1 -> 
//    let i = generate_ae_id (DH_id (pk_get_share pk)) (DH_id (sk_get_share sk)) in
//    log_invariant h1 i
//  ))
//let box_open #sk_id #pk_id n sk pk c =
//  let k = box_beforenm #pk_id #sk_id pk sk in
//  let i = AE.get_index k in
//  match AE.decrypt #i n k c with
//  | Some p -> 
//    let p' = (AE.message_unwrap #i p) in 
//    Some p'
//  | None -> None
