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

#set-options "--z3rlimit 100 --lax"

(**
   The type of the ciphertext that box and box_open use.
*)
type c = AE.cipher

assume val box_log_region: (r:MR.rid{ extends r root 
					 /\ is_eternal_region r 
					 /\ is_below r root 
					 /\ disjoint r ae_key_region 
					 /\ disjoint r dh_key_log_region
					 /\ disjoint r id_honesty_log_region
					 /\ disjoint r id_log_region
					 })

assume val box_key_log_region: (r:MR.rid{ extends r root 
					 /\ is_eternal_region r 
					 /\ is_below r root 
					 /\ disjoint r ae_key_region 
					 /\ disjoint r dh_key_log_region
					 /\ disjoint r id_honesty_log_region
					 /\ disjoint r id_log_region
					 /\ disjoint r box_log_region
					 })
					 

type box_log_key = (nonce*(i:id{AE_id? i /\ honest i}))
type box_log_value = (cipher*protected_pkae_plain)
type box_log_range = fun box_log_key -> box_log_value
type box_log_inv (f:MM.map' box_log_key box_log_range) = True

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
assume val box_key_log:  MM.t box_key_log_region box_key_log_key box_key_log_range box_key_log_inv
//let box_key_log = MM.alloc #pkae_table_region #pkae_table_key #pkae_table_range #pkae_table_inv
 
(**
   A PKAE public key, containing a DH public key.
*)
noeq type pkae_pkey (pk_id:id{DH_id? pk_id}) =
  | PKey: dh_pk:dh_pkey{ODH.pk_get_index dh_pk=pk_id} -> pkae_pkey pk_id

(**
   A PKAE private key, containing a DH private key.
*)
noeq abstract type pkae_skey (sk_id:id{DH_id? sk_id}) =
  | SKey: dh_sk:dh_skey{ODH.sk_get_index dh_sk=sk_id} -> pkae_pk:pkae_pkey sk_id -> pkae_skey sk_id

(**
   Generate a PKAE keypair, consisting of a public and a private key.
*)
val keygen: #(i:id{DH_id? i}) -> ST (pkae_pkey i * pkae_skey i)
  (requires (fun h0 -> 
    fresh i h0
    /\ registered i
  ))
  (ensures (fun h0 res h1 -> 
    unfresh i
    /\ modifies (Set.singleton id_log_region) h0 h1
  ))
let keygen #i =
  let (dh_pk, dh_sk) = ODH.keygen #i in
  let pkae_pk = PKey #i dh_pk in
  pkae_pk, SKey #i dh_sk pkae_pk

(**
   Log invariant: WIP
*)

// TODO: We should be able to replace "dishonest i"  with "~(honest i)" everywhere!
// TODO: Add patterns to quantifiers.
let log_invariant_all_keys (h:mem) = 
  // Removed this and made it a requirement only for the id that is currently handled.
  //(forall (i:id{AE_id? i /\ honest i}) . MM.defined box_key_log i h <==> MM.defined dh_key_log i h) // dh_key_log and box_key_log are in sync
  // Removed this and made it a requirement only for the id that is currently handled.
  ///\ (forall (i:id{AE_id? i /\ honest i}) . MM.fresh box_key_log i h <==> fresh i h) // all honest keys must be present in the box_key_log
  (forall (i:id{AE_id? i /\ honest i /\ MM.defined box_key_log i h}) . let k = MM.value box_key_log i h in // if it is in the box_key_log, then the local key_log
  								let k_log = get_logGT k in          // should be contained in the heap.
								MR.m_contains k_log h)
  /\ (forall (i:id{AE_id? i /\ honest i /\ MM.defined box_key_log i h}) (n:nonce) . let k = MM.value box_key_log i h in // if it is in the box_key_log, then box_log and the local key_log
  									    let k_log = get_logGT k in          // should be in sync.
  									    MM.defined box_log (n,i) h <==> MM.defined k_log n h)
  // Removed this and made it a requirement only for the id that is currently handled.
  ///\ (forall (i:id{AE_id? i /\ honest i}) (n:nonce) . (MM.fresh box_key_log i h ==> MM.fresh box_log (n,i) h)) // if it is not in the box_key_log, then there should be no nonces recorded in the box_log

let log_invariant_id (h:mem) (i:id) =
  MR.m_sel h box_key_log == MR.m_sel h dh_key_log
  /\ ((AE_id? i /\ honest i) ==> (MM.fresh dh_key_log i h <==> fresh i h)) // dh_key_log and box_key_log are in sync
  /\ (AE_id? i /\ honest i /\ MM.fresh box_key_log i h) ==> (forall (n:nonce) . (MM.fresh box_log (n,i) h)) // if it is not in the box_key_log, then there should be no nonces recorded in the box_log

let log_invariant_single_key (h:mem) (i:id) (k:AE.key) =
  ((AE_id? i /\ honest i /\  MM.defined box_key_log i h) ==> (let k_log = get_logGT k in MR.m_contains k_log h))
  /\ ((AE_id? i /\ honest i /\ MM.defined box_key_log i h) ==> (forall (n:nonce) . let k_log = get_logGT k in
  										      MM.defined box_log (n,i) h <==> MM.defined k_log n h))

private val recall_global_logs: unit -> ST unit
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> 
    h0 == h1
    /\ MR.m_contains id_log h1
    /\ MR.m_contains box_log h1
    /\ MR.m_contains box_key_log h1
    /\ MR.m_contains dh_key_log h1
  ))
let recall_global_logs () =
  MR.m_recall id_log;
  MR.m_recall dh_key_log;
  MR.m_recall box_log;
  MR.m_recall box_key_log


(**
   box_beforenm is used to generate a key using a DH public and private key. The AE id of the resulting key is a combination of the DH ids of the
   DH keys used to generate it. If idealized, the key resulting from this function will be random if both DH key ids are honest. To ensure that
   only one key is generated per DH id pair, it is stored in the box_key_log and a lookup is performed before each key is generated.
*)
val box_beforenm: #(pk_id:id{DH_id? pk_id /\ registered pk_id}) -> 
	              #(sk_id:id{DH_id? sk_id /\ registered sk_id}) -> 
	              pk:pkae_pkey pk_id -> 
	              sk:pkae_skey sk_id ->
		      ST (k:AE.key)
  (requires (fun h0 -> 
    let i = generate_ae_id pk_id sk_id in
    registered i
    // Sync of box_log and all local key_logs
    /\ log_invariant_all_keys h0
    // id is fresh if it is in the box_key_log, 
    // sync between box_key_log and dh_key_log and
    // if id is fresh, then there are no entries for it in the box_log
    /\ log_invariant_id h0 i
    // Liveness of global logs
    /\ MR.m_contains id_log h0
    /\ MR.m_contains id_honesty_log h0
    /\ MR.m_contains box_log h0
    /\ MR.m_contains box_key_log h0
    /\ MR.m_contains dh_key_log h0
    /\ MR.m_sel h0 box_key_log == MR.m_sel h0 dh_key_log
    /\ ((AE_id? i /\ honest i) ==> (MM.fresh dh_key_log i h0 <==> fresh i h0)) // dh_key_log and box_key_log are in sync
    /\ ((AE_id? i /\ honest i /\ MM.fresh box_key_log i h0) ==> (forall (n:nonce) . (MM.fresh box_log (n,i) h0))) // if it is not in the box_key_log, then there should be no nonces recorded in the box_log
  ))
  (ensures (fun h0 k h1 -> 
    let i = generate_ae_id pk_id sk_id in
    let regions_modified_dishonest = [id_log_region] in
    let regions_modified_honest_set = Set.as_set (regions_modified_dishonest @ [dh_key_log_region;box_key_log_region]) in
    let regions_modified_dishonest_set:Set.set (r:HH.rid) = Set.as_set regions_modified_dishonest in
    let k_log = get_logGT k in
    // Id sanity
    (AE.get_index k = generate_ae_id pk_id sk_id)
    // If honest, something is inserted into the log
    /\ ((AE_id?i /\ honest i) (*x*)
      ==> (let current_log = MR.m_sel h0 box_key_log in
         (MM.fresh box_key_log i h0 ==> (MR.m_sel h1 box_key_log == MM.upd current_log i k
    					 /\ MR.m_sel h1 k_log == AE.empty_log i
    					 /\ makes_unfresh_just i h0 h1
    					 /\ modifies regions_modified_honest_set h0 h1))
    	 /\ (MM.defined box_key_log i h0 ==> (MR.m_sel h0 box_key_log == MR.m_sel h1 box_key_log
    					   /\ MR.m_sel h0 k_log == MR.m_sel h1 k_log
    					   /\ h0 == h1))
    	 /\ MR.witnessed (MM.contains box_key_log i k)
    	 /\ MM.contains box_key_log i k h1))
    // If dishonest, the returned key is actually computed from both DH keys.
    /\ (dishonest i (*x*)
      ==> (modifies regions_modified_dishonest_set h0 h1
         /\ leak_key k = ODH.prf_odhGT sk.dh_sk pk.dh_pk))
    //// Sync of box_log and the local log of the returned key
    // TODO: This does not work yet, although it does when it's the only postcondition.
    /\ log_invariant_single_key h1 i k
    //// id is fresh if it is in the box_key_log, 
    //// sync between box_key_log and dh_key_log and
    //// if id is fresh, then there are no entries for it in the box_log
    //// TODO: This makes only sense if we demand it for all ids. For performance reasons, 
    //// this is currently only for the id used in this function
    /\ log_invariant_id h1 i (*x*)
    //// Liveness of global logs and local key log of the returned key.
    /\ MR.m_contains k_log h1 (*x*)
    /\ MR.m_contains id_log h1 (*x*)
    /\ MR.m_contains id_honesty_log h1 (*x*)
    /\ MR.m_contains box_log h1 (*x*)
    /\ MR.m_contains box_key_log h1 (*x*)
    /\ MR.m_contains dh_key_log h1 (*x*)
    // Would like to ensure for all keys, but verification takes too much time. Need a smarter invariant (via patterns?).
    ///\ log_invariant_all_keys h1
  ))
let box_beforenm #pk_id #sk_id pk sk =
  MR.m_recall id_log;
  MR.m_recall id_honesty_log;
  MR.m_recall dh_key_log;
  MR.m_recall box_log;
  MR.m_recall box_key_log;
  let i = generate_ae_id pk_id sk_id in
  let h0 = ST.get() in
  let k = prf_odh sk.dh_sk pk.dh_pk in
  MR.m_recall id_log;
  MR.m_recall id_honesty_log;
  MR.m_recall dh_key_log;
  MR.m_recall box_log;
  MR.m_recall box_key_log;
  recall_log k;
  (if is_honest i then
    match MM.lookup box_key_log i with
    | Some _ ->
      let h1 = ST.get() in
      assert((AE_id? i /\ honest i) ==> MM.contains dh_key_log i k h1);
      assert((AE_id? i /\ honest i) ==> MM.contains box_key_log i k h1);
      ()
    | None -> 
      MM.extend box_key_log i k;
      let h1 = ST.get() in
      assert(honest i ==> MM.contains dh_key_log i k h1);
      assert(honest i ==> MM.contains box_key_log i k h1);
      ());
  recall_log k;
  MR.m_recall id_log;
  MR.m_recall id_honesty_log;
  MR.m_recall dh_key_log;
  MR.m_recall box_log;
  MR.m_recall box_key_log;
  let h1 = ST.get() in
  //assert(  let regions_modified_dishonest = [id_log_region] in
  //  let regions_modified_honest_set = Set.as_set (regions_modified_dishonest @ [dh_key_log_region;box_key_log_region]) in
  //  let regions_modified_dishonest_set:Set.set (r:HH.rid) = Set.as_set regions_modified_dishonest in
  //  dishonest i ==> (modifies regions_modified_dishonest_set h0 h1 /\ makes_unfresh_just i h0 h1 /\ AE.leak_key k = prf_odhGT sk.dh_sk pk.dh_pk ));
  //let h = ST.get() in
  //assert(log_invariant_single_key h i k);
  //admit();
  k


#reset-options
#set-options "--z3rlimit 200 --max_ifuel 8 --max_fuel 8"
(**
   box_afternm is used to encrypt a plaintext under an AE key using a nonce. If idealized and if the AE id is honest,
   the plaintext is stored in the box_log indexed by the AE id and the nonce.
*)
val box_afternm: k:AE.key ->
		     n:nonce ->
		     p:protected_pkae_plain{PlainBox.get_index p = AE.get_index k} ->
		     ST c
  (requires (fun h0 -> 
    let k_log = get_logGT k in
    let i = AE.get_index k in
    // Liveness of global logs and local key log of the returned key.
    MR.m_contains k_log h0
    /\ MR.m_contains id_log h0
    /\ MR.m_contains id_honesty_log h0
    /\ MR.m_contains box_log h0
    /\ MR.m_contains box_key_log h0
    /\ MR.m_contains dh_key_log h0
    // Sync of box_log and the local log of the returned key
    /\ log_invariant_single_key h0 i k
    // id is fresh if it is in the box_key_log, 
    // sync between box_key_log and dh_key_log and
    // if id is fresh, then there are no entries for it in the box_log
    /\ log_invariant_id h0 i
    // Nonce freshness
    /\ ((honest i) ==> MM.fresh box_log (n,i) h0)
    // If the key is honest, it needs to be in the box_key_log
    /\ ((honest i) ==> MM.defined box_key_log i h0)
    // The key isn't fresh
    /\ ~(fresh i h0)
    /\ MR.m_sel h0 box_key_log == MR.m_sel h0 dh_key_log
    /\ ((AE_id? i /\ honest i) ==> (MM.fresh dh_key_log i h0 <==> fresh i h0)) // dh_key_log and box_key_log are in sync
    /\ ((AE_id? i /\ honest i /\ MM.fresh box_key_log i h0) ==> (forall (n:nonce) . (MM.fresh box_log (n,i) h0))) // if it is not in the box_key_log, then there should be no nonces recorded in the box_log
  ))
  (ensures (fun h0 c h1 -> 
    let i = AE.get_index k in
    let k_log = get_logGT k in
    let k_raw = get_keyGT k in
    // If dishonest or not idealizing, then we encrypt the actual message.
    ((dishonest i \/ ~(b2t pkae))
      ==> (c = SPEC.secretbox_easy (PlainBox.repr p) (AE.get_keyGT k) n))
    // If honest and idealizing, we encrypt zeros.
    ///\ ((honest i /\ b2t pkae)
    //  ==> (c == SPEC.secretbox_easy (AE.create_zero_bytes (length p)) (AE.get_keyGT k) n))
    //// We have put the message both in the local key log and in the box_log
    ///\ MR.witnessed (MM.contains k_log n (c,AE.message_wrap p))
    /////\ MR.witnessed (MM.contains box_log (n,i) (c,p))
    //// Liveness of global logs and the local key log.
    ///\ MR.m_contains id_log h1
    ///\ MR.m_contains id_honesty_log h1
    ///\ MR.m_contains box_log h1
    ///\ MR.m_contains box_key_log h1
    ///\ MR.m_contains dh_key_log h1
    ///\ MR.m_contains k_log h1
    //// id is fresh if it is in the box_key_log, 
    //// sync between box_key_log and dh_key_log and
    //// if id is fresh, then there are no entries for it in the box_log
    ///\ log_invariant_single_key h1 i k
    //// Sync of box_log and the local log of the returned key
    ///\ log_invariant_id h1 i
  ))
let box_afternm k n p =
  MR.m_recall id_honesty_log;
  MR.m_recall box_key_log;
  MR.m_recall id_log;
  MR.m_recall dh_key_log;
  MR.m_recall box_log;
  recall_log k;
  let i = AE.get_index k in
  fresh_unfresh_contradiction i;
  let ae_m = AE.message_wrap #i p in
  let c = AE.encrypt #i n k ae_m in
  MR.m_recall id_honesty_log;
  MR.m_recall box_key_log;
  MR.m_recall id_log;
  MR.m_recall dh_key_log;
  MR.m_recall box_log;
  let honest_i = is_honest i in
  (if honest_i then
    MM.extend box_log (n,i) (c,p));
  MR.m_recall id_honesty_log;
  MR.m_recall box_key_log;
  MR.m_recall id_log;
  MR.m_recall dh_key_log;
  MR.m_recall box_log;
  recall_log k;
  c
  

val box: #(pk_id:id{DH_id? pk_id}) -> 
	     #(sk_id:id{DH_id? sk_id}) -> 
	     pk:pkae_pkey pk_id{registered pk_id} -> 
	     sk:pkae_skey sk_id{registered sk_id} -> 
	     n:nonce -> 
	     p:protected_pkae_plain{PlainPKAE.get_index p = generate_ae_id pk_id sk_id} 
	     -> ST c
  (requires (fun h0 ->
    let i = generate_ae_id pk_id sk_id in
    registered i
    // Liveness of global logs
    /\ MR.m_contains id_log h0
    /\ MR.m_contains id_honesty_log h0
    /\ MR.m_contains box_log h0
    /\ MR.m_contains box_key_log h0
    /\ MR.m_contains dh_key_log h0
    // Make sure that log_invariants hold.
    /\ log_invariant_all_keys h0
    /\ log_invariant_id h0 i
    // Make sure that nonce is fresh
    /\ MM.fresh box_log (n,i) h0
  ))
  (ensures (fun h0 c h1 -> 
    let i = generate_ae_id pk_id sk_id in
    // Make sure that log_invariants hold. Would like to ensure "all_keys" variant, but too expensive to verify currently.
    log_invariant_id h1 i
    // TODO: Proof via reasoning over h1
    ///\ log_invariant_single_key h1 i k
    /\ MR.m_contains id_log h1
    /\ MR.m_contains id_honesty_log h1
    /\ MR.m_contains box_log h1
    /\ MR.m_contains box_key_log h1
    /\ MR.m_contains dh_key_log h1
    ///\ log_invariant_all_keys h1
  ))
let box #pk_id #sk_id pkae_pk pkae_sk n p =
  let k = box_beforenm #pk_id #sk_id pkae_pk pkae_sk in
  let c = box_afternm k n p in
  c

val box_open: #(sk_id:id{DH_id? sk_id}) -> 
	     #(pk_id:id{DH_id? pk_id}) -> 
	     n:nonce ->  
	     sk:pkae_skey sk_id{registered sk_id} ->
	     pk:pkae_pkey pk_id{registered pk_id} -> 
	     c:cipher ->
	     ST(option (p:protected_pkae_plain))
  (requires (fun h0 ->
    let i = generate_ae_id pk_id sk_id in
    registered i
    // Liveness of global logs
    /\ MR.m_contains box_log h0
    /\ MR.m_contains id_log h0
    /\ MR.m_contains box_key_log h0
    /\ MR.m_contains dh_key_log h0
    // Make sure that log_invariants hold.
    /\ log_invariant_all_keys h0
    ///\ log_invariant_single_key h0 i k
    /\ log_invariant_id h0 i
  ))
  (ensures (fun h0 p h1 -> 
    let i = generate_ae_id pk_id sk_id in
    // Make sure that log_invariants hold. Would like to ensure "all_keys" variant, but too expensive to verify currently.
    log_invariant_id h1 i
    /\ log_invariant_all_keys h1
  ))
let box_open #sk_id #pk_id n sk pk c =
  let k = box_beforenm #pk_id #sk_id pk sk in
  let i = AE.get_index k in
  // TODO : perform lookup in box_log
  match AE.decrypt #i n k c with
  | Some p -> 
    let p' = (AE.message_unwrap #i p) in 
    Some p'
  | None -> None
