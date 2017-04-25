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
open Box.PlainBox
open Box.Indexing

module MR = FStar.Monotonic.RRef
module MM = MonotoneMap
module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module SecretSpec = Spec.SecretBox
module CryptoSpec = Spec.CryptoBox
module AE = Box.AE
module ODH = Box.ODH
module PlainBox = Box.PlainBox

#set-options "--z3rlimit 100"

(**
   The type of the ciphertext that box and box_open use.
*)

val box_log_region: (r:MR.rid{ extends r root
           /\ is_eternal_region r
           /\ is_below r root
           /\ disjoint r AE.ae_log_region
           /\ disjoint r ODH.dh_key_log_region
           /\ disjoint r id_log_region
           /\ disjoint r id_honesty_log_region
           })
let box_log_region =
  recall_region AE.ae_log_region;
  recall_region ODH.dh_key_log_region;
  recall_region id_log_region;
  recall_region id_honesty_log_region;
  new_region root

val box_key_log_region: (r:MR.rid{ extends r root
           /\ is_eternal_region r
           /\ is_below r root
           /\ disjoint r AE.ae_log_region
           /\ disjoint r ODH.dh_key_log_region
           /\ disjoint r id_honesty_log_region
           /\ disjoint r id_log_region
           /\ disjoint r box_log_region
           })
let box_key_log_region =
  recall_region AE.ae_log_region;
  recall_region ODH.dh_key_log_region;
  recall_region id_log_region;
  recall_region id_honesty_log_region;
  recall_region box_log_region;
  new_region root

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
val box_log: MM.t box_log_region AE.ae_log_key AE.ae_log_range AE.ae_log_inv
let box_log = MM.alloc #box_log_region #AE.ae_log_key #AE.ae_log_range #AE.ae_log_inv

(**
   This monotone map maps an AE id to a key. It is used when box_beforenm generates a key using an honest DH-public key and an honest DH-private key.
   If PKAE is idealized, box_beforenm generates a random key instead of computing it from its DH components. We thus need this monotone log to guarantee that
   for a given set of DH ids a single unique key is generated.
*)
val box_key_log:  MM.t box_key_log_region ODH.dh_key_log_key ODH.dh_key_log_range ODH.dh_key_log_inv
let box_key_log = MM.alloc #box_key_log_region #ODH.dh_key_log_key #ODH.dh_key_log_range #ODH.dh_key_log_inv

(**
   A PKAE public key, containing a DH public key.
*)
type pkae_pkey = ODH.dh_pkey

(**
   A PKAE private key, containing a DH private key.
*)
type pkae_skey = ODH.dh_skey

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
let log_invariant (h:mem) (i:id) =
  MR.m_contains box_key_log h
  /\ MR.m_contains ODH.dh_key_log h
  /\ MR.m_contains box_log h
  /\ MR.m_contains AE.ae_log h
  /\ MR.m_contains id_log h
  /\ MR.m_contains id_honesty_log h
  /\ MR.m_sel h box_key_log == MR.m_sel h ODH.dh_key_log
  /\ MR.m_sel h box_log == MR.m_sel h AE.ae_log
  /\ ((AE_id? i /\ honest i) ==> (MM.fresh ODH.dh_key_log i h <==> fresh i h)) // dh_key_log and box_key_log are in sync
  /\ ((AE_id? i /\ honest i) ==> (MM.fresh ODH.dh_key_log i h ==> (forall n. MM.fresh box_log (n,i) h)))

val recall_global_logs: unit -> ST unit
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 ->
    h0 == h1
    /\ MR.m_contains ODH.dh_key_log h1
    /\ MR.m_contains box_log h1
    /\ MR.m_contains AE.ae_log h1
    /\ MR.m_contains id_log h1
    /\ MR.m_contains id_honesty_log h1
  ))
let recall_global_logs () =
  MR.m_recall id_honesty_log;
  MR.m_recall id_log;
  MR.m_recall ODH.dh_key_log;
  MR.m_recall box_key_log;
  MR.m_recall box_log;
  MR.m_recall AE.ae_log


#reset-options
#set-options "--z3rlimit 500 --max_ifuel 2 --max_fuel 0"
(**
   box_beforenm is used to generate a key using a DH public and private key. The AE id of the resulting key is a combination of the DH ids of the
   DH keys used to generate it. If idealized, the key resulting from this function will be random if both DH key ids are honest. To ensure that
   only one key is generated per DH id pair, it is stored in the box_key_log and a lookup is performed before each key is generated.
*)
val box_beforenm: pk:pkae_pkey ->
                  sk:pkae_skey ->
                  ST (k:AE.key)
  (requires (fun h0 ->
    let i = generate_ae_id (DH_id (ODH.pk_get_share pk)) (DH_id (ODH.sk_get_share sk)) in
    registered i
    /\ log_invariant h0 i
  ))
  (ensures (fun h0 k h1 ->
    let i = generate_ae_id (DH_id (ODH.pk_get_share pk)) (DH_id (ODH.sk_get_share sk)) in
    let regions_modified_dishonest = [id_log_region] in
    let regions_modified_honest_set = Set.as_set (regions_modified_dishonest @ [ODH.dh_key_log_region;box_key_log_region]) in
    let regions_modified_dishonest_set:Set.set (r:HH.rid) = Set.as_set regions_modified_dishonest in
    // Id sanity
    (AE.get_index k = generate_ae_id (DH_id (ODH.pk_get_share pk)) (DH_id (ODH.sk_get_share sk)))
    //\ log_invariant h1 i
    /\ MR.m_contains box_key_log h1
    /\ MR.m_contains ODH.dh_key_log h1
    /\ MR.m_contains box_log h1
    /\ MR.m_contains AE.ae_log h1
    /\ MR.m_contains id_log h1
    /\ MR.m_contains id_honesty_log h1
    /\ MR.m_sel h1 box_key_log == MR.m_sel h1 ODH.dh_key_log
    /\ MR.m_sel h1 box_log == MR.m_sel h1 AE.ae_log
    /\ ((AE_id? i /\ honest i) ==> (MM.fresh ODH.dh_key_log i h1 <==> fresh i h1)) // dh_key_log and box_key_log are in sync
    /\ ((AE_id? i /\ honest i) ==> (MM.fresh ODH.dh_key_log i h1 ==> (forall n. MM.fresh box_log (n,i) h1)))
    // If honest, something is inserted into the log
    /\ ((honest i /\ MM.fresh box_key_log i h0) ==> (MR.m_sel h1 box_key_log == MM.upd (MR.m_sel h0 box_key_log) i k
                                                  /\ makes_unfresh_just i h0 h1
                                                  /\ modifies (Set.union
                                                    (Set.singleton id_log_region)
                                                    (Set.union
                                                      (Set.singleton ODH.dh_key_log_region)
                                                      (Set.singleton box_key_log_region))) h0 h1))
    /\ ((honest i /\ MM.defined box_key_log i h0) ==> (MR.m_sel h0 box_key_log == MR.m_sel h1 box_key_log
                                                    /\ h0==h1))
    /\ ((honest i) ==> (MR.witnessed (MM.contains box_key_log i k)
                      /\ MM.contains box_key_log i k h1))
    /\ (dishonest i (*x*)
      ==> (modifies (Set.singleton id_log_region) h0 h1
         /\ AE.leak_key k = ODH.prf_odhGT sk pk))
    /\ ~(fresh i h1)
    /\ (dishonest i ==> AE.leak_key k = CryptoSpec.cryptobox_beforenm (ODH.pk_get_share pk) (ODH.get_skeyGT sk))
  ))

let box_beforenm pk sk =
  let i = generate_ae_id (DH_id (ODH.pk_get_share pk)) (DH_id (ODH.sk_get_share sk)) in
  let k = ODH.prf_odh sk pk in
  recall_global_logs();
  (if is_honest i then (
    match MM.lookup box_key_log i with
    | Some _ ->
      ()
    | None ->
      MM.extend box_key_log i k;
      ()
  ));
  k

#reset-options
#set-options "--z3rlimit 200 --max_ifuel 1 --max_fuel 0"
(**
   box_afternm is used to encrypt a plaintext under an AE key using a nonce. If idealized and if the AE id is honest,
   the plaintext is stored in the box_log indexed by the AE id and the nonce.
*)
val box_afternm: k:AE.key ->
         n:AE.nonce ->
         p:protected_pkae_plain (AE.get_index k) ->
         ST AE.cipher
  (requires (fun h0 ->
    let i = AE.get_index k in
    registered i
    /\ log_invariant h0 i
    // Nonce freshness
    /\ ((honest i) ==> MM.fresh box_log (n,i) h0)
    // If the key is honest, it needs to be in the box_key_log
    /\ ((honest i) ==> MM.defined box_key_log i h0)
    // The key isn't fresh
    /\ ~(fresh i h0)
  ))
  (ensures (fun h0 c h1 ->
    let i = AE.get_index k in
    let modified_regions:Set.set (r:HH.rid) = Set.union (Set.singleton box_log_region) (Set.singleton AE.ae_log_region) in
    let k_raw = AE.get_keyGT k in
    // If dishonest or not idealizing, then we encrypt the actual message.
    ((~(b2t pkae_ind_cpa) \/ dishonest i)
      ==> (eq2 #AE.cipher c (SecretSpec.secretbox_easy (PlainBox.repr p) (AE.get_keyGT k) n)))
    // If honest and idealizing, we encrypt zeros.
    /\ ((b2t pkae_ind_cpa /\ honest i)
      ==> (c == SecretSpec.secretbox_easy (AE.create_zero_bytes (length p)) (AE.get_keyGT k) n))
    //// We have put the message both in the local key log and in the box_log
    /\ ((honest i) ==> (MR.witnessed (MM.contains box_log (n,i) (c,(AE.message_wrap #i p)))))
    /\ ((honest i) ==> (MR.m_sel h1 box_log == MM.upd (MR.m_sel h0 box_log) (n,i) (c,(AE.message_wrap #i p))))
    /\ ((dishonest i) ==> h0 == h1)
    /\ ((dishonest i) ==> eq2 #AE.cipher c (CryptoSpec.cryptobox_afternm (PlainBox.repr p) n (AE.get_keyGT k)))
    /\ ((honest i) ==> modifies modified_regions h0 h1)
    /\ log_invariant h1 i
  ))


#set-options "--z3rlimit 200 --max_ifuel 1 --max_fuel 0"
let box_afternm k n p =
  let i = AE.get_index k in
  lemma_honest_or_dishonest i;
  fresh_unfresh_contradiction i;
  let c = AE.encrypt #i n k (AE.message_wrap #i p) in
  let honest_i = is_honest i in
  (if honest_i then (
    //lemma_honest_not_dishonest i;
    MM.extend box_log (n,i) (c,AE.message_wrap #i p)
  ) else (
    //lemma_dishonest_not_honest i;
    ()));
  recall_global_logs();
  c


val box: pk:pkae_pkey ->
       sk:pkae_skey ->
       n:AE.nonce ->
       p:protected_pkae_plain (generate_ae_id (DH_id (ODH.pk_get_share pk)) (DH_id (ODH.sk_get_share sk))) ->
       ST AE.cipher
  (requires (fun h0 ->
    let i = generate_ae_id (DH_id (ODH.pk_get_share pk)) (DH_id (ODH.sk_get_share sk)) in
    registered i
    // Make sure that log_invariants hold.
    /\ log_invariant h0 i
    // Make sure that nonce is fresh
    /\ MM.fresh box_log (n,i) h0
  ))
  (ensures (fun h0 c h1 ->
    let regions_modified_beforenm_dishonest = Set.singleton id_log_region in
    let regions_modified_beforenm_honest = Set.union regions_modified_beforenm_dishonest (Set.union (Set.singleton ODH.dh_key_log_region) (Set.singleton box_key_log_region)) in
    let regions_modified_afternm_honest = Set.union (Set.singleton box_log_region) (Set.singleton AE.ae_log_region) in
    let regions_modified_honest = Set.union regions_modified_beforenm_honest regions_modified_afternm_honest in
    let i = generate_ae_id (DH_id (ODH.pk_get_share pk)) (DH_id (ODH.sk_get_share sk)) in
    log_invariant h1 i
    /\ ~(fresh i h1)
    /\ ((honest i /\ MM.fresh box_key_log i h0) ==> (makes_unfresh_just i h0 h1
                                                  /\ modifies regions_modified_honest h0 h1))
    /\ ((honest i /\ MM.defined box_key_log i h0) ==> (MR.m_sel h0 box_key_log == MR.m_sel h1 box_key_log
                                                    /\ modifies regions_modified_afternm_honest h0 h1))
    /\ ((honest i)
      ==> (let k_raw = AE.get_keyGT (MM.value box_key_log i h1) in
          (~(b2t pkae_ind_cpa)
              ==> (eq2 #AE.cipher c (SecretSpec.secretbox_easy (PlainBox.repr p) k_raw n)))
          /\ ((b2t pkae_ind_cpa)
              ==> (c == SecretSpec.secretbox_easy (AE.create_zero_bytes (length p)) k_raw n))
          /\ MR.witnessed (MM.contains box_log (n,i) (c,(AE.message_wrap #i p)))
          /\ MR.m_sel h1 box_log == MM.upd (MR.m_sel h0 box_log) (n,i) (c,(AE.message_wrap #i p))
         ))
    /\ ((dishonest i)
      ==> (let k_raw = ODH.prf_odhGT sk pk in
          eq2 #AE.cipher c (SecretSpec.secretbox_easy (PlainBox.repr p) k_raw n)
          /\ modifies regions_modified_beforenm_dishonest h0 h1))
    /\ (dishonest i ==> eq #AE.cipher c CryptoSpec.cryptobox (PlainBox.repr p) n (ODH.pk_get_share pk) (ODH.get_skeyGT sk))
    // Making unfresh just i, together with the log invariant proves that we only add one entry to the
    // box_key_log. Arguing the same thing directly directly via the log itself is difficult, as we have
    // no means of getting hold of the (random) key other than pulling it from the log itself.
  ))


#set-options "--z3rlimit 300 --max_ifuel 0 --max_fuel 0"
let box pk sk n p =
  let i = generate_ae_id (DH_id (ODH.pk_get_share pk)) (DH_id (ODH.sk_get_share sk)) in
  lemma_honest_or_dishonest i;
  let k = box_beforenm pk sk in
  let c = box_afternm k n p in
  c


val box_open_afternm: n:AE.nonce -> k:AE.key -> c:AE.cipher{Seq.length c >= 16 /\ (Seq.length c - 16) / Spec.Salsa20.blocklen < pow2 32} -> ST(option (p:protected_pkae_plain (AE.get_index k)))
  (requires (fun h0 ->
    let i = AE.get_index k in
    registered i
    // Liveness of global logs
    /\ (honest i ==> MM.defined box_key_log i h0)
    // Make sure that log_invariant holds.
    /\ log_invariant h0 i
  ))
  (ensures (fun h0 p h1 ->
    let i = AE.get_index k in
    let k_raw = AE.get_keyGT k in
    log_invariant h1 i
    /\ ((~(b2t pkae_int_ctxt) \/ dishonest i)
      ==> ((Some? (SecretSpec.secretbox_open_easy c k_raw n)
        ==> (Some? p /\ Some?.v p == coerce #i (Some?.v (SecretSpec.secretbox_open_easy c k_raw n))
          /\ h0 == h1)))
        /\ ((None? (SecretSpec.secretbox_open_easy c k_raw n))
          ==> (None? p)))
    /\ ((b2t pkae_int_ctxt /\ honest i)
      ==> ((Some? p)
        ==> (let p' = AE.message_wrap (Some?.v p) in
          MM.defined box_log (n,i) h0 /\ (fst (MM.value box_log (n,i) h0) == c )
          /\ p' == snd (MM.value box_log (n,i) h0)))
        /\ ((None? p)
          ==>(MM.fresh box_log (n,i) h0 \/ c =!= fst (MM.value box_log (n,i) h0)))
      )
    /\ h0 == h1
  ))


#set-options "--z3rlimit 300 --max_ifuel 1 --max_fuel 0"
let box_open_afternm n k c =
  let i = AE.get_index k in
  match AE.decrypt #i n k c with
  | Some p ->
    let p' = (AE.message_unwrap #i p) in
    Some p'
  | None -> None


val box_open: n:AE.nonce ->
        sk:pkae_skey ->
        pk:pkae_pkey ->
        c:AE.cipher{Seq.length c >= 16 /\ (Seq.length c - 16) / Spec.Salsa20.blocklen < pow2 32} ->
        ST(option (p:protected_pkae_plain (generate_ae_id (DH_id (ODH.pk_get_share pk)) (DH_id (ODH.sk_get_share sk)))))
  (requires (fun h0 ->
    let i = generate_ae_id (DH_id (ODH.pk_get_share pk)) (DH_id (ODH.sk_get_share sk)) in
    registered i
    /\ (honest i \/ dishonest i)
    // Liveness of global logs
    /\ ((honest i) ==> MM.fresh box_log (n,i) h0)
    // Make sure that log_invariant holds.
    /\ log_invariant h0 i
  ))
  (ensures (fun h0 p h1 ->
    let i = generate_ae_id (DH_id (ODH.pk_get_share pk)) (DH_id (ODH.sk_get_share sk)) in
    let regions_modified_dishonest = Set.singleton id_log_region in
    let regions_modified_honest = Set.union regions_modified_dishonest (Set.union (Set.singleton ODH.dh_key_log_region) (Set.singleton box_key_log_region)) in
    ((honest i /\ MM.fresh box_key_log i h0) ==> (makes_unfresh_just i h0 h1
                                                  /\ modifies regions_modified_honest h0 h1))
    /\ ((honest i /\ MM.defined box_key_log i h0) ==> (MR.m_sel h0 box_key_log == MR.m_sel h1 box_key_log
                                                   /\ h0==h1))
    /\ ~(fresh i h1)
    /\ log_invariant h1 i
    /\ ((honest i)
      ==> (let k_raw = AE.get_keyGT (MM.value box_key_log i h1) in
          (~(b2t pkae_int_ctxt)
          ==> ((Some? (SecretSpec.secretbox_open_easy c k_raw n)
              ==> (Some? p /\ Some?.v p == coerce #i (Some?.v (SecretSpec.secretbox_open_easy c k_raw n))))
              /\ ((None? (SecretSpec.secretbox_open_easy c k_raw n))
                ==> (None? p))))
          /\ ((b2t pkae_int_ctxt)
            ==> (((Some? p)
                ==> (let p' = AE.message_wrap (Some?.v p) in
                    MM.defined box_log (n,i) h0 /\ (fst (MM.value box_log (n,i) h0) == c )
                    /\ p' == snd (MM.value box_log (n,i) h0)))
                /\ ((None? p)
                  ==>(MM.fresh box_log (n,i) h0 \/ c =!= fst (MM.value box_log (n,i) h0))))
         )))
    /\ ((dishonest i)
      ==> (let k_raw = ODH.prf_odhGT sk pk in
         (Some? (SecretSpec.secretbox_open_easy c k_raw n)
           ==> (Some? p /\ Some?.v p == coerce #i (Some?.v (SecretSpec.secretbox_open_easy c k_raw n))))
         /\ (None? (SecretSpec.secretbox_open_easy c k_raw n)
           ==> None? p)
         /\ modifies regions_modified_dishonest h0 h1))
  ))

let box_open n sk pk c =
  let k = box_beforenm pk sk in
  box_open_afternm n k c
