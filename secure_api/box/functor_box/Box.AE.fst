(**
   Box.AE provides cryptographically verified authenticated encryption for use by Box.PKAE. Plaintext types and functions
   to create new plaintext or break the plaintext down to bytes are provided in PlainAE. Some functions and variables are
   only present for purposes of modelling the cryptographic AE game. Of interest for other modules that are not concerned
   with cryptographic verification are coerce_key, leak_key, keygen, encrypt and decrpyt.
*)
module Box.AE

open FStar.Set
open FStar.HyperHeap
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Monotonic.RRef

open Crypto.Symmetric.Bytes

open Box.Flags
open Box.Plain
open Box.Indexing
open Box.Key

module MR = FStar.Monotonic.RRef
module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module MM = MonotoneMap
module SPEC = Spec.SecretBox
module Plain = Box.Plain
module Key = Box.Key
module ID = Box.Indexing

let noncesize = SPEC.noncelen
let keysize = SPEC.keylen
type aes_key = SPEC.key
type bytes = SPEC.bytes
type cipher = b:bytes{Seq.length b >= 16 /\ (Seq.length b - 16) / Spec.Salsa20.blocklen < pow2 32}
type nonce = SPEC.nonce

val create_zero_bytes: n:nat -> Tot (b:bytes{Seq.length b = n})
let create_zero_bytes n =
  Seq.create n (UInt8.uint_to_t 0)

type log_region (im:index_module) =
  r:MR.rid{disjoint r (ID.get_rgn im)}

(**
   The unprotected plaintext type.
*)
type ae_plain = b:bytes{Seq.length b / Spec.Salsa20.blocklen < pow2 32}

type ae_protected_plain (im:index_module) (pm:plain_module) (i:id im) = m:Plain.protected_plain_t im (get_plain pm) i

(**
  A helper function to obtain the length of a protected plaintext.
*)
let length (b:bytes) = Seq.length b

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// The following functions belong to the formal KEY module in the model.
//////////////////////////////////////////////////////////////////////////////////////////////////////////////

(**
   The key type is abstract and can only be accessed via the leak and coerce_key functions. This means that the adversary has no means
   of accessing the raw representation of any honest AE key if AE is idealized.
*)
abstract type key (im:index_module) = Key.key_t2 im
//  | Key: i:id im -> rgn:log_region im -> log:message_log im rgn pm -> raw:aes_key -> key im pm

val convert_key: #im:index_module -> k:key im -> GTot (Key.key_t2 im)
let convert_key #im k =
  k


val get_index: #im:index_module -> k:key im -> i:id im{i = k.i}
let get_index #im k =
  k.i

(**
  Similar to the leak_key function, get_keyGT provides access to the raw representation of an AE key.
  However, note that the GTot effect only allows use in type refinements and is erased upon extraction.
*)
val get_keyGT: #im:index_module -> k:key im -> GTot (b:aes_key{k.raw=b})
let get_keyGT #im k =
  k.raw

type key_log_key (im:index_module) = i:id im
type key_log_value (im:index_module) = (key im)
let key_log_range (im:index_module) = fun (k:key_log_key im) -> (v:key_log_value im{v.i = k})
let key_log_inv (im:index_module) (f:MM.map' (key_log_key im) (key_log_range im)) = True

type key_log_t (im:index_module) (rgn:log_region im) = MM.t rgn (key_log_key im) (key_log_range im) (key_log_inv im)


type message_log_key (im:index_module) = (nonce*(i:id im))
type message_log_value (im:index_module) (pm:plain_module) (i:id im) = (cipher*protected_plain_t im (get_plain pm) i)
let message_log_range (im:index_module) (pm:plain_module) = fun (k:message_log_key im) -> (message_log_value im pm (snd k))
let message_log_inv (im:index_module) (pm:plain_module) (f:MM.map' (message_log_key im) (message_log_range im pm)) = True

type message_log (im:index_module) (rgn:log_region im) (pm:plain_module) =
  MM.t rgn (message_log_key im) (message_log_range im pm) (message_log_inv im pm)

abstract noeq type ae_module (im:index_module) (pm:plain_module) =
  | AM :
    key_log_region: log_region im ->
    message_log_region: (rgn:log_region im{disjoint rgn key_log_region}) ->
    key_log: (key_log_t im key_log_region) ->
    message_log: (message_log im message_log_region pm) ->
    ae_module im pm

let create im pm (klr:log_region im) message_log_region key_log =
  AM klr message_log_region key_log


//val nonce_is_fresh: #im:index_module -> #pm:plain_module -> am:ae_module im pm -> i:id im -> n:nonce -> h:mem -> t:Type0{t <==> MM.fresh am.message_log (n,i) h}
abstract let nonce_is_fresh (#im:index_module) (#pm:plain_module) (am:ae_module im pm) (i:id im) (n:nonce) (h:mem) =
  MR.m_contains am.message_log h
  /\ MM.fresh am.message_log (n,i) h

abstract let log_freshness_invariant (#im:index_module) (#pm:plain_module) (am:ae_module im pm) (h:mem) =
  MR.m_contains (get_log im) h
  /\ MR.m_contains am.message_log h
  /\ (forall i n . ID.fresh im (ID i) h ==> MM.fresh am.message_log (n,i) h)


(**
   This function generates a fresh random key. Honest, as well as dishonest ids can be created using keygen. However, note that the adversary can
   only access the raw representation of dishonest keys. The log is created in a fresh region below the ae_key_region.
*)
#set-options "--z3rlimit 2000 --max_ifuel 1 --max_fuel 0"
val gen: #im:index_module -> #pm:plain_module -> am:ae_module im pm -> i:id im -> ST (k:key im{get_index k=i})
  (requires (fun h0 ->
    (fresh im (ID i) h0 \/ honest im (ID i))
    /\ log_freshness_invariant #im #pm am h0
    ///\ (forall (i:id im) (n:nonce) . ID.fresh im (ID i) h0 ==> MM.fresh am.message_log (n,i) h0)
  ))
  (ensures  (fun h0 k h1 ->
    (MM.fresh am.key_log i h0 ==>
              (modifies (Set.singleton am.key_log_region) h0 h1
              /\ MR.m_sel h1 am.key_log == MM.upd (MR.m_sel h0 am.key_log) i k))
    /\ (MM.defined am.key_log i h0 ==> modifies Set.empty h0 h1)
    /\ log_freshness_invariant #im #pm am h1
    ///\ (forall (i:id im) (n:nonce) . ID.fresh im (ID i) h1 ==> MM.fresh am.message_log (n,i) h1)
  ))

let gen #im #pm am i =
  match MM.lookup am.key_log i with
  | Some k -> k
  | None ->
    let rnd_k = random_bytes (UInt32.uint_to_t keysize) in
    let k:key im = Key i rnd_k in
    recall_log im;
    MR.m_recall am.message_log;
    MR.m_recall am.key_log;
    MM.extend am.key_log i k;
    k

(**
   The coerce function transforms a raw aes_key into an abstract key. Only dishonest ids can be used
   with this function.
*)
#set-options "--z3rlimit 500 --max_ifuel 1 --max_fuel 1"
val coerce: #im:index_module -> i:id im{dishonest im (ID i)} -> raw_k:aes_key -> (k:key im{get_index k=i /\ get_keyGT k = raw_k})
let coerce #im i raw_k =
  Key i raw_k

(**
   The leak_key function transforms an abstract key into a raw aes_key.
   The refinement type on the key makes sure that no honest keys can be leaked.
*)
val leak: #im:index_module -> k:key im{dishonest im (ID (get_index k))} -> Tot (raw_k:aes_key{raw_k=get_keyGT k})
let leak #im k =
  k.raw


let km (#im:ID.index_module) (#pm:plain_module) (am:ae_module im pm) = Key.create im (get_index) (get_keyGT) (log_freshness_invariant am) (gen am) (coerce) (leak)

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// The following functions belong to the formal AE module in the model.
//////////////////////////////////////////////////////////////////////////////////////////////////////////////

#reset-options
#set-options "--z3rlimit 400 --max_ifuel 0 --max_fuel 0"
(**
   Encrypt a a message under a key. Idealize if the key is honest and ae_ind_cca true.
*)
val encrypt: #im:index_module -> #pm:plain_module{get_plain pm == ae_plain} -> am:ae_module im pm -> #(i:id im) -> n:nonce -> k:key im{get_index k=i} -> m:ae_protected_plain im pm i{Plain.length #im #pm #i m / Spec.Salsa20.blocklen < pow2 32} -> ST cipher
  (requires (fun h0 ->
    registered im (ID i)
    /\ ((honest im (ID i)) ==>
               (nonce_is_fresh #im #pm am i n h0)) // Nonce freshness
    /\ log_freshness_invariant #im #pm am h0
  ))
  (ensures  (fun h0 c h1 ->
    let modified_regions_fresh = Set.union (Set.singleton am.message_log_region) (Set.singleton (ID.get_rgn im)) in
    let modified_regions_honest = Set.singleton am.message_log_region in
    registered im (ID i)
    /\ (dishonest im (ID i) ==> h0 == h1)
    /\ ((honest im (ID i) /\ b2t ae_ind_cpa)
        ==> (c = SPEC.secretbox_easy (create_zero_bytes (Plain.length #im #pm #i m)) (get_keyGT k) n))
    /\ ((dishonest im (ID i) \/ ~(b2t ae_ind_cpa))
        ==> (eq2 #cipher c (SPEC.secretbox_easy (Plain.repr #im #pm #i m) (get_keyGT k) n)))
    /\ ((honest im (ID i)) ==>
                      (MR.m_contains am.message_log h1
                      /\ MR.witnessed (MM.contains am.message_log (n,i) (c,m))
                      /\ MR.m_sel h1 am.message_log == MM.upd (MR.m_sel h0 am.message_log) (n,i) (c,m)))
    /\ log_freshness_invariant #im #pm am h1
  ))

#set-options "--z3rlimit 900 --max_ifuel 1 --max_fuel 0"
let encrypt #im #pm am #i n k m =
  MR.m_recall am.message_log;
  recall_log im;
  lemma_registered_not_fresh im (ID i);
  lemma_honest_or_dishonest im (ID i);
  let h = get_reg_honesty im (ID i) in
  let ideal =
    match h with
    | HONEST -> ae_ind_cpa
    | DISHONEST ->
      false
  in
  let p =
    if ideal then (
      Seq.create (Plain.length #im #pm #i m) (UInt8.uint_to_t 0)
    ) else (
      Plain.repr #im #pm #i m)
  in
  let  c = SPEC.secretbox_easy p k.raw n in
  if HONEST? h then (
    MR.m_recall am.message_log;
    recall_log im;
    MM.extend am.message_log (n,i) (c,m)
    );
  c


(**
   Decrypt a ciphertext c using a key k. If the key is honest and ae_int_ctxt is idealized,
   try to obtain the ciphertext from the log. Else decrypt via concrete implementation.
*)
val decrypt: #im:index_module -> #pm:plain_module{get_plain pm == ae_plain} -> am:ae_module im pm -> #(i:id im) -> n:nonce -> k:key im{get_index k=i} -> c:cipher -> ST (option (ae_protected_plain im pm i))
  (requires (fun h0 ->
    registered im (ID i) // No in-between states of keys (i.e.) where one of the shares is fresh and one is registerd
    /\ log_freshness_invariant #im #pm am h0
  ))
  (ensures  (fun h0 p h1 ->
    let modified_regions_honest = Set.singleton am.message_log_region in
    registered im (ID i)
    /\ h0 == h1
    /\ ((~(b2t ae_int_ctxt) \/ dishonest im (ID i))
      ==> ((Some? (SPEC.secretbox_open_easy c (get_keyGT k) n)
        ==> Some? p /\ Some?.v p == Plain.coerce #im #pm #i (Some?.v (SPEC.secretbox_open_easy c (get_keyGT k) n)))
  /\ ((None? (SPEC.secretbox_open_easy c (get_keyGT k) n))
    ==> None? p)
      ))
    /\ ((b2t ae_int_ctxt /\ honest im (ID i))
        ==> (Some? p
          ==> (MM.defined am.message_log (n,i) h0 /\ (fst (MM.value am.message_log (n,i) h0) == c )
            /\ Some?.v p == snd (MM.value am.message_log (n,i) h0)))
    /\ (None? p
    ==> (MM.fresh am.message_log (n,i) h0 \/ c =!= fst (MM.value am.message_log (n,i) h0)))
   )
   /\ log_freshness_invariant #im #pm am h1
  ))


#set-options "--z3rlimit 1900 --max_ifuel 1 --max_fuel 0"
let decrypt #im #pm am #i n k c =
  MR.m_recall am.message_log;
  recall_log im;
  lemma_registered_not_fresh im (ID i);
  lemma_honest_or_dishonest im (ID i);
  let h = get_reg_honesty im (ID i) in
  let ideal =
    match h with
    | HONEST -> ae_int_ctxt
    | DISHONEST ->
      false
  in
  MR.m_recall am.message_log;
  recall_log im;
  if ideal then
    match MM.lookup am.message_log (n,i) with
    | Some (c',m') ->
      if c' = c then
        Some m'
      else
        None
    | None -> None
  else
    let p = (SPEC.secretbox_open_easy c k.raw n) in
    match p with
    | Some p' ->
      Some (Plain.coerce #im #pm #i p')
    | None -> None
