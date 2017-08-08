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

module MR = FStar.Monotonic.RRef
module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module MM = MonotoneMap
module SPEC = Spec.SecretBox


let noncesize = SPEC.noncelen
let keysize = SPEC.keylen
type aes_key = SPEC.key
type bytes = SPEC.bytes
type cipher = b:bytes{Seq.length b >= 16 /\ (Seq.length b - 16) / Spec.Salsa20.blocklen < pow2 32}
type nonce = SPEC.nonce

val create_zero_bytes: n:nat -> Tot (b:bytes{Seq.length b = n})
let create_zero_bytes n =
  Seq.create n (UInt8.uint_to_t 0)

type ae_log_region (im:index_module) =
  r:MR.rid{disjoint r (get_rgn im)}

type ae_log_key (im:index_module) = (nonce*(i:id im))
type ae_log_value (im:index_module) (pm:plain_module) (i:id im) = (cipher*protected_plain_t im (get_plain pm) i)
let ae_log_range (im:index_module) (pm:plain_module) = fun (k:ae_log_key im) -> (ae_log_value im pm (snd k))
let ae_log_inv (im:index_module) (pm:plain_module) (f:MM.map' (ae_log_key im) (ae_log_range im pm)) = True

type ae_log (im:index_module) (rgn:ae_log_region im) (pm:plain_module) =
  MM.t rgn (ae_log_key im) (ae_log_range im pm) (ae_log_inv im pm)

(**
   The unprotected plaintext type.
*)
type ae_plain = b:bytes{Seq.length b / Spec.Salsa20.blocklen < pow2 32}

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
noeq abstract type key (im:index_module) (pm:plain_module) =
  | Key: i:id im -> rgn:ae_log_region im -> log:ae_log im rgn pm -> raw:aes_key -> key im pm

(**
   This function generates a fresh random key. Honest, as well as dishonest ids can be created using keygen. However, note that the adversary can
   only access the raw representation of dishonest keys. The log is created in a fresh region below the ae_key_region.
*)
#set-options "--z3rlimit 300 --max_ifuel 0 --max_fuel 0"
val gen: #im:index_module -> #pm:plain_module -> i:id im -> rgn:ae_log_region im -> ST (k:key im pm{k.i=i})
  (requires (fun h0 ->
    fresh im (ID i) h0 \/ honest im (ID i)
  ))
  (ensures  (fun h0 k h1 ->
    let modified_regions = (Set.singleton rgn) in
    modifies modified_regions h0 h1
  ))
let gen #im #pm i rgn =
  let rnd_k = random_bytes (UInt32.uint_to_t keysize) in
  let key_region = new_region rgn in
  let key_log = MM.alloc #key_region #(ae_log_key im) #(ae_log_range im pm) #(ae_log_inv im pm) in
  Key i key_region key_log rnd_k


(**
   The coerce function transforms a raw aes_key into an abstract key. Only dishonest ids can be used
   with this function.
*)
#set-options "--z3rlimit 500 --max_ifuel 1 --max_fuel 1"
val coerce: #im:index_module -> #pm:plain_module -> i:id im -> rgn:ae_log_region im -> raw_k:aes_key -> ST (k:key im pm{k.i=i /\ k.raw = raw_k})
  (requires (fun h0 ->
    dishonest im (ID i)
    \/ fresh im (ID i) h0
  ))
  (ensures  (fun h0 k h1 ->
    let modified_regions = Set.union (Set.singleton (get_rgn im)) (Set.singleton rgn) in
    let (i1,i2) = i in
    ((~(fresh im (SUBID i1) h0) /\ ~(fresh im (SUBID i2) h0)) ==> modifies (Set.singleton rgn) h0 h1)
    /\ (fresh im (SUBID i1) h0 /\ ~(fresh im (SUBID i2) h0) ==> MR.m_sel h1 (get_log im) == MM.upd (MR.m_sel h0 (get_log im)) i1 false /\ modifies modified_regions h0 h1)
    /\ (fresh im (SUBID i2) h0 /\ ~(fresh im (SUBID i1) h0) ==> MR.m_sel h1 (get_log im) == MM.upd (MR.m_sel h0 (get_log im)) i2 false /\ modifies modified_regions h0 h1)
    /\ (fresh im (SUBID i1) h0 /\ fresh im (SUBID i2) h0 ==> MR.m_sel h1 (get_log im) == MM.upd (MM.upd (MR.m_sel h0 (get_log im)) i1 false) i2 false /\ modifies modified_regions h0 h1)
  ))
let coerce #im #pm i rgn raw_k =
  recall_log im;
  make_dishonest im (ID i);
  let key_region = new_region rgn in
  let key_log = MM.alloc #key_region #(ae_log_key im) #(ae_log_range im pm) #(ae_log_inv im pm) in
  Key i key_region key_log raw_k

(**
   The leak_key function transforms an abstract key into a raw aes_key.
   The refinement type on the key makes sure that no honest keys can be leaked.
*)
val leak: #im:index_module -> #pm:plain_module -> k:key im pm{(dishonest im (ID k.i)) \/ ~(b2t ae_ind_cca)} -> Tot (raw_k:aes_key{raw_k=k.raw})
let leak #im #pm k =
  k.raw

(**
   Similar to the leak_key function, get_keyGT provides access to the raw representation of an AE key.
   However, note that the GTot effect only allows use in type refinements and is erased upon extraction.
*)
val get_keyGT: #im:index_module -> #pm:plain_module -> k:key im pm -> GTot (raw_k:aes_key{raw_k=k.raw})
let get_keyGT #im #pm k =
  k.raw

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// The following functions belong to the formal AE module in the model.
//////////////////////////////////////////////////////////////////////////////////////////////////////////////

#reset-options
#set-options "--z3rlimit 400 --max_ifuel 0 --max_fuel 0"
(**
   Encrypt a a message under a key. Idealize if the key is honest and ae_ind_cca true.
*)
val encrypt: #im:index_module -> #pm:plain_module{get_plain pm == ae_plain} -> #(i:id im) -> n:nonce -> k:key im pm{k.i=i} -> (m:Plain.protected_plain_t im (get_plain pm) i{Plain.length #im #pm #i m / Spec.Salsa20.blocklen < pow2 32}) -> ST cipher
  (requires (fun h0 ->
    (fresh im (ID i) h0 \/ registered im (ID i)) // No in-between states of keys (i.e.) where one of the shares is fresh and one is registerd
    /\ ((honest im (ID i)) ==>
               (MR.m_contains k.log h0
               /\ MM.fresh k.log (n,i) h0)) // Nonce freshness
    /\ (fresh im (ID i) h0 ==>
             (m_sel h0 k.log == MM.empty_map (ae_log_key im) (ae_log_range im pm))) // If the key is fresh, so has to be its log.
  ))
  (ensures  (fun h0 c h1 ->
    let modified_regions_fresh = Set.union (Set.singleton k.rgn) (Set.singleton (get_rgn im)) in
    let modified_regions_honest = Set.singleton k.rgn in
    registered im (ID i)
    /\ (fresh im (ID i) h0 ==>
                       (let (i1,i2) = i in
                       honest im (ID i)
                       /\ MR.m_contains (get_log im) h1
                       /\ (MR.m_sel h1 (get_log im) == MM.upd (MM.upd (MR.m_sel h0 (get_log im)) i1 true) i2 true /\ modifies modified_regions_fresh h0 h1)))
    /\ ((~(fresh im (ID i) h0) /\ honest im (ID i)) ==> HS.modifies modified_regions_honest h0 h1)
    /\ (dishonest im (ID i) ==> h0 == h1)
    /\ ((honest im (ID i) /\ b2t ae_ind_cpa)
        ==> (c = SPEC.secretbox_easy (create_zero_bytes (Plain.length #im #pm #i m)) k.raw n))
    /\ ((dishonest im (ID i) \/ ~(b2t ae_ind_cpa))
        ==> (eq2 #cipher c (SPEC.secretbox_easy (Plain.repr #im #pm #i m) k.raw n)))
    /\ ((honest im (ID i)) ==>
                      (MR.m_contains k.log h1
                      /\ MR.witnessed (MM.contains k.log (n,i) (c,m))
                      /\ MR.m_sel h1 k.log == MM.upd (MR.m_sel h0 k.log) (n,i) (c,m)))
  ))

#set-options "--z3rlimit 400 --max_ifuel 1 --max_fuel 0"
let encrypt #im #pm #i n k m =
  MR.m_recall k.log;
  recall_log im;
  if is_fresh im (ID i) then (
    make_honest im (ID i)
  );
  recall_log im;
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
    MR.m_recall k.log;
    recall_log im;
    MM.extend k.log (n,i) (c,m)
    );
  c


(**
   Decrypt a ciphertext c using a key k. If the key is honest and ae_int_ctxt is idealized,
   try to obtain the ciphertext from the log. Else decrypt via concrete implementation.
*)

val decrypt: #im:index_module -> #pm:plain_module{get_plain pm == ae_plain} -> #(i:id im) -> n:nonce -> k:key im pm{k.i=i} -> c:cipher -> ST (option (m:Plain.protected_plain_t im (get_plain pm) i))
  (requires (fun h0 ->
    (fresh im (ID i) h0 \/ registered im (ID i)) // No in-between states of keys (i.e.) where one of the shares is fresh and one is registerd
    /\ (fresh im (ID i) h0 ==>
             (m_sel h0 k.log == MM.empty_map (ae_log_key im) (ae_log_range im pm))) // If the key is fresh, so has to be its log.
  ))
  (ensures  (fun h0 p h1 ->
    let modified_regions_fresh = Set.union (Set.singleton k.rgn) (Set.singleton (get_rgn im)) in
    let modified_regions_honest = Set.singleton k.rgn in
    registered im (ID i)
    /\ (fresh im (ID i) h0 ==>
                (let (i1,i2) = i in
                honest im (ID i)
                /\ MR.m_contains (get_log im) h1
                /\ (MR.m_sel h1 (get_log im) == MM.upd (MM.upd (MR.m_sel h0 (get_log im)) i1 true) i2 true /\ modifies modified_regions_fresh h0 h1)))
    /\ (((honest im (ID i) \/ dishonest im (ID i)) /\ ~(fresh im (ID i) h0) ) ==> h0 == h1)
    /\ ((~(b2t ae_int_ctxt) \/ dishonest im (ID i))
      ==> ((Some? (SPEC.secretbox_open_easy c k.raw n)
        ==> Some? p /\ Some?.v p == Plain.coerce #im #pm #i (Some?.v (SPEC.secretbox_open_easy c k.raw n)))
  /\ ((None? (SPEC.secretbox_open_easy c k.raw n))
    ==> None? p)
      ))
    /\ ((b2t ae_int_ctxt /\ honest im (ID i))
        ==> (Some? p
          ==> (MM.defined k.log (n,i) h0 /\ (fst (MM.value k.log (n,i) h0) == c )
            /\ Some?.v p == snd (MM.value k.log (n,i) h0)))
    /\ (None? p
    ==> (MM.fresh k.log (n,i) h0 \/ c =!= fst (MM.value k.log (n,i) h0)))
   )
  ))


let decrypt #im #pm #i n k c =
  MR.m_recall k.log;
  recall_log im;
  if is_fresh im (ID i) then (
    make_honest im (ID i)
  );
  recall_log im;
  lemma_honest_or_dishonest im (ID i);
  let h = get_reg_honesty im (ID i) in
  let ideal =
    match h with
    | HONEST -> ae_int_ctxt
    | DISHONEST ->
      false
  in
  if ideal then
    match MM.lookup k.log (n,i) with
    | Some (c',m') ->
      if c' = c then
        Some m'
      else
        None
    | None -> None
  else
    let p = (SPEC.secretbox_open_easy c k.raw n) in
    match p with
    | Some p' -> Some (Plain.coerce #im #pm #i p')
    | None -> None
