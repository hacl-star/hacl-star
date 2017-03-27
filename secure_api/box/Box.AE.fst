(**
   Box.AE provides cryptographically verified authenticated encryption for use by Box.PKAE. Plaintext types and functions
   to create new plaintext or break the plaintext down to bytes are provided in PlainAE. Some functions and variables are
   only present for purposes of modelling the cryptographic AE game. Of interest for other modules that are not concerned
   with cryptographic verification are coerce_key, encrypt and decrpyt.
*)
module Box.AE

open FStar.Set
open FStar.HyperStack
open FStar.HyperHeap
open FStar.Monotonic.RRef
open FStar.Endianness

open Crypto.Symmetric.Bytes

open Box.Flags
open Box.Indexing

module MR = FStar.Monotonic.RRef
module HH = FStar.HyperHeap
module MM = MonotoneMap
module SPEC = Spec.SecretBox

open Box.PlainAE

#set-options "--z3rlimit 100 --lax"
// TODO: implement an init function for all the global state.
type noncesize = SPEC.noncelen
type keysize = SPEC.keylen
type aes_key = SPEC.key 
type bytes = SPEC.bytes
type cipher = b:bytes
type nonce = SPEC.nonce

val create_zero_bytes: n:nat -> Tot (b:bytes{Seq.length b = n})
let create_zero_bytes n =
  Seq.create n (UInt8.uint_to_t 0)

assume val ae_key_region: (r:MR.rid{ extends r root 
				     /\ is_eternal_region r 
				     /\ is_below r root
				     /\ disjoint r id_log_region
				     /\ disjoint r id_honesty_log_region
				     })

type log_key = nonce
type log_value (i:id{AE_id? i}) = (cipher*protected_ae_plain i)
type log_range = fun (i:id{AE_id? i}) -> (fun log_key -> (log_value i))
type log_inv (i:id{AE_id? i}) (f:MM.map' log_key (log_range i)) = True

(**
   log_t is a monotone map that maps nonces to a tuple of ciphertext and plaintext. It is instantiated in the key type
   to provide the following guarantee in case the key is honest and AE is idealized:
   * Authentication: Upon encryption, the message is stored in the log, indexed by the nonce. Upon decryption, a lookup
     is performed using the nonce received and if the ciphertext in the log matches the received ciphertext, the plaintext
     is extracted from the log.
   The log will give the following guarantee regardless of the honesty of the key or the idealization of AE:
   * Nonce uniqueness: Every log can only have one entry per index. Since the nonce is used as the index in the log, a nonce
     can only be used once per key.
   
*)
type log_t (i:id{AE_id? i}) (r:rid)  = MM.t r log_key (log_range i) (log_inv i)

(**
   empty_log returns an empty monotone map of type log_t. 
*)
val empty_log: i:id{AE_id? i} -> Tot (MM.map' log_key (log_range i))
let empty_log i = MM.empty_map log_key (log_range i)

(**
   The key type is abstract and can only be accessed via the leak and coerce_key functions. This means that the adversary has no means
   of accessing the raw representation of any honest AE key if AE is idealized.
*)
noeq abstract type key =
  | Key: #i:id{AE_id? i /\ unfresh i /\ registered i} -> #(region:rid{extends region ae_key_region /\ is_below region ae_key_region /\ is_eternal_region region}) -> raw:aes_key -> log:log_t i region -> key

val get_index: k:key -> Tot (i:id{i=k.i /\ AE_id? i})
let get_index k = k.i

#set-options "--z3rlimit 25"
(**
   This function generates a fresh random key. Honest, as well as dishonest ids can be created using keygen. However, note that the adversary can
   only access the raw representation of dishonest keys. The log is created in a fresh region below the ae_key_region.
*)
val keygen: i:id{AE_id? i} -> ST (k:key{k.i=i})
  (requires (fun h -> 
    fresh i h // Prevents multiple keys with the same id
    /\ registered i // We require this to enforce a static corruption model.
  ))
  (ensures  (fun h0 k h1 -> 
    let (s:Set.set (HH.rid)) = Set.union (Set.singleton k.region) (Set.singleton id_log_region) in
    HH.modifies_just s h0.h h1.h
    /\ extends k.region ae_key_region
    /\ fresh_region k.region h0.h h1.h
    /\ is_below k.region ae_key_region
    /\ m_contains k.log h1
    /\ m_sel h1 k.log == MM.empty_map log_key (log_range k.i)
    /\ makes_unfresh_just i h0 h1
  ))
let keygen i =
  MR.m_recall id_log;
  make_unfresh i;
  let rnd_k = random_bytes (UInt32.uint_to_t keysize) in
  let region = new_region ae_key_region in
  let log = MM.alloc #region #log_key #(log_range i) #(log_inv i) in
  fresh_unfresh_contradiction i;
  Key #i #region rnd_k log

(**
   The coerce function transforms a raw aes_key into an abstract key. Only dishonest ids can be used
   with this function.
*)
val coerce_key: i:id{AE_id? i /\ (dishonest i)} -> raw_k:aes_key -> ST (k:key{k.i=i /\ k.raw = raw_k})
  (requires (fun h0 -> 
    registered i
  ))
  (ensures  (fun h0 k h1 ->
    let (s:Set.set (HH.rid)) = Set.union (Set.singleton k.region) (Set.singleton id_log_region) in
    HH.modifies_just s h0.h h1.h
    /\ extends k.region ae_key_region
    /\ fresh_region k.region h0.h h1.h
    /\ is_below k.region ae_key_region
    /\ m_contains k.log h1
    /\ m_sel h1 k.log == MM.empty_map log_key (log_range k.i)
    /\ registered i
    /\ makes_unfresh_just i h0 h1
    /\ dishonest i
  ))
let coerce_key i raw = 
  make_unfresh i;
  let region = new_region ae_key_region in
  let log = MM.alloc #region #log_key #(log_range i) #(log_inv i) in
  fresh_unfresh_contradiction i;
  Key #i #region raw log

(**
   The message wrap- and unwrap functions are provided here for use in the PKAE module.
*)
let message_wrap #i = PlainAE.ae_message_wrap #i
let message_unwrap #i = PlainAE.ae_message_unwrap #i

(**
   The leak_key function transforms an abstract key into a raw aes_key.
   The refinement type on the key makes sure that no honest keys can be leaked.
*)
val leak_key: k:key{(dishonest k.i) \/ ~(b2t ae_ind_cca)} -> Tot (raw_k:aes_key{raw_k=k.raw})
let leak_key k =
  k.raw

(**
   Similar to the leak_key function, get_keyGT provides access to the raw representation of an AE key.
   However, note that the GTot effect only allows use in type refinements and is erased upon extraction.
*)
val get_keyGT: k:key -> GTot (raw_k:aes_key{raw_k=k.raw})
let get_keyGT k =
  k.raw
(**
   The get_logGT function provides direct access to the log of a key. Note that its GTot effect allows
   use on type-level only and means that the function will be erased upon extraction.
*)
val get_logGT: k:key -> GTot (log:log_t k.i k.region{log=k.log})
let get_logGT k =
  k.log

(**
   recall_log allows proving liveness of the log of a key.
*)
val recall_log: k:key -> ST unit
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 ->
    h0 == h1
    /\ MR.m_contains k.log h1
  ))
let recall_log k =
  MR.m_recall k.log

val get_regionGT: k:key -> GTot (region:rid{region=k.region})
let get_regionGT k =
  k.region


(**
   Encrypt a a message under a key. Idealize if the key is honest and ae_ind_cca true.
*)
#reset-options
#set-options "--z3rlimit 100 --initial_fuel 10 --initial_ifuel 10"
val encrypt: #(i:id{AE_id? i}) -> n:nonce -> k:key{k.i=i} -> (m:protected_ae_plain i) -> ST cipher
  (requires (fun h0 -> 
    ((honest i) ==> MM.fresh k.log n h0) // Nonce freshness
    /\ MR.m_contains k.log h0
    /\ registered i
  ))
  (ensures  (fun h0 c h1 ->
    let current_log = MR.m_sel h0 k.log in
    modifies_one k.region h0.h h1.h
    /\ m_contains k.log h1
    /\ ((honest i /\ b2t ae_ind_cpa)
      ==> (c = SPEC.secretbox_easy (create_zero_bytes (length m)) k.raw n))
    /\ ((dishonest i \/ ~(b2t ae_ind_cpa))
      ==> (c = SPEC.secretbox_easy (repr m) k.raw n))
    /\ (dishonest i \/ honest i)
    /\ MR.m_sel h1 k.log == MM.upd current_log n (c,m)
    /\ MR.witnessed (MM.contains k.log n (c,m))
    ))
let encrypt #i n k m =
  MR.m_recall id_log;
  MR.m_recall id_honesty_log;
  recall_log k;
  let honest_i = is_honest i in
  let p = 
    if (ae_ind_cpa && honest_i) then (
      Seq.create (length m) (UInt8.uint_to_t 0)
    ) else (
      repr m )
  in
  let  c = SPEC.secretbox_easy p k.raw n in
  if honest_i then (
    MM.extend k.log n (c,m));
  c


#reset-options
#set-options "--z3rlimit 100"
(**
   Decrypt a ciphertext c using a key k. If the key is honest and ae_int_ctxt is idealized,
   try to obtain the ciphertext from the log. Else decrypt via concrete implementation.
*)
val decrypt: #(i:id{AE_id? i}) -> n:nonce -> k:key{k.i=i} -> c:cipher{Seq.length c >= 16 /\ (Seq.length c - 16) / Spec.Salsa20.blocklen < pow2 32} -> ST (option (protected_ae_plain i))
  (requires (fun h -> 
    Map.contains h.h k.region
    /\ MR.m_contains k.log h
    /\ registered i
  ))
  (ensures  (fun h0 p h1 -> 
    modifies_none h0 h1
    /\ m_contains k.log h1
    /\ ((~(b2t ae_int_ctxt) \/ dishonest i)
      ==> (Some? (SPEC.secretbox_open_easy c k.raw n)
        ==> Some? p /\ Some?.v p == coerce (Some?.v (SPEC.secretbox_open_easy c k.raw n))))
    /\ (( (b2t ae_int_ctxt) /\ honest i /\ Some? p) 
      ==> (MM.defined k.log n h0 /\ (fst (MM.value k.log n h0) == c ) 
         /\ Some?.v p == snd (MM.value k.log n h0)))
  ))
let decrypt #i n k c =
  let honest_i = is_honest i in
  if ae_int_ctxt && honest_i then
    match MM.lookup k.log n with
    | Some (c',m') -> 
      if c' = c then 
	Some m'
      else 
	None
    | None -> None
  else 
    let p = (SPEC.secretbox_open_easy c k.raw n) in
    match p with
    | Some p' -> Some (PlainAE.coerce #i p')
    | None -> None
