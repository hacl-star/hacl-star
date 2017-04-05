(**
   Box.AE provides cryptographically verified authenticated encryption for use by Box.PKAE. Plaintext types and functions
   to create new plaintext or break the plaintext down to bytes are provided in PlainAE. Some functions and variables are
   only present for purposes of modelling the cryptographic AE game. Of interest for other modules that are not concerned
   with cryptographic verification are coerce_key, encrypt and decrpyt.
*)
module Box.AE

open FStar.Set
open FStar.HyperHeap
open FStar.HyperStack
open FStar.Monotonic.RRef
open FStar.Endianness

open Crypto.Symmetric.Bytes

open Box.Flags
open Box.Indexing

module MR = FStar.Monotonic.RRef
module HH = FStar.HyperHeap
module HS = FStar.HyperStack
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


assume val ae_log_region: (r:MR.rid{ extends r root 
				     /\ is_eternal_region r 
				     /\ is_below r root
				     /\ disjoint r id_log_region
				     /\ disjoint r id_honesty_log_region
				     })

type ae_log_key = (nonce*(i:id{AE_id? i}))
type ae_log_value (i:id{AE_id? i}) = (cipher*protected_ae_plain i)
type ae_log_range = fun (k:ae_log_key) -> ae_log_value (snd k)
type ae_log_inv (f:MM.map' ae_log_key ae_log_range) = True


assume val ae_log: MM.t ae_log_region ae_log_key ae_log_range ae_log_inv

(**
   The key type is abstract and can only be accessed via the leak and coerce_key functions. This means that the adversary has no means
   of accessing the raw representation of any honest AE key if AE is idealized.
*)
noeq abstract type key =
  | Key: #i:id{AE_id? i /\ unfresh i /\ registered i} -> raw:aes_key -> key

val get_index: k:key -> Tot (i:id{i=k.i /\ AE_id? i})
let get_index k = k.i

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
    let (s:Set.set (HH.rid)) = Set.singleton id_log_region in
    HH.modifies_just s h0.h h1.h
    /\ makes_unfresh_just i h0 h1
  ))
let keygen i =
  MR.m_recall id_log;
  make_unfresh i;
  let rnd_k = random_bytes (UInt32.uint_to_t keysize) in
  Key #i rnd_k

(**
   The coerce function transforms a raw aes_key into an abstract key. Only dishonest ids can be used
   with this function.
*)
val coerce_key: i:id{AE_id? i /\ (dishonest i)} -> raw_k:aes_key -> ST (k:key{k.i=i /\ k.raw = raw_k})
  (requires (fun h0 -> 
    registered i
  ))
  (ensures  (fun h0 k h1 ->
    let (s:Set.set (HH.rid)) = Set.singleton id_log_region in
    HH.modifies_just s h0.h h1.h
    /\ registered i
    /\ makes_unfresh_just i h0 h1
    /\ dishonest i
  ))
let coerce_key i raw = 
  make_unfresh i;
  fresh_unfresh_contradiction i;
  Key #i raw

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


#reset-options
#set-options "--z3rlimit 100 --max_ifuel 1 --max_fuel 1"
(**
   Encrypt a a message under a key. Idealize if the key is honest and ae_ind_cca true.
*)
val encrypt: #(i:id{AE_id? i}) -> n:nonce -> k:key{k.i=i} -> (m:protected_ae_plain i) -> ST cipher
  (requires (fun h0 -> 
    MR.m_contains ae_log h0
    /\ ((honest i) ==> MM.fresh ae_log (n,i) h0) // Nonce freshness
    /\ registered i
  ))
  (ensures  (fun h0 c h1 ->
    let current_log = MR.m_sel h0 ae_log in
    let modified_regions:Set.set (r:HH.rid) = Set.singleton ae_log_region in
    (honest i ==> HS.modifies modified_regions h0 h1)
    /\ m_contains ae_log h1
    /\ ((honest i /\ b2t ae_ind_cpa)
      ==> (c = SPEC.secretbox_easy (create_zero_bytes (length m)) k.raw n))
    /\ ((~(b2t ae_ind_cpa) \/ dishonest i)
      ==> (c = SPEC.secretbox_easy (repr m) k.raw n))
    /\ (dishonest i \/ honest i)
    /\ ((honest i) ==> (MR.witnessed (MM.contains ae_log (n,i) (c,m))
                                /\ MR.m_sel h1 ae_log == MM.upd current_log (n,i) (c,m)))
    /\ ((dishonest i) ==> h0 == h1)
    /\ (modifies modified_regions h0 h1 \/ h0 == h1)
  ))
let encrypt #i n k m =
  MR.m_recall id_log;
  MR.m_recall id_honesty_log;
  MR.m_recall ae_log;
  let honest_i = is_honest i in
  //let p = 
  //  if (ae_ind_cpa && honest_i) then (
  //    Seq.create (length m) (UInt8.uint_to_t 0)
  //  ) else (
  //    assert(~(b2t ae_ind_cpa) \/ dishonest i);
  //    repr m )
  //in
  //let  c = SPEC.secretbox_easy p k.raw n in
  let c = 
    if (ae_ind_cpa && honest_i) then (
      let c' = SPEC.secretbox_easy (Seq.create (length m) (UInt8.uint_to_t 0)) k.raw n in
      c'
    ) else (
      let c' = SPEC.secretbox_easy (repr m) k.raw n in
      c'
    )
  in
  if honest_i then (
    MM.extend ae_log (n,i) (c,m));
  c


#reset-options
#set-options "--z3rlimit 100"
(**
   Decrypt a ciphertext c using a key k. If the key is honest and ae_int_ctxt is idealized,
   try to obtain the ciphertext from the log. Else decrypt via concrete implementation.
*)
val decrypt: #(i:id{AE_id? i}) -> n:nonce -> k:key{k.i=i} -> c:cipher{Seq.length c >= 16 /\ (Seq.length c - 16) / Spec.Salsa20.blocklen < pow2 32} -> ST (option (protected_ae_plain i))
  (requires (fun h -> 
    MR.m_contains ae_log h
    /\ registered i
  ))
  (ensures  (fun h0 p h1 -> 
    h0 == h1
    /\ m_contains ae_log h1
    /\ ((~(b2t ae_int_ctxt) \/ dishonest i)
      ==> ((Some? (SPEC.secretbox_open_easy c k.raw n)
        ==> Some? p /\ Some?.v p == coerce (Some?.v (SPEC.secretbox_open_easy c k.raw n)))
	/\ ((None? (SPEC.secretbox_open_easy c k.raw n))
	  ==> None? p)
      ))
    /\ ((b2t ae_int_ctxt /\ honest i)
        ==> (Some? p
          ==> (MM.defined ae_log (n,i) h0 /\ (fst (MM.value ae_log (n,i) h0) == c ) 
            /\ Some?.v p == snd (MM.value ae_log (n,i) h0)))
	  /\ (None? p
	  ==> (MM.fresh ae_log (n,i) h0 \/ c =!= fst (MM.value ae_log (n,i) h0)))
	 )
  ))


let decrypt #i n k c =
  let honest_i = is_honest i in
  if ae_int_ctxt && honest_i then
    match MM.lookup ae_log (n,i) with
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
