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


type log_region (im:index_module) =
  r:MR.rid{disjoint r (ID.get_rgn im)}

(**
   The unprotected plaintext type.
*)
let plain_max_length = Spec.Salsa20.blocklen `op_Multiply` pow2 32
type ae_plain = b:bytes{Seq.length b < plain_max_length} // / Spec.Salsa20.blocklen < pow2 32} //one off error?

val create_zero_bytes: n:nat{n < plain_max_length}-> Tot (b:ae_plain{Seq.length b = n /\ b=Seq.create n (UInt8.uint_to_t 0)})
let create_zero_bytes n =
  Seq.create n (UInt8.uint_to_t 0)

type ae_protected_plain (im:index_module) (pm:plain_module) (i:id im) = m:Plain.protected_plain_t im (get_plain pm) i

(**
  A helper function to obtain the length of a protected plaintext.
*)
val length: b:ae_plain -> n:nat{n<plain_max_length}
let length (b:ae_plain) = Seq.length b

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// The following functions belong to the formal KEY module in the model.
//////////////////////////////////////////////////////////////////////////////////////////////////////////////

(**
   The key type is abstract and can only be accessed via the leak and coerce_key functions. This means that the adversary has no means
   of accessing the raw representation of any honest AE key if AE is idealized.
*)
abstract noeq type key (im:index_module) =
  | Key: i:id im -> raw:aes_key -> key im

private val get_index: #im:index_module -> k:key im -> i:id im{i = k.i}
let get_index #im k =
  k.i

(**
  Similar to the leak_key function, get_keyGT provides access to the raw representation of an AE key.
  However, note that the GTot effect only allows use in type refinements and is erased upon extraction.
*)
private val get_rawGT: #im:index_module -> k:key im -> GTot (b:aes_key{k.raw=b})
let get_rawGT #im k =
  k.raw

type key_log_key (im:index_module) = i:id im
type key_log_value (im:index_module) = (key im)
let key_log_range (im:index_module) = fun (k:key_log_key im) -> (v:key_log_value im{v.i = k})
let key_log_inv (im:index_module) (f:MM.map' (key_log_key im) (key_log_range im)) = True

type key_log_t (im:index_module) (rgn:log_region im) = MM.t rgn (key_log_key im) (key_log_range im) (key_log_inv im)


type message_log_key (im:index_module) = (nonce*(i:id im))
type message_log_value (im:index_module) (i:id im) = (cipher*protected_plain_t im ae_plain i)
type message_log_range (im:index_module) (k:message_log_key im) = (message_log_value im (snd k))
type message_log_inv (im:index_module) (f:MM.map' (message_log_key im) (message_log_range im)) = True

type message_log (im:index_module) (rgn:log_region im) =
  MM.t rgn (message_log_key im) (message_log_range im) (message_log_inv im)

abstract noeq type ae_module (im:index_module) =
  | AM :
    (pm:plain_module{get_plain pm == ae_plain}) ->
    key_log_region: log_region im ->
    message_log_region: (rgn:log_region im{disjoint rgn key_log_region}) ->
    key_log: (key_log_t im key_log_region) ->
    message_log: (message_log im message_log_region) ->
    ae_module im

#set-options "--z3rlimit 2000 --max_ifuel 1 --max_fuel 0"
val recall_logs: #im:index_module -> am:ae_module im -> ST unit
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 ->
    h0 == h1
    /\ MR.m_contains am.message_log h1
    /\ MR.m_contains am.key_log h1
  ))
let recall_logs #im am =
  MR.m_recall am.key_log;
  MR.m_recall am.message_log

val get_message_log_region: #im:index_module  -> am:ae_module im -> (lr:log_region im{lr == am.message_log_region})
let get_message_log_region #im am =
  am.message_log_region

val get_message_logGT: #im:index_module  -> am:ae_module im -> Tot (ml:message_log im am.message_log_region{ml == am.message_log}) //TODO: MK would prefer this to be GTot
let get_message_logGT #im am =
  am.message_log

val get_pm: #im:index_module -> am:ae_module im -> pm:plain_module{pm == am.pm}
let get_pm #im am = am.pm

val nonce_is_fresh: (#im:index_module) -> (am:ae_module im) -> (i:id im) -> (n:nonce) -> (h:mem) -> (t:Type0{t <==>
    (MR.m_contains am.message_log h
    /\ MM.fresh am.message_log (n,i) h)})
let nonce_is_fresh (#im:index_module) (am:ae_module im) (i:id im) (n:nonce) (h:mem) =
  let _ = () in
  MR.m_contains am.message_log h
  /\ MM.fresh am.message_log (n,i) h

(**
  This invariant makes sure that there are no entries in the logs for fresh IDs. It should be maintained by any function handling the message log.
*)
abstract let log_freshness_invariant (#im:index_module) (am:ae_module im) (h:mem) =
  MR.m_contains (get_log im) h
  /\ MR.m_contains am.message_log h
  /\ (forall i n . ID.fresh im (ID i) h ==> MM.fresh am.message_log (n,i) h)

val nonce_freshness_lemma: #im:index_module  -> am:ae_module im -> i:id im -> n:nonce -> h0:mem -> h1:mem -> Lemma
  (requires nonce_is_fresh am i n h0)
  (ensures ((modifies (Set.singleton am.key_log_region) h0 h1 \/ h0 == h1) ==> nonce_is_fresh am i n h1))
let nonce_freshness_lemma #im am i n h0 h1 =
 ()

#set-options "--z3rlimit 2000 --max_ifuel 1 --max_fuel 0"
val create: im:index_module -> pm:plain_module{Plain.get_plain pm == ae_plain /\ Plain.plain_max_length #pm = plain_max_length} -> rgn:log_region im -> ST (am:ae_module im)
  (requires (fun h0 ->
    True
  ))
  (ensures (fun h0 am h1 ->
    modifies_none h0 h1
    /\ MR.m_contains am.key_log h1
    /\ MR.m_contains am.message_log h1
    /\ MR.m_sel #am.key_log_region h1 am.key_log == MM.empty_map (key_log_key im) (key_log_range im)
    /\ MR.m_sel #am.message_log_region h1 am.message_log == MM.empty_map (message_log_key im) (message_log_range im)
    /\ log_freshness_invariant #im am h1
  ))
let create im pm rgn =
  let klr = new_region rgn in
  let mlr = new_region rgn in
  let kl = MM.alloc #klr #(key_log_key im) #(key_log_range im) #(key_log_inv im) in
  let ml = MM.alloc #mlr #(message_log_key im) #(message_log_range im) #(message_log_inv im) in
  recall_log im;
  AM pm klr mlr kl ml

(**
   This function generates a fresh random key. Honest, as well as dishonest ids can be created using keygen. However, note that the adversary can
   only access the raw representation of dishonest keys. The log is created in a fresh region below the ae_key_region.
*)
#set-options "--z3rlimit 2000 --max_ifuel 1 --max_fuel 0"
private val gen: #im:index_module  -> am:ae_module im -> i:id im -> ST (k:key im{get_index k=i})
  (requires (fun h0 ->
    (fresh im (ID i) h0 \/ honest im (ID i))
  ))
  (ensures  (fun h0 k h1 ->
    (MM.fresh am.key_log i h0 ==>
              (modifies (Set.singleton am.key_log_region) h0 h1
              /\ MR.m_sel h1 am.key_log == MM.upd (MR.m_sel h0 am.key_log) i k))
    /\ (MM.defined am.key_log i h0 ==> modifies Set.empty h0 h1)
  ))

let gen #im am i =
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
private val coerce: #im:index_module -> i:id im{dishonest im (ID i)} -> raw_k:aes_key -> (k:key im{get_index k=i /\ get_rawGT k = raw_k})
let coerce #im i raw_k =
  Key i raw_k

(**
   The leak_key function transforms an abstract key into a raw aes_key.
   The refinement type on the key makes sure that no honest keys can be leaked.
*)
private val leak: #im:index_module -> k:key im{dishonest im (ID (get_index k))} -> Tot (raw_k:aes_key{raw_k=get_rawGT k})
let leak #im k =
  k.raw

#set-options "--z3rlimit 1000 --max_ifuel 0 --max_fuel 0"
val instantiate_km: #im:index_module -> am:ae_module im -> km:key_module im{
    Key.get_keytype im km == key im
    /\ Key.get_index im km == get_index #im
    /\ Key.get_rawGT im km == get_rawGT #im
    /\ Key.invariant im km == log_freshness_invariant am
    /\ Key.get_log_region im km == am.key_log_region
    /\ disjoint (Key.get_log_region im km) am.message_log_region
  }
let instantiate_km #im am =
  let km = Key.create im key get_index get_rawGT (log_freshness_invariant am) (am.key_log_region) (gen am) coerce leak in
  km

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// The following functions belong to the formal AE module in the model.
//////////////////////////////////////////////////////////////////////////////////////////////////////////////

#reset-options
#set-options "--z3rlimit 400 --max_ifuel 0 --max_fuel 0"
(**
   Encrypt a a message under a key. Idealize if the key is honest and ae_ind_cca true.
*)
val encrypt: #im:index_module -> am:ae_module im -> #(i:id im) -> n:nonce -> k:key im{get_index k=i} -> m:ae_protected_plain im am.pm i -> ST cipher
(requires (fun h0 ->
  registered im (ID i)
  /\ nonce_is_fresh #im am i n h0 // Nonce freshness
  ///\ log_freshness_invariant #im #pm am h0
))
(ensures  (fun h0 c h1 ->
  let modified_regions_fresh = Set.union (Set.singleton am.message_log_region) (Set.singleton (ID.get_rgn im)) in
  let modified_regions_honest = Set.singleton am.message_log_region in
  registered im (ID i)
  /\ (dishonest im (ID i) ==> modifies (Set.singleton am.message_log_region) h0 h1) // No stateful changes if the id is dishonest.
  /\ ((honest im (ID i) /\ b2t ae_ind_cpa) // Ideal behaviour if the id is honest and the assumption holds.
      ==> (c = SPEC.secretbox_easy (create_zero_bytes (Plain.length #im #am.pm #i m)) (get_rawGT k) n))
  /\ ((dishonest im (ID i) \/ ~(b2t ae_ind_cpa)) // Concrete behaviour otherwise.
      ==> (eq2 #cipher c (SPEC.secretbox_easy (Plain.repr #im #am.pm #i m) (get_rawGT k) n)))
  /\ MR.m_contains am.message_log h1  // A message is added to the log if the id is honest. This also guarantees nonce-uniqueness.
  /\ MR.witnessed (MM.contains am.message_log (n,i) (c,m))
  /\ MR.m_sel h1 am.message_log == MM.upd (MR.m_sel h0 am.message_log) (n,i) (c,m)
  ///\ log_freshness_invariant #im #pm am h1
))

#set-options "--z3rlimit 900 --max_ifuel 1 --max_fuel 0"
let encrypt #im am #i n k m =
  MR.m_recall am.message_log;
  recall_log im;
  lemma_honest_or_dishonest im (ID i);
  let honest_i = get_honesty im (ID i) in
  let p =
    if honest_i && ae_ind_cpa then (
      Seq.create (Plain.length #im #am.pm #i m) (UInt8.uint_to_t 0)
    ) else (
      Plain.repr #im #am.pm #i m)
  in
  let  c = SPEC.secretbox_easy p k.raw n in
  MR.m_recall am.message_log;
  recall_log im;
  MM.extend am.message_log (n,i) (c,m);
  c


(**
   Decrypt a ciphertext c using a key k. If the key is honest and ae_int_ctxt is idealized,
   try to obtain the ciphertext from the log. Else decrypt via concrete implementation.
*)
val decrypt: #im:index_module -> am:ae_module im -> #(i:id im) -> n:nonce -> k:key im{get_index k=i} -> c:cipher -> ST (option (ae_protected_plain im am.pm i))
  (requires (fun h0 ->
    registered im (ID i) // No in-between states of keys (i.e.) where one of the shares is fresh and one is registerd
  ))
  (ensures  (fun h0 p h1 ->
    let modified_regions_honest = Set.singleton am.message_log_region in
    registered im (ID i)
    /\ h0 == h1
    /\ ((~(b2t ae_int_ctxt) \/ dishonest im (ID i)) ==> // Concrete behaviour of the id is dishonest or if the assumption doesn't hold.
        (let option_m = SPEC.secretbox_open_easy c (get_rawGT k) n in // Functional correctness: we get a result iff the ciphertext is valid.
          (Some? option_m ==>
            Some? p /\ Some?.v p == Plain.coerce #im #am.pm #i (Some?.v option_m))
          /\ (None? option_m ==>
              None? p)
      ))
    /\ ((b2t ae_int_ctxt /\ honest im (ID i)) // Ideal behaviour otherwise: We get a result iff something is in the log.
        ==> (Some? p
          ==> (MM.defined am.message_log (n,i) h0 /\ (fst (MM.value am.message_log (n,i) h0) == c )
            /\ Some?.v p == snd (MM.value am.message_log (n,i) h0)))
    /\ (None? p
    ==> (MM.fresh am.message_log (n,i) h0 \/ c =!= fst (MM.value am.message_log (n,i) h0)))
   )
  ))


#set-options "--z3rlimit 1900 --max_ifuel 1 --max_fuel 0"
let decrypt #im am #i n k c =
  MR.m_recall am.message_log;
  recall_log im;
  lemma_honest_or_dishonest im (ID i);
  let honest_i = get_honesty im (ID i) in
  MR.m_recall am.message_log;
  recall_log im;
  if honest_i && ae_int_ctxt then
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
      Some (Plain.coerce #im #am.pm #i p')
    | None -> None
