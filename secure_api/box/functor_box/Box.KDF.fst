(**
  A key derivation function
*)
module Box.KDF

open FStar.Set
open FStar.HyperHeap
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Monotonic.RRef

open Crypto.Symmetric.Bytes

open Box.Flags
open Box.Plain
open Box.Index
open Box.Key

module MR = FStar.Monotonic.RRef
module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module MM = MonotoneMap

module HSalsa = Spec.HSalsa20
let keylen = HSalsa.keylen 
let rawkey = HSalsa.key
module SPEC = Spec.SecretBox
module Plain = Box.Plain
module Key = Box.Key

#set-options "--z3rlimit 1300 --max_ifuel 1 --max_fuel 2"
type key_id (im:index_module) = | Derived : id im -> key_id im

type out_index_module (im:index_module) = kim:index_module{id kim == key_id im}

type log_region (im:index_module) =
  r:MR.rid{disjoint r (get_rgn im)}


//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// The following functions belong to the formal KEY module in the model.
//////////////////////////////////////////////////////////////////////////////////////////////////////////////

(**
   The key type is abstract and can only be accessed via the leak and coerce_key functions. This means that the adversary has no means
   of accessing the raw representation of any honest key.
*)
abstract noeq type key (im:index_module) =
  | Key: i:id im -> raw:rawkey -> key im

private val get_index: #im:index_module -> k:key im -> i:id im{i = k.i}
let get_index #im k =
  k.i

(**
  Similar to the leak_key function, get_keyGT provides access to the raw representation of a key.
  However, note that the GTot effect only allows use in type refinements and is erased upon extraction.
*)
private val get_rawGT: #im:index_module -> k:key im -> GTot (b:rawkey{k.raw=b})
let get_rawGT #im k =
  k.raw

type key_log_key (im:index_module) = i:id im
type key_log_value (im:index_module) = (key im)
let key_log_range (im:index_module) = fun (k:key_log_key im) -> (v:key_log_value im{v.i = k})
let key_log_inv (im:index_module) (f:MM.map' (key_log_key im) (key_log_range im)) = True

type key_log_t (im:index_module) (rgn:log_region im) = MM.t rgn (key_log_key im) (key_log_range im) (key_log_inv im)


abstract noeq type kdf_module (im:index_module) =
  | DM :
    key_log_region: log_region im ->
    key_log: (key_log_t im key_log_region) ->
    out_im:out_index_module im ->
    out_km:key_module out_im{get_keylen out_im out_km = keylen} ->
    kdf_module im


val recall_logs: #im:index_module -> dm:kdf_module im -> ST unit
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 ->
    h0 == h1
    /\ MR.m_contains dm.key_log h1
  ))
let recall_logs #im dm =
  MR.m_recall dm.key_log

val create: im:index_module -> rgn:log_region im -> out_im:out_index_module im ->out_km:key_module out_im{get_keylen out_im out_km = keylen} -> ST (dm:kdf_module im)
(requires (fun h0 ->
  True
))
(ensures (fun h0 dm h1 ->
  modifies_none h0 h1
  /\ MR.m_contains dm.key_log h1
  /\ MR.m_sel #dm.key_log_region h1 dm.key_log == MM.empty_map (key_log_key im) (key_log_range im)
))
 

#set-options "--z3rlimit 1000 --max_ifuel 1 --max_fuel 0"
let create im rgn out_im out_km =
  let klr = new_region rgn in
  let kl = MM.alloc #klr #(key_log_key im) #(key_log_range im) #(key_log_inv im) in
  recall_log im;
  DM klr kl out_im out_km
  
(**
   This function generates a fresh random key. Honest, as well as dishonest ids can be created using keygen. However, note that the adversary can
   only access the raw representation of dishonest keys. 
*)
private val gen: #im:index_module  -> dm:kdf_module im -> i:id im -> ST (k:key im{get_index k=i})
  (requires (fun h0 ->
    (fresh im i h0 \/ honest im i)
  ))
  (ensures  (fun h0 k h1 ->
    (MM.fresh dm.key_log i h0 ==>
              (modifies (Set.singleton dm.key_log_region) h0 h1
              /\ MR.m_sel h1 dm.key_log == MM.upd (MR.m_sel h0 dm.key_log) i k))
    /\ (MM.defined dm.key_log i h0 ==> modifies Set.empty h0 h1)
  ))

let gen #im dm i =
  match MM.lookup dm.key_log i with
  | Some k -> k
  | None ->
    let rnd_k = random_bytes (UInt32.uint_to_t keylen) in
    let k:key im = Key i rnd_k in
    recall_log im;
    MR.m_recall dm.key_log;
    MM.extend dm.key_log i k;
    admit();
    k

(**
   The coerce function transforms a raw key into an abstract key. Only dishonest ids can be used
   with this function.
*)
private val coerce: #im:index_module -> i:id im{dishonest im i} -> raw_k:rawkey -> (k:key im{get_index k=i /\ get_rawGT k = raw_k})
let coerce #im i raw_k =
  Key i raw_k

(**
   The leak_key function transforms an abstract key into a raw key.
   The refinement type on the key makes sure that no honest keys can be leaked.
*)
private val leak: #im:index_module -> k:key im{dishonest im (get_index k)} -> Tot (raw_k:rawkey{raw_k=get_rawGT k})
let leak #im k =
  k.raw

#set-options "--z3rlimit 300 --max_ifuel 0 --max_fuel 0 --print_full_names --print_effect_args --print_implicits --print_universes"
val instantiate_km: #im:index_module -> dm:kdf_module im -> km:key_module im{
    Key.get_keytype im km == key im
    /\ Key.get_index im km == get_index #im
    /\ Key.get_rawGT im km == get_rawGT #im
    /\ Key.get_log_region im km == dm.key_log_region
  }


let instantiate_km #im dm =
  let km = Key.create im keylen key get_index get_rawGT (fun (m:mem) -> True ) (dm.key_log_region) (gen dm) coerce leak in
  km
//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// The following functions belong to the formal KDF module in the model.
//////////////////////////////////////////////////////////////////////////////////////////////////////////////
 

  val derive: im:index_module -> dm:kdf_module im -> k:key im -> ST (k':Key.get_keytype dm.out_im dm.out_km{Key.get_index dm.out_im dm.out_km k' = Derived (get_index k) } )
  (requires (fun h0 ->
    ( let i = get_index k in
      let out_i : id dm.out_im = Derived i in
      registered im i 
    /\ registered dm.out_im out_i
    /\ Key.invariant dm.out_im dm.out_km h0
    )
  ))
  (ensures (fun h0 k' h1 ->
    let i = get_index k in
    let out_i : id dm.out_im = Derived i in
    (honest dm.out_im out_i ==> modifies (Set.singleton (Key.get_log_region dm.out_im dm.out_km)) h0 h1)
    // We should guarantee, that the key is randomly generated. Generally, calls to derive should be idempotent. How to specify that?
    // Should we have a genPost condition that we guarantee here?
    /\ (dishonest dm.out_im out_i ==> True
          //              (Key.leak im km k =  deriveGT k // Functional correctness. Spec should be external in Spec.Cryptobox.
                        /\ h0 == h1)
//    /\ (modifies (Set.singleton (Key.get_log_region out_im out_km)) h0 h1 \/ h0 == h1)
    /\ Key.invariant dm.out_im dm.out_km h1
  )
)

(**
Nonce to use with HSalsa.hsalsa20.
  *)
private let zero_nonce = Seq.create HSalsa.noncelen (UInt8.uint_to_t 0)

let derive im dm k =
  let i = get_index k in
  let out_i : id dm.out_im = Derived i in
  lemma_honest_or_dishonest dm.out_im out_i;
  match get_honest dm.out_im out_i with
  | true ->
    Key.gen dm.out_im dm.out_km out_i 
  | false ->
    let hashed_raw_k = HSalsa.hsalsa20 k.raw zero_nonce in
    Key.coerce dm.out_im dm.out_km out_i hashed_raw_k 
