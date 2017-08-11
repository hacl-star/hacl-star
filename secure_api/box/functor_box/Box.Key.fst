(**
   This module exists to provide type information and functions needed by Box.DH. Box.AE is not imported directly by
   Box.DH to preserve some notion of modularity. If Box.DH should be used with some other module, only Box.PlainDH
   should have to be edited.
*)
module Box.Key

open FStar.HyperHeap
open FStar.HyperStack
open FStar.HyperStack.ST
open Crypto.Symmetric.Bytes

open Box.Indexing
open Box.Plain
open Box.Flags

module MR = FStar.Monotonic.RRef
module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module MM = MonotoneMap
module SPEC = Spec.SecretBox

assume val is_random: bytes -> Type0

// Have an abstract(?) key type in here with a leak function attached? Then abstract-alias it in the AE module.
// Then we can use it in other places if we don't idealize.
// What refinements to have on the leak function?


type log_region (im:index_module) =
  r:MR.rid{disjoint r (get_rgn im)}


type key_t (im:index_module) (pm:plain_module)= Type0

type aes_key = SPEC.key
type cipher = b:bytes{Seq.length b >= 16 /\ (Seq.length b - 16) / Spec.Salsa20.blocklen < pow2 32}
noeq type key_t2 (im:index_module) =
  | Key: i:id im -> raw:aes_key -> key_t2 im

#set-options "--z3rlimit 300 --max_ifuel 1 --max_fuel 0"
abstract noeq type key_module (im:index_module) =
  | KM:
    get_index: (k:key_t2 im -> i:id im{k.i = i}) ->
    get_rawGT: (#i:id im -> (k:key_t2 im) -> GTot (b:bytes{b=k.raw})) -> // Returns the raw bytes of the key. Needed for spec of gen/leak/coerce.
    gen: (i:id im -> ST (k:key_t2 im{k.i = i}) // The spec should indicate that the result is random
      (requires (fun h0 ->
        fresh im (ID i) h0 \/ honest im (ID i)
      ))
      (ensures  (fun h0 k h1 ->
        h0 == h1
      ))) ->
    coerce: (i:id im -> b:bytes -> ST (k:key_t2 im{k.i = i /\ b=k.raw}) //TODO: make Total
      (requires (fun h0 ->
        dishonest im (ID i) \/ fresh im (ID i) h0 //TODO: require only dishonest
      ))
      (ensures  (fun h0 k h1 ->
        h0 == h1
      ))) ->
    leak: (k:key_t2 im{(dishonest im (ID (get_index k))) \/ ~(b2t ae_ind_cca)} -> (b:bytes{b = k.raw})) -> //TODO: remove not ae_ind_cca
    key_module im

let create (im:index_module) (get_index:(k:key_t2 im -> i:id im{k.i = i})) get_rawGT gen coerce leak =
  KM get_index get_rawGT gen coerce leak

val get_index: im:index_module -> km:key_module im -> k:key_t2 im -> i:id im{k.i = i}
let get_index im km k =
  km.get_index k

val gen: (im:index_module) -> (km:key_module im) -> (i:id im) -> ST (k:key_t2 im{k.i = i})
  (requires (fun h0 ->
    fresh im (ID i) h0 \/ honest im (ID i)
  ))
  (ensures  (fun h0 k h1 ->
    h0 == h1
    //let modified_regions_fresh_key = (Set.union (Set.singleton am.message_log_region) (Set.singleton am.key_log_region)) in
    //(MM.fresh am.key_log i h0 ==> modifies modified_regions_fresh_key h0 h1)
    ///\ (MM.defined am.key_log i h0 ==> h0 == h1)
  ))
let gen im km i =
  km.gen i

val coerce: (im:index_module) -> (km:key_module im) -> (i:id im) -> (b:bytes) -> ST (k:key_t2 im{k.i = i /\ b = k.raw})
  (requires (fun h0 ->
    dishonest im (ID i) \/ fresh im (ID i) h0
  ))
  (ensures (fun h0 k h1 ->
    h0 == h1
  ))
let coerce im km i b =
  km.coerce i b

val leak: im:index_module -> (km:key_module im) -> (k:key_t2 im{(dishonest im (ID k.i)) \/ ~(b2t ae_ind_cca)}) -> (b:bytes{b=k.raw})
let leak im km k =
  km.leak k
