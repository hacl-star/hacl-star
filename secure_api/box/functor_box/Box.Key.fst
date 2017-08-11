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
    //key_type: (im:index_module -> t:Type0{t==key_t2 im}) ->
    get_index: (k:key_t2 im -> i:id im{k.i = i}) ->
    get_rawGT: ((k:key_t2 im) -> GTot (b:aes_key{b=k.raw})) -> // Returns the raw bytes of the key. Needed for spec of gen/leak/coerce.
    invariant: (h:mem -> Type0) ->
    gen: (i:id im -> ST (k:key_t2 im{k.i = i}) // The spec should indicate that the result is random and that gen is idempotent
      (requires (fun h0 ->
        (fresh im (ID i) h0 \/ honest im (ID i))
        /\ invariant h0))
      (ensures  (fun h0 k h1 -> invariant h1))) ->
    coerce: (i:id im{dishonest im (ID i)} -> raw:aes_key -> (k:key_t2 im{k.i = i /\ raw=k.raw})) ->
    leak: (k:key_t2 im{dishonest im (ID (get_index k))} -> (raw:aes_key{raw = k.raw})) ->
    key_module im

let create (im:index_module) (get_index:(k:key_t2 im -> i:id im{k.i = i})) get_rawGT invariant gen coerce leak =
  KM get_index get_rawGT invariant gen coerce leak

val get_index: im:index_module -> km:key_module im -> k:key_t2 im -> i:id im{k.i = i}
let get_index im km k =
  km.get_index k

val gen: (im:index_module) -> (km:key_module im) -> (i:id im) -> ST (k:key_t2 im{k.i = i})
  (requires (fun h0 ->
    (fresh im (ID i) h0 \/ honest im (ID i))
    /\ km.invariant h0))
  (ensures  (fun h0 k h1 -> km.invariant h1))
let gen im km i =
  km.gen i

val coerce: (im:index_module) -> (km:key_module im) -> (i:id im{dishonest im (ID i)}) -> (b:bytes) -> (k:key_t2 im{k.i = i /\ b = k.raw})
let coerce im km i b =
  km.coerce i b

val leak: im:index_module -> (km:key_module im) -> (k:key_t2 im{dishonest im (ID k.i)}) -> (b:bytes{b=k.raw})
let leak im km k =
  km.leak k

val km_invariant: im:index_module -> km:key_module im -> h0:mem -> Type0
let km_invariant im km h0 =
  km.invariant h0
