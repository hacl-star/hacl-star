(**
   This module exists to provide type information and functions needed by Box.DH. Box.AE is not imported directly by
   Box.DH to preserve some notion of modularity. If Box.DH should be used with some other module, only Box.PlainDH
   should have to be edited.
*)
module Box.Key

open FStar.HyperHeap
open FStar.HyperStack
open FStar.HyperHeap.ST
open Crypto.Symmetric.Bytes

module MR = FStar.Monotonic.RRef
module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module MM = MonotoneMap
module SPEC = Spec.SecretBox

assume val is_random: bytes -> Type0

// Have an abstract(?) key type in here with a leak function attached? Then abstract-alias it in the AE module.
// Then we can use it in other places if we don't idealize.
// What refinements to have on the leak function?

type id = int
type nonce = SPEC.nonce
let noncesize = SPEC.noncelen
let keysize = SPEC.keylen
type aes_key = SPEC.key
type bytes = SPEC.bytes
type cipher = b:bytes{Seq.length b >= 16 /\ (Seq.length b - 16) / Spec.Salsa20.blocklen < pow2 32}


type ae_log_region =
  r:MR.rid{ extends r root
            /\ is_eternal_region r
            /\ is_below r root
            }

#set-options "--z3rlimit 500 --max_ifuel 2 --max_fuel 0"
type protected_ae_plain (i:id) = bytes
type pairtype (i:id)= (cipher*protected_ae_plain i)
type key_log_key = (nonce*(i:id))
type key_log_value (i:id) = (cipher*protected_ae_plain i)
type key_log_range (k:ae_log_key) = ae_log_value (snd k)
type key_log_inv (f:MM.map' ae_log_key ae_log_range) = True

type key_log (rgn:ae_log_region) =
  MM.t rgn ae_log_key ae_log_range ae_log_inv

noeq abstract type key (#it:Type0) (id:it) =
  | Key: rgn:ae_log_region -> log:(ae_log rgn) -> raw:bytes -> key #it id

abstract noeq type key_module (im:index_module) =
  | KM:
    key:Type0 ->
    rgn:ae_log_region ->
    fresh: (id:it -> Type0) ->
    honest: (id:it -> Type0) ->
    honestST: (id:it -> ST bool
      (requires (fun h0 -> True))
      (ensures (fun h0 b h1 -> b <==> honest id))) ->
    dishonest: (id:it -> Type0) ->
    dishonestST: (id:it -> ST bool
      (requires (fun h0 -> True))
      (ensures (fun h0 b h1 -> b <==> dishonest id))) ->
    make_honest: (id:it -> ST unit
      (requires (fun h0 -> ~(dishonest id)))
      (ensures (fun h0 _ h1 -> honest id))) ->
    make_dishonest: (id:it -> ST unit
      (requires (fun h0 -> ~(honest id)))
      (ensures (fun h0 _ h1 -> dishonest id))) ->
    get_rawGT: (#id:it -> (k:key #it id) -> GTot (b:bytes{k.raw = b})) -> // Returns the raw bytes of the key. Needed for spec of gen/leak/coerce.
    gen: (id:it -> ST (k:key id)
      (requires fun h -> honest id)
      (ensures fun h0 k h1 -> True)) ->
    coerce: (id:it -> b:bytes -> ST (k:key id)
      (requires fun h -> ~(honest id))
      (ensures fun h0 k h1 -> True)) ->  // What requirments for coerce? Determinism?
    leak: (#id:it -> k:key id -> ST (b:bytes)
      (requires (fun h -> ~(honest id)))
      (ensures (fun h0 k h1 -> True))) -> // What requirements here? Inverse of coerce?
    key_module

val get_region: km:key_module -> ae_log_region
let get_region km =
  km.rgn

val getIt: km:key_module -> Type0
let getIt km =
  km.it

val honest: km:key_module -> id:km.it -> Type0
let honest km id =
  km.honest id

val honestST: km:key_module -> id:km.it -> ST bool
  (requires (fun h0 -> True))
  (ensures (fun h0 b h1 -> b <==> honest km id))
let honestST km id =
  km.honestST id


val dishonest: km:key_module -> id:km.it -> Type0
let dishonest km id =
  km.dishonest id

val dishonestST: km:key_module -> id:km.it -> ST bool
  (requires (fun h0 -> True))
  (ensures (fun h0 b h1 -> b <==> dishonest km id))
let dishonestST km id =
  km.dishonestST id

val make_honest: km:key_module -> id:km.it -> ST unit
  (requires (fun h0 -> ~(dishonest km id)))
  (ensures (fun h0 b h1 -> honest km id))
let make_honest km id =
  km.make_honest id

val make_dishonest: km:key_module -> id:km.it -> ST unit
  (requires (fun h0 -> ~(honest km id)))
  (ensures (fun h0 b h1 -> dishonest km id))
let make_dishonest km id =
  km.make_dishonest id

val gen: (km:key_module) -> (id:km.it) -> ST (k:key #km.it id)
  (requires (fun h0 -> km.fresh id))
  (ensures (fun h0 k h1 -> True))
let gen km id =
  km.gen id

val coerce: (km:key_module) -> (id:km.it) -> (b:bytes) -> ST (k:key #km.it id)
  (requires (fun h0 -> ~(km.honest id)))
  (ensures (fun h0 k h1 -> True))
let coerce km id b =
  km.coerce id b

val leak: (km:key_module) -> (#id:km.it) -> (k:key id) -> ST (b:bytes)
  (requires (fun h0 -> ~(km.honest id)))
  (ensures (fun h0 k h1 -> True))
let leak km #id k =
  km.leak k
