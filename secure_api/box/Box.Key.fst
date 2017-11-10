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

open Box.Flags

module ID = Box.Index
module Plain = Box.Plain
module MR = FStar.Monotonic.RRef
module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module MM = MonotoneMap
module SPEC = Spec.SecretBox

assume val is_random: bytes -> Type0

let index_module = ID.index_module
let plain_module = Plain.plain_module
let id = ID.id

type log_region =
  r:MR.rid{is_eternal_region r}

type key_t (im:index_module) (pm:plain_module)= Type0

//type aes_key = SPEC.key
//type cipher = b:bytes{Seq.length b >= 16 /\ (Seq.length b - 16) / Spec.Salsa20.blocklen < pow2 32}
//noeq type key_t2 (im:index_module) =

#set-options "--z3rlimit 300 --max_ifuel 1 --max_fuel 0"
abstract noeq type key_module (im:index_module) =
  | KM:
    keylen: nat ->
    key_type: (im':index_module{im' == im} -> t:Type0) ->
    get_index: (k:key_type im -> i:id im) -> // You have to have faith in this function...
    get_rawGT: ((k:key_type im) -> GTot (b:lbytes keylen)) -> // You have to have faith in this function...
    invariant: (h:mem -> Type0) ->
    key_log_region: (rgn:log_region{disjoint rgn (ID.get_rgn im)}) ->
    gen: (i:id im -> ST (k:key_type im{get_index k = i}) // The spec should indicate that the result is random and that gen is idempotent
      (requires (fun h0 ->
        (ID.fresh im i h0 \/ ID.honest im i)
        /\ invariant h0))
      (ensures  (fun h0 k h1 ->
        invariant h1
        /\ modifies (Set.singleton key_log_region) h0 h1
        ))) ->
    set: ((i:id im {Game3? current_game \/ Game0? current_game}) -> (b:lbytes keylen) -> (k:key_type im{get_index k = i /\ b = get_rawGT k})) ->
    coerce: (i:id im{ID.dishonest im i} -> raw:lbytes keylen -> (k:key_type im{get_index k = i /\ raw=get_rawGT k})) ->
    leak: (k:key_type im{ID.dishonest im (get_index k)} -> (raw:lbytes keylen{raw = get_rawGT k})) ->
    key_module im

val get_keylen: im:index_module -> km:key_module im -> n:nat{n = km.keylen}
let get_keylen im km =
  km.keylen

val get_keytype: im:index_module -> km:key_module im -> t:Type0{t == km.key_type im}
let get_keytype im km =
  km.key_type im

val get_index: im:index_module -> km:key_module im -> gi:(k:km.key_type im -> i:id im){gi==km.get_index}
let get_index im km =
  km.get_index

val get_rawGT: im:index_module -> km:key_module im -> gr:(k:km.key_type im -> GTot (b:lbytes km.keylen)){gr == km.get_rawGT}
let get_rawGT im km =
  km.get_rawGT

val get_log_region: im:index_module -> km:key_module im -> rgn:log_region{rgn = km.key_log_region}
let get_log_region im km =
  km.key_log_region

val gen: (im:index_module) -> (km:key_module im) -> (i:id im) -> ST (k:km.key_type im{km.get_index k = i})
  (requires (fun h0 ->
    (ID.fresh im i h0 \/ ID.honest im i)
    /\ km.invariant h0))
  (ensures  (fun h0 k h1 ->
    km.invariant h1
    /\ modifies (Set.singleton km.key_log_region) h0 h1
  ))
let gen im km i =
  km.gen i

val set: (im:index_module) -> (km:key_module im) -> (i:id im {~(Game2? current_game)}) -> (b:lbytes km.keylen) -> (k:km.key_type im{km.get_index k = i /\ b = km.get_rawGT k})
let set im km i b =
  km.set i b

val coerce: (im:index_module) -> (km:key_module im) -> (i:id im{ID.dishonest im i}) -> (b:lbytes km.keylen) -> (k:km.key_type im{km.get_index k = i /\ b = km.get_rawGT k})
let coerce im km i b =
  km.coerce i b

val leak: im:index_module -> (km:key_module im) -> (k:km.key_type im{ID.dishonest im (km.get_index k)}) -> (b:lbytes km.keylen{b=km.get_rawGT k})
let leak im km k =
  km.leak k

val invariant: im:index_module -> km:key_module im -> inv:(h0:mem -> Type0){inv == km.invariant}
let invariant im km =
  km.invariant

#set-options "--z3rlimit 2000 --max_ifuel 2 --max_fuel 0"
val create: (im:index_module) ->
            (keylen: nat) ->
            (km_key_type: (im':index_module{im' == im} -> t:Type0)) ->
            (km_get_index: (k:km_key_type im -> i:id im)) -> // You have to have faith in this function...
            (km_get_rawGT: ((k:km_key_type im) -> GTot (b:lbytes keylen))) -> // You have to have faith in this function...
            (km_invariant: (h:mem -> Type0)) ->
            (km_key_log_region: (r:log_region{disjoint r (ID.get_rgn im)})) ->
            (km_gen: (i:id im -> ST (k:km_key_type im{km_get_index k = i}) // The spec should indicate that the result is random and that gen is idempotent
              (requires (fun h0 ->
                (ID.fresh im i h0 \/ ID.honest im i)
                /\ km_invariant h0))
              (ensures  (fun h0 k h1 ->
                km_invariant h1
                /\ modifies (Set.singleton km_key_log_region) h0 h1
              )))) ->
            (km_set: (i:id im {Game3? current_game \/ Game0? current_game} -> b:lbytes keylen -> (k:km_key_type im{km_get_index k = i /\ b = km_get_rawGT k}))) ->
            (km_coerce: (i:id im{ID.dishonest im i} -> raw:lbytes keylen -> (k:km_key_type im{km_get_index k = i /\ raw=km_get_rawGT k}))) ->
            (km_leak: (k:km_key_type im{ID.dishonest im (km_get_index k)} -> (raw:lbytes keylen{raw = km_get_rawGT k}))) ->
            (km:key_module im{
              get_keytype im km == km_key_type im
              /\ get_keylen im km == keylen
              /\ get_index im km == km_get_index
              /\ get_rawGT im km == km_get_rawGT
              /\ invariant im km == km_invariant
              /\ get_log_region im km == km_key_log_region
    })
let create im keylen km_key_type km_get_index km_get_rawGT km_invariant km_key_log_region km_gen km_set km_coerce km_leak =
  let km = KM keylen km_key_type km_get_index km_get_rawGT km_invariant km_key_log_region km_gen km_set km_coerce km_leak in
  km
