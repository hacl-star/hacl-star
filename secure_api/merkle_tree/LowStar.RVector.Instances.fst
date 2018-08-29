module LowStar.RVector.Instances

open FStar.All
open FStar.Integers
open LowStar.Buffer
open LowStar.RVector

module HH = FStar.Monotonic.HyperHeap
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module V = LowStar.Vector
module RV = LowStar.RVector

/// `LowStar.Buffer` is regional

val buffer_region_of:
  #a:Type -> v:B.buffer a -> GTot HH.rid
let buffer_region_of #a v =
  B.frameOf v

val buffer_r_invariant:
  #a:Type -> len:UInt32.t{len > 0ul} ->
  h:HS.mem -> v:B.buffer a -> GTot Type0
let buffer_r_invariant #a len h v =
  B.len v = len

val buffer_r_live:
  #a:Type -> h:HS.mem -> v:B.buffer a -> GTot Type0
let buffer_r_live #a h v =
  B.live h v

val buffer_r_live_preserved:
  #a:Type -> v:B.buffer a -> p:loc -> h:HS.mem -> h':HS.mem ->
  Lemma (requires (loc_disjoint 
		    (loc_all_regions_from false 
		      (buffer_region_of v)) p /\
		  buffer_r_live h v /\ modifies p h h'))
	(ensures (buffer_r_live h' v))
let buffer_r_live_preserved #a v p h h' =
  assert (loc_includes (loc_all_regions_from false (B.frameOf v))
		       (loc_buffer v));
  B.modifies_buffer_elim v p h h'

val buffer_r_freeable:
  #a:Type -> h:HS.mem -> v:B.buffer a -> GTot Type0
let buffer_r_freeable #a h v =
  B.freeable v

val buffer_r_init: 
  #a:Type -> ia:a -> len:UInt32.t{len > 0ul} -> r:erid ->
  HST.ST (b:B.buffer a)
    (requires (fun h0 -> true))
    (ensures (fun h0 v h1 -> 
      modifies loc_none h0 h1 /\
      buffer_r_invariant len h1 v /\
      buffer_r_live h1 v /\ buffer_r_freeable h1 v /\
      buffer_region_of v = r))
let buffer_r_init #a ia len r =
  B.malloc r ia len

val buffer_r_copy:
  #a:Type -> len:UInt32.t{len > 0ul} -> 
  src:B.buffer a -> dst:B.buffer a ->
  HST.ST unit
    (requires (fun h0 ->
      buffer_r_invariant len h0 src /\ buffer_r_invariant len h0 dst /\
      buffer_r_live h0 src /\ buffer_r_live h0 dst /\
      HH.disjoint (buffer_region_of src) (buffer_region_of dst)))
    (ensures (fun h0 _ h1 ->
      modifies (loc_all_regions_from false (buffer_region_of dst)) h0 h1 /\
      buffer_r_live h1 dst))
let buffer_r_copy #a len src dst =
  B.blit src 0ul dst 0ul len

val buffer_r_free:
  #a:Type -> v:B.buffer a ->
  HST.ST unit
    (requires (fun h0 -> 
      buffer_r_live h0 v /\ buffer_r_freeable h0 v))
    (ensures (fun h0 _ h1 ->
      modifies (loc_all_regions_from false (buffer_region_of v)) h0 h1))
let buffer_r_free #a v =
  B.free v

val buffer_regional: 
  #a:Type -> ia:a -> len:UInt32.t{len > 0ul} ->
  regional (b:B.buffer a)
let buffer_regional #a ia len =
  Rgl (buffer_region_of #a)
      (buffer_r_invariant #a len)
      (buffer_r_live #a)
      (buffer_r_live_preserved #a)
      (buffer_r_freeable #a)
      (buffer_r_init #a ia len)
      (buffer_r_copy #a len)
      (buffer_r_free #a)

/// If `a` is regional, then `rvector a` is also regional

val vector_region_of: 
  #a:Type -> #rg:regional a -> v:rvector rg -> GTot HH.rid
let vector_region_of #a #rg v = V.frameOf v

val vector_r_invariant:
  #a:Type -> #rg:regional a -> 
  h:HS.mem -> v:rvector rg -> GTot Type0
let vector_r_invariant #a #rg h v =
  rv_disj h v

val vector_r_live:
  #a:Type -> #rg:regional a ->
  h:HS.mem -> v:rvector rg -> GTot Type0
let vector_r_live #a #rg h v =
  V.live h v /\
  V.forall_all h v (fun e -> Rgl?.r_live rg h e)

val vector_r_live_preserved:
  #a:Type -> #rg:regional a ->
  v:rvector rg -> p:loc -> h:HS.mem -> h':HS.mem ->
  Lemma (requires (vector_r_invariant h v /\
		  loc_disjoint 
		    (loc_all_regions_from false (vector_region_of v))
		    p /\
		  vector_r_live h v /\ modifies p h h'))
	(ensures (vector_r_live h' v))
let vector_r_live_preserved #a #rg v p h h' =
  admit ()

val vector_r_freeable:
  #a:Type -> #rg:regional a ->
  h:HS.mem -> v:rvector rg -> GTot Type0
let vector_r_freeable #a #rg h v =
  V.freeable v /\
  V.forall_all h v (fun e -> Rgl?.r_freeable rg h e)

val vector_r_init: 
  #a:Type -> #rg:regional a -> ia:a -> r:erid ->
  HST.ST (v:rvector rg)
    (requires (fun h0 -> true))
    (ensures (fun h0 v h1 -> 
      modifies loc_none h0 h1 /\
      vector_r_invariant h1 v /\
      vector_r_live h1 v /\ vector_r_freeable h1 v /\
      vector_region_of v = r))
let vector_r_init #a #rg ia r =
  V.create_reserve 1ul ia r

val vector_r_copy:
  #a:Type -> #rg:regional a ->
  src:rvector rg -> dst:rvector rg ->
  HST.ST unit
    (requires (fun h0 ->
      vector_r_live h0 src /\ vector_r_live h0 dst /\
      HH.disjoint (vector_region_of src) (vector_region_of dst)))
    (ensures (fun h0 _ h1 ->
      modifies (loc_all_regions_from false (vector_region_of dst)) h0 h1 /\
      vector_r_live h1 dst))
let vector_r_copy #a #rg src dst =
  // `r_copy` is not used above a certain level, e.g., no copy operations are
  // called for `V.vector (B.buffer a)`. Do we need to implement even so?
  admit () 

val vector_r_free:
  #a:Type -> #rg:regional a -> v:rvector rg ->
  HST.ST unit
    (requires (fun h0 ->
      vector_r_invariant h0 v /\
      vector_r_live h0 v /\ vector_r_freeable h0 v))
    (ensures (fun h0 _ h1 ->
      modifies (loc_all_regions_from false (vector_region_of v)) h0 h1))
let vector_r_free #a #rg v =
  RV.free v

val vector_regional: 
  #a:Type -> ia:a -> rg:regional a -> regional (rvector rg)
let vector_regional #a ia rg =
  Rgl (vector_region_of #a #rg)
      (vector_r_invariant #a #rg)
      (vector_r_live #a #rg)
      (vector_r_live_preserved #a #rg)
      (vector_r_freeable #a #rg)
      (vector_r_init #a #rg ia)
      (vector_r_copy #a #rg)
      (vector_r_free #a #rg)

// An instantiation: `LowStar.Buffer` of `LowStar.RVector` is regional.

val buffer_vector_regional:
  #a:Type -> ia:a -> len:UInt32.t{len > 0ul} ->
  regional (rvector #(B.buffer a) (buffer_regional ia len))


