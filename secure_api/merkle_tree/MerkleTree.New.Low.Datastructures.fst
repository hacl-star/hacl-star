module MerkleTree.New.Low.Datastructures

open FStar.All
open FStar.Integers
open FStar.Mul

open LowStar.Buffer
open LowStar.BufferOps
open LowStar.Vector
open LowStar.Regional
open LowStar.RVector
open LowStar.Regional.Instances

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MHS = FStar.Monotonic.HyperStack
module HH = FStar.Monotonic.HyperHeap

module B = LowStar.Buffer
module CB = LowStar.ConstBuffer
module V = LowStar.Vector
module RV = LowStar.RVector
module RVI = LowStar.Regional.Instances

module S = FStar.Seq

module EHS = EverCrypt.Hash
module U32 = FStar.UInt32
module MTH = MerkleTree.New.High

open EverCrypt.Helpers
open Lib.IntTypes

open MerkleTree.New.Low.Hashes

#set-options "--z3rlimit 10 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

// We cannot use `Low.RVector.Instances`, where we have some general
// typeclass instances of `regional`, e.g., if `rg:regional a` then
// `regional (rvector rg)`. In FStar we can use this, but KreMLin currently
// cannot deal with this and gives a number of errors.
// So we temporarily instantiate some `regional`s manually below, which is
// extractable to C by KreMLin.

/// Some instantiations of `regional` used in Merkle tree
/// 1. `hash` is regional

val hash_region_of: #hsz:hash_size_t -> v:hash #hsz -> GTot HH.rid
let hash_region_of #_ v =
  B.frameOf v

noextract inline_for_extraction private
val hash_dummy (#hsz:hash_size_t): hash #hsz
let hash_dummy #hsz = B.null

val hash_r_inv: #hsz:hash_size_t -> h:HS.mem -> v:hash #hsz -> GTot Type0
let hash_r_inv #hsz h v =
  B.live h v /\ B.freeable v /\
  B.len v = hsz

val hash_r_inv_reg:
  #hsz:hash_size_t ->
  h:HS.mem -> v:hash ->
  Lemma (requires hash_r_inv h v)
        (ensures MHS.live_region h (hash_region_of #hsz v))
let hash_r_inv_reg #_ h v = ()

private
val hash_repr (#hsz:hash_size_t): Type0
let hash_repr #hsz = MTH.hash #(U32.v hsz)

val hash_r_repr: #hsz:hash_size_t -> h:HS.mem -> v:hash{hash_r_inv #hsz h v} -> GTot (hash_repr #hsz)
let hash_r_repr #_ h v = B.as_seq h v

val hash_r_sep:
  #hsz:hash_size_t ->
  v:hash #hsz -> p:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires
      hash_r_inv h0 v /\
      loc_disjoint
        (loc_all_regions_from false
          (hash_region_of v)) p /\
      modifies p h0 h1)
  (ensures
     hash_r_inv h1 v /\
     hash_r_repr h0 v == hash_r_repr h1 v)
let hash_r_sep #_ v p h0 h1 =
  assert (loc_includes (loc_all_regions_from false (hash_region_of v))
                       (loc_buffer v));
  B.modifies_buffer_elim v p h0 h1

val hash_irepr: #hsz:hash_size_t -> Ghost.erased (hash_repr #hsz)
let hash_irepr #hsz =
  Ghost.hide (S.create (U32.v hsz) (u8 0))

val hash_r_alloc_p: #hsz:hash_size_t -> v:hash #hsz -> GTot Type0
let hash_r_alloc_p #_ v = True

val hash_r_alloc:
  #hsz:hash_size_t ->
  r:HST.erid ->
  HST.ST (hash #hsz)
    (requires (fun h0 -> true))
    (ensures (fun h0 v h1 ->
      Set.subset (Map.domain (MHS.get_hmap h0))
                 (Map.domain (MHS.get_hmap h1)) /\
      modifies loc_none h0 h1 /\
      hash_r_alloc_p v /\
      hash_r_inv h1 v /\
      hash_region_of v = r /\
      hash_r_repr h1 v == Ghost.reveal hash_irepr /\
      B.fresh_loc (B.loc_buffer v) h0 h1))
let hash_r_alloc #hsz r =
  B.malloc r (u8 0) hsz

val hash_r_free:
  #hsz:hash_size_t ->
  v:hash #hsz ->
  HST.ST unit
    (requires fun h0 -> hash_r_inv h0 v)
    (ensures  fun h0 _ h1 ->
      modifies (loc_all_regions_from false (hash_region_of v)) h0 h1)
let hash_r_free #_ v =
  B.free v

val hash_copy:
  #hsz:hash_size_t ->
  src:hash #hsz -> dst:hash #hsz ->
  HST.ST unit
    (requires fun h0 ->
      hash_r_inv h0 src /\ hash_r_inv h0 dst /\
      HH.disjoint (hash_region_of src) (hash_region_of dst))
    (ensures fun h0 _ h1 ->
      modifies (loc_all_regions_from false (hash_region_of dst)) h0 h1 /\
      hash_r_inv h1 dst /\
      hash_r_repr h1 dst == hash_r_repr h0 src)
let hash_copy #hsz src dst =
  B.blit src 0ul dst 0ul hsz

noextract inline_for_extraction
val hreg: #hsz:hash_size_t -> regional (hash #hsz)
let hreg #hsz =
  Rgl hash_region_of
      B.loc_buffer
      hash_dummy
      hash_r_inv
      hash_r_inv_reg
      hash_repr
      hash_r_repr
      hash_r_sep
      hash_irepr
      hash_r_alloc_p
      hash_r_alloc
      hash_r_free

val hcpy: #hsz:hash_size_t -> copyable (hash #hsz) hreg
let hcpy #_ = Cpy hash_copy

type hash_vec (#hsz:hash_size_t) = RV.rvector (hreg #hsz)

/// 2. `rvector hash` is regional

val hash_vec_region_of: #hsz:hash_size_t -> v:hash_vec #hsz -> GTot HH.rid
let hash_vec_region_of #_ v = V.frameOf v

private
val hash_vec_dummy: #hsz:hash_size_t -> hash_vec #hsz
let hash_vec_dummy #_ = V.alloc_empty hash

val hash_vec_r_inv: #hsz:hash_size_t -> h:HS.mem -> v:hash_vec #hsz -> GTot Type0
let hash_vec_r_inv #_ h v = RV.rv_inv h v

val hash_vec_r_inv_reg:
  #hsz:hash_size_t -> 
  h:HS.mem -> v:hash_vec #hsz ->
  Lemma (requires (hash_vec_r_inv h v))
  (ensures (MHS.live_region h (hash_vec_region_of v)))
let hash_vec_r_inv_reg #_ h v = ()

private
val hash_vec_repr: #hsz:hash_size_t -> Type0
let hash_vec_repr #hsz = MTH.hashes #(U32.v hsz)

val hash_vec_r_repr:
  #hsz:hash_size_t -> 
  h:HS.mem -> v:hash_vec #hsz {hash_vec_r_inv h v} -> GTot (hash_vec_repr #hsz)
let hash_vec_r_repr #_ h v =
  RV.as_seq h v

val hash_vec_r_sep:
  #hsz:hash_size_t -> 
  v:hash_vec #hsz -> p:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (hash_vec_r_inv h0 v /\
      loc_disjoint
        (loc_all_regions_from false (hash_vec_region_of v))
        p /\
      modifies p h0 h1))
  (ensures (hash_vec_r_inv h1 v /\
     hash_vec_r_repr h0 v == hash_vec_r_repr h1 v))
let hash_vec_r_sep #_ v p h0 h1 =
  RV.rv_inv_preserved v p h0 h1;
  RV.as_seq_preserved v p h0 h1

val hash_vec_irepr: #hsz:hash_size_t -> Ghost.erased (hash_vec_repr #hsz)
let hash_vec_irepr #_ = Ghost.hide S.empty

val hash_vec_r_alloc_p: #hsz:hash_size_t -> v:hash_vec #hsz -> GTot Type0
let hash_vec_r_alloc_p #_ v = V.size_of v = 0ul

#push-options "--initial_fuel 1 --max_fuel 1"
val hash_vec_r_alloc:
  #hsz:hash_size_t -> 
  r:HST.erid ->
  HST.ST (v:hash_vec #hsz)
    (requires (fun h0 -> true))
    (ensures (fun h0 v h1 ->
      Set.subset (Map.domain (MHS.get_hmap h0))
                 (Map.domain (MHS.get_hmap h1)) /\
      modifies loc_none h0 h1 /\
      hash_vec_r_alloc_p v /\
      hash_vec_r_inv h1 v /\
      hash_vec_region_of v = r /\
      hash_vec_r_repr h1 v == Ghost.reveal hash_vec_irepr /\
      B.fresh_loc (V.loc_vector v) h0 h1))
let hash_vec_r_alloc #_ r =
  let nrid = HST.new_region r in
  let ia = Rgl?.dummy hreg in
  V.alloc_reserve 1ul ia r
#pop-options

val hash_vec_r_free:
  #hsz:hash_size_t -> 
  v:hash_vec #hsz ->
  HST.ST unit
    (requires (fun h0 -> hash_vec_r_inv h0 v))
    (ensures (fun h0 _ h1 ->
      modifies (loc_all_regions_from false (hash_vec_region_of v)) h0 h1))
let hash_vec_r_free #_ v =
  RV.free v

noextract inline_for_extraction
val hvreg: #hsz:hash_size_t -> regional (hash_vec #hsz)
let hvreg #_ =
  Rgl hash_vec_region_of
      V.loc_vector
      hash_vec_dummy
      hash_vec_r_inv
      hash_vec_r_inv_reg
      hash_vec_repr
      hash_vec_r_repr
      hash_vec_r_sep
      hash_vec_irepr
      hash_vec_r_alloc_p
      hash_vec_r_alloc
      hash_vec_r_free

type hash_vv (#hsz:hash_size_t) = RV.rvector (hvreg #hsz)

noextract
val hvvreg: #hsz:hash_size_t -> regional (hash_vv #hsz)
let hvvreg #_ = RVI.vector_regional hvreg

val hash_vec_rv_inv_r_inv:
  #hsz:hash_size_t ->
  h:HS.mem -> hv:hash_vec #hsz -> i:uint32_t{i < V.size_of hv} ->
  Lemma (requires RV.rv_inv h hv)
        (ensures  Rgl?.r_inv hreg h (V.get h hv i))
let hash_vec_rv_inv_r_inv #_ h hv i = ()

val hash_vv_rv_inv_r_inv:
  #hsz:hash_size_t ->
  h:HS.mem -> hvv:hash_vv #hsz ->
  i:uint32_t -> j:uint32_t ->
  Lemma (requires RV.rv_inv h hvv /\
                  i < V.size_of hvv /\
                  j < V.size_of (V.get h hvv i))
        (ensures Rgl?.r_inv hvreg h (V.get h hvv i) /\
                 Rgl?.r_inv hreg h (V.get h (V.get h hvv i) j))
let hash_vv_rv_inv_r_inv #_ h hvv i j = ()

val hash_vv_rv_inv_disjoint:
  #hsz:hash_size_t ->
  h:HS.mem -> hvv:hash_vv #hsz ->
  i:uint32_t -> j:uint32_t -> drid:HH.rid ->
  Lemma (requires (RV.rv_inv h hvv /\
                  i < V.size_of hvv /\
                  j < V.size_of (V.get h hvv i) /\
                  HH.disjoint (Rgl?.region_of hvvreg hvv) drid))
        (ensures (HH.disjoint (Rgl?.region_of hreg (V.get h (V.get h hvv i) j)) drid))
let hash_vv_rv_inv_disjoint #_ h hvv i j drid =
  assert (HH.disjoint (Rgl?.region_of hvreg (V.get h hvv i)) drid);
  assert (RV.rv_inv h (V.get h hvv i));
  assert (HH.disjoint (Rgl?.region_of hreg (V.get h (V.get h hvv i) j)) drid)

val hash_vv_rv_inv_includes:
  #hsz:hash_size_t ->
  h:HS.mem -> hvv:hash_vv #hsz ->
  i:uint32_t -> j:uint32_t ->
  Lemma (requires (RV.rv_inv h hvv /\
                  i < V.size_of hvv /\
                  j < V.size_of (V.get h hvv i)))
        (ensures (HH.includes
                   (Rgl?.region_of hvvreg hvv)
                   (Rgl?.region_of hreg (V.get h (V.get h hvv i) j))))
let hash_vv_rv_inv_includes #_ h hvv i j = ()

val hash_vv_as_seq_get_index:
  #hsz:hash_size_t ->
  h:HS.mem -> hvv:hash_vv #hsz -> i:uint32_t -> j:uint32_t ->
  Lemma (requires (RV.rv_inv h hvv /\
                  i < V.size_of hvv /\
                  j < V.size_of (V.get h hvv i)))
        (ensures (Rgl?.r_repr hreg h (V.get h (V.get h hvv i) j) ==
                 S.index (S.index (RV.as_seq h hvv) (U32.v i)) (U32.v j)))
#push-options "--z3rlimit 20"
let hash_vv_as_seq_get_index #_ h hvv i j = ()
#pop-options
