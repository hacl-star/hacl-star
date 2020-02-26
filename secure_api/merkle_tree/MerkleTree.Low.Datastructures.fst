module MerkleTree.Low.Datastructures

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

#set-options "--z3rlimit 10 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

type hash_size_t = n:uint32_t{n > 0ul}
type hash (#hsz:hash_size_t) = b:B.buffer uint8 { B.len b = hsz \/ B.g_is_null b }

// We cannot use `Low.RVector.Instances`, where we have some general
// typeclass instances of `regional`, e.g., if `rg:regional a` then
// `regional (rvector rg)`. In FStar we can use this, but KreMLin currently
// cannot deal with this and gives a number of errors.
// So we temporarily instantiate some `regional`s manually below, which is
// extractable to C by KreMLin.

/// Some instantiations of `regional` used in Merkle tree
/// 1. `hash` is regional

private
noextract
val hash_region_of: #hsz:hash_size_t -> v:hash #hsz -> GTot HH.rid
let hash_region_of #_ v = B.frameOf v

private inline_for_extraction
val hash_dummy: #hsz:Ghost.erased hash_size_t -> Tot (hash #hsz)
let hash_dummy #_ = B.null

private
noextract
val hash_r_inv: #hsz:hash_size_t -> h:HS.mem -> v:hash #hsz -> GTot Type0
let hash_r_inv #hsz h v =
  B.live h v /\ B.freeable v /\
  B.len v = hsz

private
noextract
val hash_r_inv_reg:
  #hsz:hash_size_t ->
  h:HS.mem -> v:hash ->
  Lemma (requires hash_r_inv h v)
        (ensures MHS.live_region h (hash_region_of #hsz v))
let hash_r_inv_reg #_ h v = ()

private
noextract
val hash_repr (#hsz:hash_size_t): Type0
let hash_repr #hsz = MTH.hash #(U32.v hsz)

private
noextract
val hash_r_repr: #hsz:hash_size_t -> h:HS.mem -> v:hash{hash_r_inv #hsz h v} -> GTot (hash_repr #hsz)
let hash_r_repr #_ h v = B.as_seq h v

private
noextract
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

private
noextract
val hash_irepr: #hsz:hash_size_t -> Ghost.erased (hash_repr #hsz)
let hash_irepr #hsz =
  Ghost.hide (S.create (U32.v hsz) (u8 0))

private
noextract
val hash_r_alloc_p: #hsz:hash_size_t -> v:hash #hsz -> GTot Type0
let hash_r_alloc_p #_ v = True

val hash_r_alloc:
  #hsz':Ghost.erased hash_size_t ->
  hsz:hash_size_t { hsz == Ghost.reveal hsz' } ->
  r:HST.erid ->
  HST.ST (hash #hsz)
    (requires (fun h0 -> true))
    (ensures (fun h0 v h1 ->
      Set.subset (Map.domain (MHS.get_hmap h0))
                 (Map.domain (MHS.get_hmap h1)) /\
      modifies loc_none h0 h1 /\
      hash_r_alloc_p #hsz v /\
      hash_r_inv h1 v /\
      hash_region_of v = r /\
      hash_r_repr h1 v == Ghost.reveal hash_irepr /\
      B.fresh_loc (B.loc_buffer v) h0 h1))
let hash_r_alloc #_ s r =
  B.malloc r (u8 0) s

val hash_r_free:
  #hsz:Ghost.erased hash_size_t ->
  v:hash #hsz ->
  HST.ST unit
    (requires fun h0 -> hash_r_inv h0 v)
    (ensures  fun h0 _ h1 ->
      modifies (loc_all_regions_from false (hash_region_of v)) h0 h1)
let hash_r_free #_ v =
  B.free v

noextract inline_for_extraction
val hreg (hsz:hash_size_t): regional (h:hash_size_t) (hash #hsz)
let hreg hsz =
  Rgl #(h:hash_size_t) #(hash #hsz) hsz
      (hash_region_of #hsz)
      (B.loc_buffer)
      (hash_dummy #hsz)
      (hash_r_inv #hsz)
      (hash_r_inv_reg #hsz)
      (hash_repr #hsz)
      (hash_r_repr #hsz)
      (hash_r_sep #hsz)
      (hash_irepr #hsz)
      (hash_r_alloc_p #hsz)
      (hash_r_alloc #hsz)
      (hash_r_free #hsz)

private
val hash_copy:
  #s':Ghost.erased hash_size_t ->
  s:hash_size_t { s == Ghost.reveal s' } ->
  src:hash #s -> dst:hash #s ->
  HST.ST unit
    (requires fun h0 ->
      hash_r_inv h0 src /\ hash_r_inv h0 dst /\
      HH.disjoint (hash_region_of src) (hash_region_of dst))
    (ensures fun h0 _ h1 ->
      modifies (loc_all_regions_from false (hash_region_of dst)) h0 h1 /\
      hash_r_inv h1 dst /\
      hash_r_repr h1 dst == hash_r_repr h0 src)
let hash_copy #_ s src dst =
  B.blit src 0ul dst 0ul s

/// JP: so much stuff happening here. First, single-constructor, single-argument
/// elimination takes places and Cpy becomes completely eliminated, in favor of
/// just being a type alias for the underlying function. So now, we have a
/// function that returns a function pointer.
///
/// Next, one might think that the hsz argument is going to be eliminated. It's
/// not, because there's a hidden implicit argument to Cpy which is (hreg hsz),
/// meaning that hsz is used at run-time even though Cpy is only using this
/// argument ghostly. This would be have to be fixed.
///
/// Finally, if the inline_for_extraction is removed, there seems to be a
/// kremlin bug that inserts a void*0. To be fixed.
inline_for_extraction
val hcpy: hsz:hash_size_t -> copyable #hash_size_t (hash #hsz) (hreg hsz)
let hcpy hsz =
  Cpy (hash_copy #hsz)

type hash_vec (#hsz:hash_size_t) = RV.rvector (hreg hsz)

/// 2. `rvector hash` is regional

type rhst (hsz:hash_size_t) = regional hash_size_t (hash #hsz)

private
noextract
val hash_vec_region_of: #hsz:hash_size_t -> v:hash_vec #hsz -> GTot HH.rid
let hash_vec_region_of #_ v = V.frameOf v

private inline_for_extraction
val hash_vec_dummy: (#hsz:Ghost.erased hash_size_t) -> hash_vec #hsz
let hash_vec_dummy #_ = V.alloc_empty (hash #_)

noextract
val hash_vec_r_inv: #hsz:hash_size_t -> h:HS.mem -> v:hash_vec #hsz -> GTot Type0
let hash_vec_r_inv #hsz h v = RV.rv_inv h v

noextract
val hash_vec_r_inv_reg:
  #hsz:hash_size_t -> 
  h:HS.mem -> v:hash_vec #hsz ->
  Lemma (requires (hash_vec_r_inv h v))
  (ensures (MHS.live_region h (hash_vec_region_of v)))
let hash_vec_r_inv_reg #_ h v = ()

private
noextract
val hash_vec_repr: #hsz:hash_size_t -> Type0
let hash_vec_repr #hsz = MTH.hashes #(U32.v hsz)

noextract
val hash_vec_r_repr:
  #hsz:hash_size_t -> 
  h:HS.mem -> v:hash_vec #hsz {hash_vec_r_inv h v} -> GTot (hash_vec_repr #hsz)
let hash_vec_r_repr #_ h v =
  RV.as_seq h v

noextract
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

noextract
val hash_vec_irepr: #hsz:hash_size_t -> Ghost.erased (hash_vec_repr #hsz)
let hash_vec_irepr #_ = Ghost.hide S.empty

noextract
val hash_vec_r_alloc_p: #hsz:hash_size_t -> v:hash_vec #hsz -> GTot Type0
let hash_vec_r_alloc_p #_ v = V.size_of v = 0ul

#push-options "--initial_fuel 1 --max_fuel 1"
val hash_vec_r_alloc:
  #hsz':Ghost.erased hash_size_t ->
  hsz:hash_size_t { hsz == Ghost.reveal hsz' } ->
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
let hash_vec_r_alloc #_ hsz r =
  let nrid = HST.new_region r in
  // Note: here we are not creating a generic parameterized regional, we are
  // creating a specialized regional vector of hashes, so we don't need to go
  // through a run-time indirection to figure out what the dummy default element
  // is; we know it's the one for hashes
  V.alloc_reserve 1ul (hash_dummy #hsz) r
#pop-options

val hash_vec_r_free:
  #hsz:Ghost.erased hash_size_t ->
  v:hash_vec ->
  HST.ST unit
    (requires (fun h0 -> hash_vec_r_inv h0 v))
    (ensures (fun h0 _ h1 ->
      modifies (loc_all_regions_from false (hash_vec_region_of #hsz v)) h0 h1))
let hash_vec_r_free #_ v =
  // RV.free v
  V.free v

/// This is nice because the only piece of state that we are keeping is one
/// word, the hash size, since we are implementing a specialized instance of
/// RVector over hashes of a known length. We could also, for genericity, make
/// this a mere application of RVector over hreg, which would be less
/// implementation effort, at the expense of a bigger run-time cost since there
/// would be extra space in the struct (which is passed by value!) and also a
/// run-time indirection to do the lookup of the type class instance for the
/// elements of the rvector.
noextract inline_for_extraction
val hvreg (hsz:hash_size_t): regional hash_size_t (hash_vec #hsz)
let hvreg hsz =
  Rgl hsz
      (hash_vec_region_of #hsz)
      V.loc_vector
      (hash_vec_dummy #hsz)
      (hash_vec_r_inv #hsz)
      (hash_vec_r_inv_reg #hsz)
      (hash_vec_repr #hsz)
      (hash_vec_r_repr #hsz)
      (hash_vec_r_sep #hsz)
      (hash_vec_irepr #hsz)
      (hash_vec_r_alloc_p #hsz)
      (hash_vec_r_alloc #hsz)
      (hash_vec_r_free #hsz)

/// 3. A vector of hash vectors is also regional

type hash_vv (hsz:hash_size_t) = RV.rvector (hvreg hsz)

noextract inline_for_extraction
val hvvreg (hsz:hash_size_t): regional (regional hash_size_t (hash_vec #hsz)) (hash_vv hsz)
let hvvreg hsz = RVI.vector_regional (hvreg hsz)

val hash_vec_rv_inv_r_inv:
  #hsz:hash_size_t ->
  h:HS.mem -> hv:hash_vec #hsz -> i:uint32_t{i < V.size_of hv} ->
  Lemma (requires RV.rv_inv h hv)
        (ensures  Rgl?.r_inv (hreg hsz) h (V.get h hv i))
let hash_vec_rv_inv_r_inv #_ h hv i = ()

val hash_vv_rv_inv_r_inv:
  #hsz:hash_size_t ->
  h:HS.mem -> hvv:hash_vv hsz ->
  i:uint32_t -> j:uint32_t ->
  Lemma (requires RV.rv_inv h hvv /\
                  i < V.size_of hvv /\
                  j < V.size_of (V.get h hvv i))
        (ensures Rgl?.r_inv (hvreg hsz) h (V.get h hvv i) /\
                 Rgl?.r_inv (hreg hsz) h (V.get h (V.get h hvv i) j))
let hash_vv_rv_inv_r_inv #_ h hvv i j = ()

val hash_vv_rv_inv_disjoint:
  #hsz:hash_size_t ->
  h:HS.mem -> hvv:hash_vv hsz ->
  i:uint32_t -> j:uint32_t -> drid:HH.rid ->
  Lemma (requires (RV.rv_inv h hvv /\
                  i < V.size_of hvv /\
                  j < V.size_of (V.get h hvv i) /\
                  HH.disjoint (Rgl?.region_of (hvvreg hsz) hvv) drid))
        (ensures (HH.disjoint (Rgl?.region_of (hreg hsz) (V.get h (V.get h hvv i) j)) drid))
let hash_vv_rv_inv_disjoint #hsz h hvv i j drid =
  assert (HH.disjoint (Rgl?.region_of (hvreg hsz) (V.get h hvv i)) drid);
  assert (RV.rv_inv h (V.get h hvv i));
  assert (HH.disjoint (Rgl?.region_of (hreg hsz) (V.get h (V.get h hvv i) j)) drid)

val hash_vv_rv_inv_includes:
  #hsz:hash_size_t ->
  h:HS.mem -> hvv:hash_vv hsz ->
  i:uint32_t -> j:uint32_t ->
  Lemma (requires (RV.rv_inv h hvv /\
                  i < V.size_of hvv /\
                  j < V.size_of (V.get h hvv i)))
        (ensures (HH.includes
                   (Rgl?.region_of (hvvreg hsz) hvv)
                   (Rgl?.region_of (hreg hsz) (V.get h (V.get h hvv i) j))))
let hash_vv_rv_inv_includes #_ h hvv i j = ()

val hash_vv_as_seq_get_index:
  #hsz:hash_size_t ->
  h:HS.mem -> hvv:hash_vv hsz -> i:uint32_t -> j:uint32_t ->
  Lemma (requires (RV.rv_inv h hvv /\
                  i < V.size_of hvv /\
                  j < V.size_of (V.get h hvv i)))
        (ensures (Rgl?.r_repr (hreg hsz) h (V.get h (V.get h hvv i) j) ==
                 S.index (S.index (RV.as_seq h hvv) (U32.v i)) (U32.v j)))
#push-options "--z3rlimit 20"
let hash_vv_as_seq_get_index #_ h hvv i j = ()
#pop-options
