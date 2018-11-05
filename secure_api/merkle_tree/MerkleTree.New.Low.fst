module MerkleTree.New.Low

open EverCrypt
open EverCrypt.Helpers
open EverCrypt.AutoConfig

open FStar.All
open FStar.Integers
open FStar.Mul
open LowStar.Modifies
open LowStar.BufferOps
open Low.Vector
open Low.Regional
open Low.RVector
open Low.Regional.Instances

open MerkleTree.New.High

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MHS = FStar.Monotonic.HyperStack
module HH = FStar.Monotonic.HyperHeap

module B = LowStar.Buffer
module V = Low.Vector
module RV = Low.RVector
module RVI = Low.Regional.Instances

module S = FStar.Seq

module U32 = FStar.UInt32
module U8 = FStar.UInt8

module EHS = EverCrypt.Hash
module EHL = EverCrypt.Helpers

module High = MerkleTree.New.High

val hash_size: uint32_t
let hash_size = EHS.tagLen EHS.SHA256

type hash = uint8_p

val hash_cfg: EverCrypt.AutoConfig.impl -> HST.St unit
let hash_cfg i =
  EverCrypt.AutoConfig.init (EverCrypt.AutoConfig.Prefer i)

// We cannot use `Low.RVector.Instances`, where we have some general
// typeclass instances of `regional`, e.g., if `rg:regional a` then
// `regional (rvector rg)`. In FStar we can use this, but KreMLin currently
// cannot deal with this and gives a number of errors.
// So we temporarily instantiate some `regional`s manually below, which is
// extractable to C by KreMLin.

/// Some instantiations of `regional` used in Merkle tree
/// 1. `hash` is regional

val hash_region_of:
  v:hash -> GTot HH.rid
let hash_region_of v =
  B.frameOf v

private val hash_dummy: unit -> Tot hash
private let hash_dummy _ = B.null

val hash_r_inv: h:HS.mem -> v:hash -> GTot Type0
let hash_r_inv h v =
  B.live h v /\ B.freeable v /\
  B.len v = hash_size

val hash_r_inv_reg:
  h:HS.mem -> v:hash ->
  Lemma (requires (hash_r_inv h v))
  (ensures (MHS.live_region h (hash_region_of v)))
let hash_r_inv_reg h v = ()

private val hash_repr: Type0
private let hash_repr = High.hash

val hash_r_repr:
  h:HS.mem -> v:hash{hash_r_inv h v} -> GTot hash_repr
let hash_r_repr h v = B.as_seq h v

val hash_r_sep:
  v:hash -> p:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (hash_r_inv h0 v /\
      loc_disjoint
        (loc_all_regions_from false
          (hash_region_of v)) p /\
      modifies p h0 h1))
  (ensures (hash_r_inv h1 v /\
     hash_r_repr h0 v == hash_r_repr h1 v))
let hash_r_sep v p h0 h1 =
  assert (loc_includes (loc_all_regions_from false (hash_region_of v))
           (loc_buffer v));
  B.modifies_buffer_elim v p h0 h1

val hash_irepr: Ghost.erased hash_repr
let hash_irepr =
  Ghost.hide (S.create (U32.v hash_size) 0uy)

val hash_r_init_p: v:hash -> GTot Type0
let hash_r_init_p v = True

private val hash_r_init:
  r:erid ->
  HST.ST hash
    (requires (fun h0 -> true))
    (ensures (fun h0 v h1 ->
      Set.subset (Map.domain (MHS.get_hmap h0))
                 (Map.domain (MHS.get_hmap h1)) /\
      modifies loc_none h0 h1 /\
      hash_r_init_p v /\
      hash_r_inv h1 v /\
      hash_region_of v = r /\
      hash_r_repr h1 v == Ghost.reveal hash_irepr))
private let hash_r_init r =
  B.malloc r 0uy hash_size

val hash_r_free:
  v:hash ->
  HST.ST unit
    (requires (fun h0 -> hash_r_inv h0 v))
    (ensures (fun h0 _ h1 ->
      modifies (loc_all_regions_from false (hash_region_of v)) h0 h1))
let hash_r_free v =
  B.free v

val hash_copy:
  src:hash -> dst:hash ->
  HST.ST unit
    (requires (fun h0 ->
      hash_r_inv h0 src /\ hash_r_inv h0 dst /\
      HH.disjoint (hash_region_of src) (hash_region_of dst)))
    (ensures (fun h0 _ h1 ->
      modifies (loc_all_regions_from false (hash_region_of dst)) h0 h1 /\
      hash_r_inv h1 dst /\
      hash_r_repr h1 dst == hash_r_repr h0 src))
let hash_copy src dst =
  B.blit src 0ul dst 0ul hash_size

// `hash_dummy ()` is is also a trick to extract the C code using KreMLin.
// If we just define and use `hash_dummy` as a constant, then gcc complains with
// the error "initializer element is not a compile-time constant".
private val hreg: regional hash
private let hreg =
  Rgl hash_region_of
      (hash_dummy ())
      hash_r_inv
      hash_r_inv_reg
      hash_repr
      hash_r_repr
      hash_r_sep
      hash_irepr
      hash_r_init_p
      hash_r_init
      hash_r_free

private val hcpy: copyable hash hreg
private let hcpy = Cpy hash_copy

type hash_vec = RV.rvector hreg

/// 2. `rvector hash` is regional

val hash_vec_region_of:
  v:hash_vec -> GTot HH.rid
let hash_vec_region_of v = V.frameOf v

private val hash_vec_dummy: hash_vec
private let hash_vec_dummy = V.create_empty hash

val hash_vec_r_inv:
  h:HS.mem -> v:hash_vec -> GTot Type0
let hash_vec_r_inv h v = RV.rv_inv h v

val hash_vec_r_inv_reg:
  h:HS.mem -> v:hash_vec ->
  Lemma (requires (hash_vec_r_inv h v))
  (ensures (MHS.live_region h (hash_vec_region_of v)))
let hash_vec_r_inv_reg h v = ()

private val hash_vec_repr: Type0
private let hash_vec_repr = High.hash_seq

val hash_vec_r_repr:
  h:HS.mem -> v:hash_vec{hash_vec_r_inv h v} -> GTot hash_vec_repr
let hash_vec_r_repr h v =
  RV.as_seq h v

val hash_vec_r_sep:
  v:hash_vec -> p:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (hash_vec_r_inv h0 v /\
      loc_disjoint
        (loc_all_regions_from false (hash_vec_region_of v))
        p /\
      modifies p h0 h1))
  (ensures (hash_vec_r_inv h1 v /\
     hash_vec_r_repr h0 v == hash_vec_r_repr h1 v))
let hash_vec_r_sep v p h0 h1 =
  RV.rv_inv_preserved v p h0 h1;
  RV.as_seq_preserved v p h0 h1

val hash_vec_irepr: Ghost.erased hash_vec_repr
let hash_vec_irepr =
  Ghost.hide S.empty

val hash_vec_r_init_p: v:hash_vec -> GTot Type0
let hash_vec_r_init_p v =
  V.size_of v = 0ul

private val hash_vec_r_init:
  r:erid ->
  HST.ST (v:hash_vec)
    (requires (fun h0 -> true))
    (ensures (fun h0 v h1 ->
      Set.subset (Map.domain (MHS.get_hmap h0))
                 (Map.domain (MHS.get_hmap h1)) /\
      modifies loc_none h0 h1 /\
      hash_vec_r_init_p v /\
      hash_vec_r_inv h1 v /\
      hash_vec_region_of v = r /\
      hash_vec_r_repr h1 v == Ghost.reveal hash_vec_irepr))
private let hash_vec_r_init r =
  let nrid = RV.new_region_ r in
  let ia = Rgl?.dummy hreg in
  V.create_reserve 1ul ia r

val hash_vec_r_free:
  v:hash_vec ->
  HST.ST unit
    (requires (fun h0 -> hash_vec_r_inv h0 v))
    (ensures (fun h0 _ h1 ->
      modifies (loc_all_regions_from false (hash_vec_region_of v)) h0 h1))
let hash_vec_r_free v =  
  RV.free v


private val hvreg: regional hash_vec
private let hvreg =
  Rgl hash_vec_region_of
      hash_vec_dummy
      hash_vec_r_inv
      hash_vec_r_inv_reg
      hash_vec_repr
      hash_vec_r_repr
      hash_vec_r_sep
      hash_vec_irepr
      hash_vec_r_init_p
      hash_vec_r_init
      hash_vec_r_free

type hash_vv = RV.rvector hvreg

noextract private val hvvreg: regional hash_vv
noextract private let hvvreg =
  vector_regional hvreg

private val hash_vec_rv_inv_r_inv:
  h:HS.mem -> hv:hash_vec -> i:uint32_t{i < V.size_of hv} ->
  Lemma (requires (RV.rv_inv h hv))
        (ensures (Rgl?.r_inv hreg h (V.get h hv i)))
private let hash_vec_rv_inv_r_inv h hv i = ()

private val hash_vv_rv_inv_r_inv:
  h:HS.mem -> hvv:hash_vv ->
  i:uint32_t -> j:uint32_t ->
  Lemma (requires (RV.rv_inv h hvv /\
                  i < V.size_of hvv /\
                  j < V.size_of (V.get h hvv i)))
        (ensures (Rgl?.r_inv hreg h (V.get h (V.get h hvv i) j)))
private let hash_vv_rv_inv_r_inv h hvv lv i = ()

private val hash_vv_rv_inv_disjoint:
  h:HS.mem -> hvv:hash_vv ->
  i:uint32_t -> j:uint32_t -> drid:HH.rid ->
  Lemma (requires (RV.rv_inv h hvv /\
                  i < V.size_of hvv /\ 
                  j < V.size_of (V.get h hvv i) /\
                  HH.disjoint (Rgl?.region_of hvvreg hvv) drid))
        (ensures (HH.disjoint (Rgl?.region_of hreg (V.get h (V.get h hvv i) j)) drid))
private let hash_vv_rv_inv_disjoint h hvv i j drid =
  assert (HH.disjoint (Rgl?.region_of hvreg (V.get h hvv i)) drid);
  assert (RV.rv_inv h (V.get h hvv i));
  assert (HH.disjoint (Rgl?.region_of hreg (V.get h (V.get h hvv i) j)) drid)

private val hash_vv_as_seq_get_index:
  h:HS.mem -> hvv:hash_vv -> i:uint32_t -> j:uint32_t ->
  Lemma (requires (RV.rv_inv h hvv /\ 
                  i < V.size_of hvv /\
                  j < V.size_of (V.get h hvv i)))
        (ensures (Rgl?.r_repr hreg h (V.get h (V.get h hvv i) j) ==
                 S.index (S.index (RV.as_seq h hvv) (U32.v i)) (U32.v j)))
#reset-options "--z3rlimit 20"
private let hash_vv_as_seq_get_index h hvv i j = ()

/// The Merkle tree implementation begins here.

/// Utility for hashes

let init_hash = hash_r_init
let free_hash = hash_r_free

val hash_2:
  src1:hash -> src2:hash -> dst:hash ->
  HST.ST unit
   (requires (fun h0 ->
     Rgl?.r_inv hreg h0 src1 /\
     Rgl?.r_inv hreg h0 src2 /\
     Rgl?.r_inv hreg h0 dst))
   (ensures (fun h0 _ h1 ->
     // memory safety
     modifies (B.loc_region_only false (B.frameOf dst)) h0 h1 /\
     Rgl?.r_inv hreg h1 dst /\
     // correctness
     S.equal (Rgl?.r_repr hreg h1 dst)
       (High.hash_2
         (Rgl?.r_repr hreg h0 src1)
         (Rgl?.r_repr hreg h0 src2))))
#reset-options "--z3rlimit 40"
let hash_2 src1 src2 dst =
  let hh0 = HST.get () in
  HST.push_frame ();
  // let cb = B.malloc HH.root 0uy (EHS.blockLen EHS.SHA256) in
  // EHS.blockLen EHS.SHA256 = 64ul
  let cb = B.alloca 0uy 64ul in
  B.blit src1 0ul cb 0ul hash_size;
  B.blit src2 0ul cb 32ul hash_size;
  let st = EHS.create EHS.SHA256 in
  EHS.init #(Ghost.hide EHS.SHA256) st;
  let hh1 = HST.get () in
  assert (S.equal (S.append
                    (Rgl?.r_repr hreg hh0 src1)
                    (Rgl?.r_repr hreg hh0 src2))
                  (B.as_seq hh1 cb));
  EHS.update #(Ghost.hide EHS.SHA256) (Ghost.hide S.empty) st cb;
  let hh2 = HST.get () in
  assert (EHS.hashing st hh2 (S.append S.empty (B.as_seq hh1 cb)));
  assert (S.equal (S.append S.empty (B.as_seq hh1 cb))
                  (B.as_seq hh1 cb));
  EHS.finish #(Ghost.hide EHS.SHA256) st dst;
  let hh3 = HST.get () in
  assert (S.equal (B.as_seq hh3 dst)
                  (EHS.extract (EHS.repr st hh2)));
  assert (S.equal (B.as_seq hh3 dst)
                  (EHS.extract
                    (EHS.hash0 #EHS.SHA256 (B.as_seq hh1 cb))));
  assert (S.equal (B.as_seq hh3 dst)
                  (High.hash_2
                    (Rgl?.r_repr hreg hh0 src1)
                    (Rgl?.r_repr hreg hh0 src2)));
  EHS.free #(Ghost.hide EHS.SHA256) st;
  HST.pop_frame ();
  let hh4 = HST.get () in
  assert (S.equal (B.as_seq hh4 dst)
                  (High.hash_2
                    (Rgl?.r_repr hreg hh0 src1)
                    (Rgl?.r_repr hreg hh0 src2)));
  // TODO: need to deal with `st` and stack-allocated `cb`
  assume (modifies (B.loc_region_only false (B.frameOf dst)) hh0 hh4)

/// Low-level Merkle tree data structure

// NOTE: because of a lack of 64-bit LowStar.Buffer support, currently
// we cannot change below to some other types.
type index_t = uint32_t

inline_for_extraction val merkle_tree_size_lg: uint32_t
inline_for_extraction let merkle_tree_size_lg = 32ul

// A Merkle tree `MT i j hs rhs_ok rhs` stores all necessary hashes to generate
// a Merkle path for each element from the index `i` to `j-1`.
// - Parameters
// `hs`: a 2-dim store for hashes, where `hs[0]` contains leaf hash values.
// `rhs_ok`: to check the rightmost hashes are up-to-date
// `rhs`: a store for "rightmost" hashes, manipulated only when required to
//        calculate some merkle parhs that need the rightmost hashes
//        as a part of them.
// `mroot`: during the construction of `rhs` we can also calculate the Merkle
//          root of the tree. If `rhs_ok` is true then it has the up-to-date
//          root value.
noeq type merkle_tree =
| MT: i:index_t -> j:index_t{j >= i} ->
      hs:hash_vv{V.size_of hs = merkle_tree_size_lg} ->
      rhs_ok:bool ->
      rhs:hash_vec{V.size_of rhs = merkle_tree_size_lg} ->
      mroot:hash ->
      merkle_tree

type mt_p = B.pointer merkle_tree

val mt_not_full: HS.mem -> mt_p -> GTot bool
let mt_not_full h mt =
  MT?.j (B.get h mt 0) < U32.uint_to_t (UInt.max_int U32.n)

/// (Memory) Safety

val offset_of: i:index_t -> Tot index_t
let offset_of i =
  if i % 2ul = 0ul then i else i - 1ul

val mt_safe_elts:
  h:HS.mem -> lv:uint32_t{lv <= merkle_tree_size_lg} ->
  hs:hash_vv{V.size_of hs = merkle_tree_size_lg} ->
  i:index_t -> j:index_t{j >= i} ->
  GTot Type0 (decreases (32 - U32.v lv))
let rec mt_safe_elts h lv hs i j =
  if lv = merkle_tree_size_lg then true
  else (let ofs = offset_of i in
       V.size_of (V.get h hs lv) == j - ofs /\
       mt_safe_elts h (lv + 1ul) hs (i / 2ul) (j / 2ul))

val mt_safe_elts_constr:
  h:HS.mem -> lv:uint32_t{lv < merkle_tree_size_lg} ->
  hs:hash_vv{V.size_of hs = merkle_tree_size_lg} ->
  i:index_t -> j:index_t{j >= i} ->
  Lemma (requires (V.size_of (V.get h hs lv) == j - offset_of i /\
                  mt_safe_elts h (lv + 1ul) hs (i / 2ul) (j / 2ul)))
        (ensures (mt_safe_elts h lv hs i j))
let mt_safe_elts_constr h lv hs i j = ()

val mt_safe_elts_head:
  h:HS.mem -> lv:uint32_t{lv < merkle_tree_size_lg} ->
  hs:hash_vv{V.size_of hs = merkle_tree_size_lg} ->
  i:index_t -> j:index_t{j >= i} ->
  Lemma (requires (mt_safe_elts h lv hs i j))
        (ensures (V.size_of (V.get h hs lv) == j - offset_of i))
let mt_safe_elts_head h lv hs i j = ()

val mt_safe_elts_rec:
  h:HS.mem -> lv:uint32_t{lv < merkle_tree_size_lg} ->
  hs:hash_vv{V.size_of hs = merkle_tree_size_lg} ->
  i:index_t -> j:index_t{j >= i} ->
  Lemma (requires (mt_safe_elts h lv hs i j))
        (ensures (mt_safe_elts h (lv + 1ul) hs (i / 2ul) (j / 2ul)))
let mt_safe_elts_rec h lv hs i j = ()

val mt_safe_elts_init:
  h:HS.mem -> lv:uint32_t{lv <= merkle_tree_size_lg} ->
  hs:hash_vv{V.size_of hs = merkle_tree_size_lg} ->
  Lemma (requires (V.forall_ h hs lv (V.size_of hs)
                    (fun hv -> V.size_of hv = 0ul)))
        (ensures (mt_safe_elts h lv hs 0ul 0ul))
        (decreases (32 - U32.v lv))
let rec mt_safe_elts_init h lv hs =
  if lv = merkle_tree_size_lg then ()
  else mt_safe_elts_init h (lv + 1ul) hs

val mt_safe_elts_preserved:
  lv:uint32_t{lv <= merkle_tree_size_lg} ->
  hs:hash_vv{V.size_of hs = merkle_tree_size_lg} ->
  i:index_t -> j:index_t{j >= i} ->
  p:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (V.live h0 hs /\
                  mt_safe_elts h0 lv hs i j /\
                  loc_disjoint p (V.loc_vector_within hs lv (V.size_of hs)) /\
                  modifies p h0 h1))
        (ensures (mt_safe_elts h1 lv hs i j))
        (decreases (32 - U32.v lv))
        [SMTPat (V.live h0 hs);
        SMTPat (mt_safe_elts h0 lv hs i j);
        SMTPat (loc_disjoint p (RV.loc_rvector hs));
        SMTPat (modifies p h0 h1)]
let rec mt_safe_elts_preserved lv hs i j p h0 h1 =
  if lv = merkle_tree_size_lg then ()
  else (V.get_preserved hs lv p h0 h1;
       mt_safe_elts_preserved (lv + 1ul) hs (i / 2ul) (j / 2ul) p h0 h1)

val mt_safe: HS.mem -> mt_p -> GTot Type0
let mt_safe h mt =
  B.live h mt /\ B.freeable mt /\
  (let mtv = B.get h mt 0 in
  // Liveness & Accessibility
  RV.rv_inv h (MT?.hs mtv) /\
  RV.rv_inv h (MT?.rhs mtv) /\
  Rgl?.r_inv hreg h (MT?.mroot mtv) /\
  mt_safe_elts h 0ul (MT?.hs mtv) (MT?.i mtv) (MT?.j mtv) /\
  // Regionality
  HH.extends (V.frameOf (MT?.hs mtv)) (B.frameOf mt) /\
  HH.extends (V.frameOf (MT?.rhs mtv)) (B.frameOf mt) /\
  HH.extends (B.frameOf (MT?.mroot mtv)) (B.frameOf mt) /\
  HH.disjoint (V.frameOf (MT?.hs mtv)) (V.frameOf (MT?.rhs mtv)) /\
  HH.disjoint (V.frameOf (MT?.hs mtv)) (B.frameOf (MT?.mroot mtv)) /\
  HH.disjoint (V.frameOf (MT?.rhs mtv)) (B.frameOf (MT?.mroot mtv)))

val mt_loc: mt_p -> GTot loc
let mt_loc mt =
  B.loc_all_regions_from false (B.frameOf mt)

val mt_safe_preserved:
  mt:mt_p -> p:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (mt_safe h0 mt /\
                  loc_disjoint p (mt_loc mt) /\
                  modifies p h0 h1))
        (ensures (B.get h0 mt 0 == B.get h1 mt 0 /\
                 mt_safe h1 mt))
let mt_safe_preserved mt p h0 h1 =
  assert (loc_includes (mt_loc mt) (B.loc_buffer mt));
  let mtv = B.get h0 mt 0 in
  assert (loc_includes (mt_loc mt) (RV.loc_rvector (MT?.hs mtv)));
  assert (loc_includes (mt_loc mt) (RV.loc_rvector (MT?.rhs mtv)));
  assert (loc_includes (mt_loc mt) (V.loc_vector (MT?.hs mtv)));
  assert (loc_includes (mt_loc mt)
           (B.loc_all_regions_from false (B.frameOf (MT?.mroot mtv))));
  RV.rv_inv_preserved (MT?.hs mtv) p h0 h1;
  RV.rv_inv_preserved (MT?.rhs mtv) p h0 h1;
  Rgl?.r_sep hreg (MT?.mroot mtv) p h0 h1;
  V.loc_vector_within_included (MT?.hs mtv) 0ul (V.size_of (MT?.hs mtv));
  mt_safe_elts_preserved 0ul (MT?.hs mtv) (MT?.i mtv) (MT?.j mtv) p h0 h1

/// Lifting to a high-level Merkle tree structure

val mt_safe_elts_spec:
  h:HS.mem ->
  lv:uint32_t{lv <= merkle_tree_size_lg} ->
  hs:hash_vv{V.size_of hs = merkle_tree_size_lg} ->
  i:index_t ->
  j:index_t{j >= i} ->
  Lemma (requires (RV.rv_inv h hs /\
                  mt_safe_elts h lv hs i j))
        (ensures (High.mt_wf_elts
                   (U32.v lv) (RV.as_seq h hs)
                   (U32.v i) (U32.v j)))
        (decreases (32 - U32.v lv))
let rec mt_safe_elts_spec h lv hs i j =
  if lv = merkle_tree_size_lg then ()
  else mt_safe_elts_spec h (lv + 1ul) hs (i / 2ul) (j / 2ul)

val merkle_tree_lift:
  h:HS.mem ->
  mtv:merkle_tree{
    RV.rv_inv h (MT?.hs mtv) /\
    RV.rv_inv h (MT?.rhs mtv) /\
    Rgl?.r_inv hreg h (MT?.mroot mtv) /\
    mt_safe_elts h 0ul (MT?.hs mtv) (MT?.i mtv) (MT?.j mtv)} ->
  GTot High.wf_mt
let merkle_tree_lift h mtv =
  mt_safe_elts_spec h 0ul (MT?.hs mtv) (MT?.i mtv) (MT?.j mtv);
  High.MT (U32.v (MT?.i mtv))
    (U32.v (MT?.j mtv))
    (RV.as_seq h (MT?.hs mtv))
    (MT?.rhs_ok mtv)
    (RV.as_seq h (MT?.rhs mtv))
    (Rgl?.r_repr hreg h (MT?.mroot mtv))

val mt_lift:
  h:HS.mem -> mt:mt_p{mt_safe h mt} ->
  GTot High.wf_mt
let mt_lift h mt =
  merkle_tree_lift h (B.get h mt 0)

val mt_preserved:
  mt:mt_p -> p:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (mt_safe h0 mt /\
                  loc_disjoint p (mt_loc mt) /\
                  modifies p h0 h1))
        (ensures (mt_safe_preserved mt p h0 h1;
                 mt_lift h0 mt == mt_lift h1 mt))
let mt_preserved mt p h0 h1 =
  assert (loc_includes (B.loc_all_regions_from false (B.frameOf mt))
                       (B.loc_buffer mt));
  B.modifies_buffer_elim mt p h0 h1;
  assert (B.get h0 mt 0 == B.get h1 mt 0);
  assert (loc_includes (B.loc_all_regions_from false (B.frameOf mt))
                       (RV.loc_rvector (MT?.hs (B.get h0 mt 0))));
  assert (loc_includes (B.loc_all_regions_from false (B.frameOf mt))
                       (RV.loc_rvector (MT?.rhs (B.get h0 mt 0))));
  assert (loc_includes (B.loc_all_regions_from false (B.frameOf mt))
                       (B.loc_buffer (MT?.mroot (B.get h0 mt 0))));
  RV.as_seq_preserved (MT?.hs (B.get h0 mt 0)) p h0 h1;
  RV.as_seq_preserved (MT?.rhs (B.get h0 mt 0)) p h0 h1;
  B.modifies_buffer_elim (MT?.mroot (B.get h0 mt 0)) p h0 h1

/// Construction

// NOTE: the public function is `create_mt` defined below, which
// builds a tree with an initial hash.
private val create_empty_mt: r:erid ->
  HST.ST mt_p
   (requires (fun _ -> true))
   (ensures (fun h0 mt h1 ->
     // memory safety
     B.frameOf mt = r /\
     modifies (mt_loc mt) h0 h1 /\
     mt_safe h1 mt /\
     mt_not_full h1 mt /\
     // correctness
     mt_lift h1 mt == High.create_empty_mt ()))
#reset-options "--z3rlimit 100"
private let create_empty_mt r =
  let hs_region = RV.new_region_ r in
  let hs = RV.create_rid hvreg merkle_tree_size_lg hs_region in
  let h0 = HST.get () in
  assert (RV.as_seq h0 hs == S.create 32 S.empty);
  mt_safe_elts_init h0 0ul hs;
  let rhs_region = RV.new_region_ r in
  let rhs = RV.create_rid hreg merkle_tree_size_lg rhs_region in
  let h1 = HST.get () in
  assert (RV.as_seq h1 rhs == S.create 32 High.hash_init);
  RV.rv_inv_preserved hs (V.loc_vector rhs) h0 h1;
  RV.as_seq_preserved hs (V.loc_vector rhs) h0 h1;
  V.loc_vector_within_included hs 0ul (V.size_of hs);
  mt_safe_elts_preserved
    0ul hs 0ul 0ul (V.loc_vector rhs) h0 h1;
  let mroot_region = RV.new_region_ r in
  let mroot = Rgl?.r_init hreg mroot_region in
  let h2 = HST.get () in
  RV.as_seq_preserved hs loc_none h1 h2;
  RV.as_seq_preserved rhs loc_none h1 h2;
  mt_safe_elts_preserved 0ul hs 0ul 0ul loc_none h1 h2;
  let mt = B.malloc r (MT 0ul 0ul hs false rhs mroot) 1ul in
  let h3 = HST.get () in
  RV.as_seq_preserved hs loc_none h2 h3;
  RV.as_seq_preserved rhs loc_none h2 h3;
  Rgl?.r_sep hreg mroot loc_none h2 h3;
  mt_safe_elts_preserved 0ul hs 0ul 0ul loc_none h2 h3;
  mt

/// Destruction (free)

val free_mt: mt:mt_p ->
  HST.ST unit
   (requires (fun h0 -> mt_safe h0 mt))
   (ensures (fun h0 _ h1 -> modifies (mt_loc mt) h0 h1))
// This proof works with the resource limit above, but it's a bit slow.
// It will be admitted until the hint file is generated.
#reset-options "--admit_smt_queries true"
let free_mt mt =
  let mtv = !*mt in
  RV.free (MT?.hs mtv);
  RV.free (MT?.rhs mtv);
  Rgl?.r_free hreg (MT?.mroot mtv);
  B.free mt
#reset-options // reset "--admit_smt_queries true"

/// Insertion

#reset-options "--z3rlimit 40"
inline_for_extraction private val hash_vv_insert_copy:
  lv:uint32_t{lv < merkle_tree_size_lg} ->
  i:Ghost.erased index_t ->
  j:index_t{
    Ghost.reveal i <= j &&
    U32.v j < pow2 (32 - U32.v lv) - 1 &&
    j < U32.uint_to_t (UInt.max_int U32.n)} ->
  hs:hash_vv{V.size_of hs = merkle_tree_size_lg} ->
  v:hash ->
  HST.ST unit
    (requires (fun h0 ->
      RV.rv_inv h0 hs /\ 
      Rgl?.r_inv hreg h0 v /\
      HH.disjoint (V.frameOf hs) (B.frameOf v) /\
      mt_safe_elts h0 lv hs (Ghost.reveal i) j))
    (ensures (fun h0 _ h1 ->
      // memory safety
      modifies (loc_union
                 (RV.rs_loc_elem hvreg (V.as_seq h0 hs) (U32.v lv))
                 (V.loc_vector_within hs lv (lv + 1ul)))
               h0 h1 /\
      RV.rv_inv h1 hs /\
      Rgl?.r_inv hreg h1 v /\
      V.size_of (V.get h1 hs lv) == j + 1ul - offset_of (Ghost.reveal i) /\
      V.size_of (V.get h1 hs lv) == V.size_of (V.get h0 hs lv) + 1ul /\
      mt_safe_elts h1 (lv + 1ul) hs (Ghost.reveal i / 2ul) (j / 2ul) /\
      RV.rv_loc_elems h0 hs (lv + 1ul) (V.size_of hs) ==
      RV.rv_loc_elems h1 hs (lv + 1ul) (V.size_of hs) /\
      // correctness
      (mt_safe_elts_spec h0 lv hs (Ghost.reveal i) j;
      S.equal (RV.as_seq h1 hs)
      (High.hash_ss_insert
        (U32.v lv) (U32.v (Ghost.reveal i)) (U32.v j)
        (RV.as_seq h0 hs) (Rgl?.r_repr hreg h0 v))) /\
      S.equal (S.index (RV.as_seq h1 hs) (U32.v lv))
      (S.snoc (S.index (RV.as_seq h0 hs) (U32.v lv))
      (Rgl?.r_repr hreg h0 v))))
#reset-options "--z3rlimit 100"
inline_for_extraction private let hash_vv_insert_copy lv i j hs v =
  let hh0 = HST.get () in
  mt_safe_elts_rec hh0 lv hs (Ghost.reveal i) j;

  /// 1) Insert an element at the level `lv`, where the new vector is not yet
  /// connected to `hs`.
  let ihv = RV.insert_copy hcpy (V.index hs lv) v in
  let hh1 = HST.get () in

  // 1-0) Basic disjointness conditions
  V.forall2_forall_left hh0 hs 0ul (V.size_of hs) lv
    (fun b1 b2 -> HH.disjoint (Rgl?.region_of hvreg b1)
                              (Rgl?.region_of hvreg b2));
  V.forall2_forall_right hh0 hs 0ul (V.size_of hs) lv
    (fun b1 b2 -> HH.disjoint (Rgl?.region_of hvreg b1)
                              (Rgl?.region_of hvreg b2));
  V.loc_vector_within_included hs lv (lv + 1ul);
  V.loc_vector_within_included hs (lv + 1ul) (V.size_of hs);
  V.loc_vector_within_disjoint hs lv (lv + 1ul) (lv + 1ul) (V.size_of hs);

  // 1-1) For the `modifies` postcondition.
  assert (modifies (RV.rs_loc_elem hvreg (V.as_seq hh0 hs) (U32.v lv)) hh0 hh1);

  // 1-2) Preservation
  Rgl?.r_sep hreg v (RV.loc_rvector (V.get hh0 hs lv)) hh0 hh1;
  RV.rv_loc_elems_preserved
    hs (lv + 1ul) (V.size_of hs)
    (RV.loc_rvector (V.get hh0 hs lv)) hh0 hh1;

  // 1-3) For `mt_safe_elts`
  assert (V.size_of ihv == j + 1ul - offset_of (Ghost.reveal i)); // head updated
  mt_safe_elts_preserved
    (lv + 1ul) hs (Ghost.reveal i / 2ul) (j / 2ul)
    (RV.loc_rvector (V.get hh0 hs lv)) hh0 hh1; // tail not yet

  // 1-4) For the `rv_inv` postcondition
  RV.rs_loc_elems_elem_disj
    hvreg (V.as_seq hh0 hs) (V.frameOf hs)
    0 (U32.v (V.size_of hs)) 0 (U32.v lv) (U32.v lv);
  RV.rs_loc_elems_parent_disj
    hvreg (V.as_seq hh0 hs) (V.frameOf hs)
    0 (U32.v lv);
  RV.rv_elems_inv_preserved
    hs 0ul lv (RV.loc_rvector (V.get hh0 hs lv))
    hh0 hh1;
  assert (RV.rv_elems_inv hh1 hs 0ul lv);

  RV.rs_loc_elems_elem_disj
    hvreg (V.as_seq hh0 hs) (V.frameOf hs)
    0 (U32.v (V.size_of hs))
    (U32.v lv + 1) (U32.v (V.size_of hs))
    (U32.v lv);
  RV.rs_loc_elems_parent_disj
    hvreg (V.as_seq hh0 hs) (V.frameOf hs)
    (U32.v lv + 1) (U32.v (V.size_of hs));
  RV.rv_elems_inv_preserved
    hs (lv + 1ul) (V.size_of hs) (RV.loc_rvector (V.get hh0 hs lv))
    hh0 hh1;
  assert (RV.rv_elems_inv hh1 hs (lv + 1ul) (V.size_of hs));

  // assert (rv_itself_inv hh1 hs);
  // assert (elems_reg hh1 hs);

  // 1-5) Correctness
  assert (S.equal (RV.as_seq hh1 ihv)
                  (S.snoc (RV.as_seq hh0 (V.get hh0 hs lv)) (Rgl?.r_repr hreg hh0 v)));

  /// 2) Assign the updated vector to `hs` at the level `lv`.
  RV.assign hs lv ihv;
  let hh2 = HST.get () in

  // 2-1) For the `modifies` postcondition.
  assert (modifies (V.loc_vector_within hs lv (lv + 1ul)) hh1 hh2);
  assert (modifies (loc_union
                     (RV.rs_loc_elem hvreg (V.as_seq hh0 hs) (U32.v lv))
                     (V.loc_vector_within hs lv (lv + 1ul))) hh0 hh2);

  // 2-2) Preservation
  Rgl?.r_sep hreg v (RV.loc_rvector hs) hh1 hh2;
  RV.rv_loc_elems_preserved
    hs (lv + 1ul) (V.size_of hs)
    (V.loc_vector_within hs lv (lv + 1ul)) hh1 hh2;

  // 2-3) For `mt_safe_elts`
  assert (V.size_of (V.get hh2 hs lv) == j + 1ul - offset_of (Ghost.reveal i));
  mt_safe_elts_preserved
    (lv + 1ul) hs (Ghost.reveal i / 2ul) (j / 2ul)
    (V.loc_vector_within hs lv (lv + 1ul)) hh1 hh2;

  // 2-4) Correctness
  RV.as_seq_sub_preserved hs 0ul lv (loc_rvector ihv) hh0 hh1;
  RV.as_seq_sub_preserved hs (lv + 1ul) merkle_tree_size_lg (loc_rvector ihv) hh0 hh1;
  assert (S.equal (RV.as_seq hh2 hs)
                  (S.append
                    (RV.as_seq_sub hh0 hs 0ul lv)
                    (S.cons (RV.as_seq hh1 ihv)
                            (RV.as_seq_sub hh0 hs (lv + 1ul) merkle_tree_size_lg))));
  assume (S.equal (RV.as_seq hh2 hs)
                  (S.upd (RV.as_seq hh0 hs) (U32.v lv) (RV.as_seq hh1 ihv)))

private val insert_index_helper_even:
  lv:uint32_t{lv < merkle_tree_size_lg} ->
  j:index_t{U32.v j < pow2 (32 - U32.v lv) - 1} ->
  Lemma (requires (j % 2ul <> 1ul))
        (ensures (U32.v j % 2 <> 1 /\ j / 2ul == (j + 1ul) / 2ul))
private let insert_index_helper_even lv j = ()

private val insert_index_helper_odd:
  lv:uint32_t{lv < merkle_tree_size_lg} ->
  i:index_t ->
  j:index_t{i <= j && U32.v j < pow2 (32 - U32.v lv) - 1} ->
  Lemma (requires (j % 2ul = 1ul /\
                  j < U32.uint_to_t (UInt.max_int U32.n)))
        (ensures (U32.v j % 2 = 1 /\
                 U32.v (j / 2ul) < pow2 (32 - U32.v (lv + 1ul)) - 1 /\
                 (j + 1ul) / 2ul == j / 2ul + 1ul /\
                 j - offset_of i > 0ul))
private let insert_index_helper_odd lv i j = ()

private val insert_modifies_rec_helper:
  lv:uint32_t{lv < merkle_tree_size_lg} ->
  hs:hash_vv{V.size_of hs = merkle_tree_size_lg} ->
  aloc:loc ->
  h:HS.mem ->
  Lemma (loc_union
          (loc_union
            (loc_union
              (RV.rs_loc_elem hvreg (V.as_seq h hs) (U32.v lv))
              (V.loc_vector_within hs lv (lv + 1ul)))
            aloc)
          (loc_union
            (loc_union
              (RV.rv_loc_elems h hs (lv + 1ul) (V.size_of hs))
              (V.loc_vector_within hs (lv + 1ul) (V.size_of hs)))
            aloc) ==
          loc_union
            (loc_union
              (RV.rv_loc_elems h hs lv (V.size_of hs))
              (V.loc_vector_within hs lv (V.size_of hs)))
            aloc)
private let insert_modifies_rec_helper lv hs aloc h =
  admit ()

private val insert_modifies_union_loc_weakening:
  l1:loc -> l2:loc -> l3:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (modifies l1 h0 h1))
        (ensures (modifies (loc_union (loc_union l1 l2) l3) h0 h1))
private let insert_modifies_union_loc_weakening l1 l2 l3 h0 h1 =
  B.loc_includes_union_l l1 l2 l1;
  B.loc_includes_union_l (loc_union l1 l2) l3 (loc_union l1 l2)

private val insert_snoc_last_helper:
  #a:Type -> s:S.seq a{S.length s > 0} -> v:a ->
  Lemma (S.index (S.snoc s v) (S.length s - 1) == S.last s)
private let insert_snoc_last_helper #a s v = ()

// TODO: better to move to `Low.Rvector.fst`
private val rv_inv_rv_elems_reg:
  #a:Type0 -> #rg:regional a ->
  h:HS.mem -> rv:rvector rg ->
  i:uint32_t -> j:uint32_t{i <= j && j <= V.size_of rv} ->
  Lemma (requires (RV.rv_inv h rv))
        (ensures (RV.rv_elems_reg h rv i j))
private let rv_inv_rv_elems_reg #a #rg h rv i j = ()

private val insert_:
  lv:uint32_t{lv < merkle_tree_size_lg} ->
  i:Ghost.erased index_t ->
  j:index_t{
    Ghost.reveal i <= j &&
    U32.v j < pow2 (32 - U32.v lv) - 1 &&
    j < U32.uint_to_t (UInt.max_int U32.n)} ->
  hs:hash_vv{V.size_of hs = merkle_tree_size_lg} ->
  acc:hash ->
  HST.ST unit
         (requires (fun h0 ->
           RV.rv_inv h0 hs /\ 
           Rgl?.r_inv hreg h0 acc /\
           HH.disjoint (V.frameOf hs) (B.frameOf acc) /\
           mt_safe_elts h0 lv hs (Ghost.reveal i) j))
         (ensures (fun h0 _ h1 ->
           // memory safety
           modifies (loc_union
                      (loc_union
                        (RV.rv_loc_elems h0 hs lv (V.size_of hs))
                        (V.loc_vector_within hs lv (V.size_of hs)))
                      (B.loc_all_regions_from false (B.frameOf acc)))
                    h0 h1 /\
           RV.rv_inv h1 hs /\
           Rgl?.r_inv hreg h1 acc /\
           mt_safe_elts h1 lv hs (Ghost.reveal i) (j + 1ul) /\
           // correctness
           (mt_safe_elts_spec h0 lv hs (Ghost.reveal i) j;
           S.equal (RV.as_seq h1 hs)
                   (High.insert_ (U32.v lv) (U32.v (Ghost.reveal i)) (U32.v j)
                     (RV.as_seq h0 hs) (Rgl?.r_repr hreg h0 acc)))))
         (decreases (U32.v j))
// #reset-options "--z3rlimit 800"
// This proof works with the resource limit above, but it's a bit slow.
// It will be admitted until the hint file is generated.
#reset-options "--admit_smt_queries true"
private let rec insert_ lv i j hs acc =
  let hh0 = HST.get () in
  hash_vv_insert_copy lv i j hs acc;
  let hh1 = HST.get () in

  // Base conditions
  V.loc_vector_within_included hs lv (lv + 1ul);
  V.loc_vector_within_included hs (lv + 1ul) (V.size_of hs);
  V.loc_vector_within_disjoint hs lv (lv + 1ul) (lv + 1ul) (V.size_of hs);
  
  assert (V.size_of (V.get hh1 hs lv) == j + 1ul - offset_of (Ghost.reveal i));
  assert (mt_safe_elts hh1 (lv + 1ul) hs (Ghost.reveal i / 2ul) (j / 2ul));

  if j % 2ul = 1ul
  then (insert_index_helper_odd lv (Ghost.reveal i) j;
       assert (S.length (S.index (RV.as_seq hh0 hs) (U32.v lv)) > 0);
       let lvhs = V.index hs lv in
       assert (U32.v (V.size_of lvhs) ==
              S.length (S.index (RV.as_seq hh0 hs) (U32.v lv)) + 1);
       assert (V.size_of lvhs > 1ul);

       /// 3) Update the accumulator `acc`.
       hash_vec_rv_inv_r_inv hh1 (V.get hh1 hs lv) (V.size_of (V.get hh1 hs lv) - 2ul);
       assert (Rgl?.r_inv hreg hh1 acc);
       hash_2 (V.index lvhs (V.size_of lvhs - 2ul)) acc acc;
       let hh2 = HST.get () in

       // 3-1) For the `modifies` postcondition
       assert (modifies (B.loc_all_regions_from false (B.frameOf acc)) hh1 hh2);
       assert (modifies
                (loc_union
                  (loc_union
                    (RV.rs_loc_elem hvreg (V.as_seq hh0 hs) (U32.v lv))
                    (V.loc_vector_within hs lv (lv + 1ul)))
                  (B.loc_all_regions_from false (B.frameOf acc)))
                hh0 hh2);

       // 3-2) Preservation
       RV.rv_inv_preserved
         hs (B.loc_region_only false (B.frameOf acc)) hh1 hh2;
       RV.as_seq_preserved
         hs (B.loc_region_only false (B.frameOf acc)) hh1 hh2;
       RV.rv_loc_elems_preserved
         hs (lv + 1ul) (V.size_of hs)
         (B.loc_region_only false (B.frameOf acc)) hh1 hh2;
       assert (RV.rv_inv hh2 hs);
       assert (Rgl?.r_inv hreg hh2 acc);

       // 3-3) For `mt_safe_elts`
       V.get_preserved hs lv
         (B.loc_region_only false (B.frameOf acc)) hh1 hh2; // head preserved
       mt_safe_elts_preserved
         (lv + 1ul) hs (Ghost.reveal i / 2ul) (j / 2ul)
         (B.loc_region_only false (B.frameOf acc)) hh1 hh2; // tail preserved

       // 3-4) Correctness
       insert_snoc_last_helper
         (RV.as_seq hh0 (V.get hh0 hs lv))
         (Rgl?.r_repr hreg hh0 acc);
       assert (S.equal (Rgl?.r_repr hreg hh2 acc) // `nacc` in `High.insert_`
                       (High.hash_2
                         (S.last (S.index (RV.as_seq hh0 hs) (U32.v lv)))
                         (Rgl?.r_repr hreg hh0 acc)));

       /// 4) Recursion
       insert_ (lv + 1ul)
         (Ghost.hide (Ghost.reveal i / 2ul)) (j / 2ul)
         hs acc;
       let hh3 = HST.get () in

       // 4-0) Memory safety brought from the postcondition of the recursion
       assert (RV.rv_inv hh3 hs);
       assert (Rgl?.r_inv hreg hh3 acc);
       assert (modifies (loc_union
                          (loc_union
                            (RV.rv_loc_elems hh0 hs (lv + 1ul) (V.size_of hs))
                            (V.loc_vector_within hs (lv + 1ul) (V.size_of hs)))
                          (B.loc_all_regions_from false (B.frameOf acc)))
                        hh2 hh3);
       assert (modifies
                (loc_union
                  (loc_union
                    (loc_union
                      (RV.rs_loc_elem hvreg (V.as_seq hh0 hs) (U32.v lv))
                      (V.loc_vector_within hs lv (lv + 1ul)))
                    (B.loc_all_regions_from false (B.frameOf acc)))
                  (loc_union
                    (loc_union
                      (RV.rv_loc_elems hh0 hs (lv + 1ul) (V.size_of hs))
                      (V.loc_vector_within hs (lv + 1ul) (V.size_of hs)))
                    (B.loc_all_regions_from false (B.frameOf acc))))
                hh0 hh3);

       // 4-1) For `mt_safe_elts`
       rv_inv_rv_elems_reg hh2 hs (lv + 1ul) (V.size_of hs);
       RV.rv_loc_elems_included hh2 hs (lv + 1ul) (V.size_of hs);
       assert (loc_disjoint
                (V.loc_vector_within hs lv (lv + 1ul))
                (RV.rv_loc_elems hh2 hs (lv + 1ul) (V.size_of hs)));
       assert (loc_disjoint
                (V.loc_vector_within hs lv (lv + 1ul))
                (B.loc_all_regions_from false (B.frameOf acc)));
       V.get_preserved hs lv
         (loc_union
           (loc_union
             (V.loc_vector_within hs (lv + 1ul) (V.size_of hs))
             (RV.rv_loc_elems hh2 hs (lv + 1ul) (V.size_of hs)))
           (B.loc_all_regions_from false (B.frameOf acc)))
         hh2 hh3;

       assert (V.size_of (V.get hh3 hs lv) ==
              j + 1ul - offset_of (Ghost.reveal i)); // head preserved
       assert (mt_safe_elts hh3 (lv + 1ul) hs
                (Ghost.reveal i / 2ul) (j / 2ul + 1ul)); // tail by recursion
       mt_safe_elts_constr hh3 lv hs (Ghost.reveal i) (j + 1ul);
       assert (mt_safe_elts hh3 lv hs (Ghost.reveal i) (j + 1ul));

       // 4-2) Correctness
       mt_safe_elts_spec hh2 (lv + 1ul) hs (Ghost.reveal i / 2ul) (j / 2ul);
       assert (S.equal (RV.as_seq hh3 hs)
       (High.insert_ (U32.v lv + 1) (U32.v (Ghost.reveal i) / 2) (U32.v j / 2)
         (RV.as_seq hh2 hs) (Rgl?.r_repr hreg hh2 acc)));
       mt_safe_elts_spec hh0 lv hs (Ghost.reveal i) j;
       High.insert_rec (U32.v lv) (U32.v (Ghost.reveal i)) (U32.v j)
         (RV.as_seq hh0 hs) (Rgl?.r_repr hreg hh0 acc);
       assert (S.equal (RV.as_seq hh3 hs)
       (High.insert_ (U32.v lv) (U32.v (Ghost.reveal i)) (U32.v j)
         (RV.as_seq hh0 hs) (Rgl?.r_repr hreg hh0 acc))))
  else (insert_index_helper_even lv j;
       // memory safety
       assert (mt_safe_elts hh1 (lv + 1ul) hs (Ghost.reveal i / 2ul) ((j + 1ul) / 2ul));
       mt_safe_elts_constr hh1 lv hs (Ghost.reveal i) (j + 1ul);
       assert (mt_safe_elts hh1 lv hs (Ghost.reveal i) (j + 1ul));
       assert (modifies
                (loc_union
                  (RV.rs_loc_elem hvreg (V.as_seq hh0 hs) (U32.v lv))
                  (V.loc_vector_within hs lv (lv + 1ul)))
                hh0 hh1);
       insert_modifies_union_loc_weakening
         (loc_union
           (RV.rs_loc_elem hvreg (V.as_seq hh0 hs) (U32.v lv))
           (V.loc_vector_within hs lv (lv + 1ul)))
         (B.loc_all_regions_from false (B.frameOf acc))
         (loc_union
           (loc_union
             (RV.rv_loc_elems hh0 hs (lv + 1ul) (V.size_of hs))
             (V.loc_vector_within hs (lv + 1ul) (V.size_of hs)))
           (B.loc_all_regions_from false (B.frameOf acc)))
         hh0 hh1;
       // correctness
       mt_safe_elts_spec hh0 lv hs (Ghost.reveal i) j;
       High.insert_base (U32.v lv) (U32.v (Ghost.reveal i)) (U32.v j)
         (RV.as_seq hh0 hs) (Rgl?.r_repr hreg hh0 acc);
       assert (S.equal (RV.as_seq hh1 hs)
              (High.insert_ (U32.v lv) (U32.v (Ghost.reveal i)) (U32.v j)
                (RV.as_seq hh0 hs) (Rgl?.r_repr hreg hh0 acc))));

  /// 5) Proving the postcondition after recursion
  let hh4 = HST.get () in

  // 5-1) For the `modifies` postcondition.
  assert (modifies
           (loc_union
             (loc_union
               (loc_union
                 (RV.rs_loc_elem hvreg (V.as_seq hh0 hs) (U32.v lv))
                 (V.loc_vector_within hs lv (lv + 1ul)))
               (B.loc_all_regions_from false (B.frameOf acc)))
             (loc_union
               (loc_union
                 (RV.rv_loc_elems hh0 hs (lv + 1ul) (V.size_of hs))
                 (V.loc_vector_within hs (lv + 1ul) (V.size_of hs)))
               (B.loc_all_regions_from false (B.frameOf acc))))
           hh0 hh4);
  insert_modifies_rec_helper
    lv hs (B.loc_all_regions_from false (B.frameOf acc)) hh0;

  // 5-2) For `mt_safe_elts`
  assert (mt_safe_elts hh4 lv hs (Ghost.reveal i) (j + 1ul));

  // 5-3) Preservation
  assert (RV.rv_inv hh4 hs);
  assert (Rgl?.r_inv hreg hh4 acc);

  // 5-4) Correctness
  mt_safe_elts_spec hh0 lv hs (Ghost.reveal i) j;
  assert (S.equal (RV.as_seq hh4 hs)
                  (High.insert_ (U32.v lv) (U32.v (Ghost.reveal i)) (U32.v j)
                    (RV.as_seq hh0 hs) (Rgl?.r_repr hreg hh0 acc))) // QED
#reset-options // reset "--admit_smt_queries true"

// Caution: current impl. manipulates the content in `v`.
val mt_insert:
  mt:mt_p -> v:hash ->
  HST.ST unit
   (requires (fun h0 ->
     mt_not_full h0 mt /\
     mt_safe h0 mt /\
     Rgl?.r_inv hreg h0 v /\
     HH.disjoint (B.frameOf mt) (B.frameOf v)))
   (ensures (fun h0 _ h1 ->
     // memory safety
     modifies (loc_union
                (mt_loc mt)
                (B.loc_all_regions_from false (B.frameOf v)))
              h0 h1 /\
     mt_safe h1 mt /\
     // correctness
     mt_lift h1 mt == High.mt_insert (mt_lift h0 mt) (Rgl?.r_repr hreg h0 v)))
#reset-options "--z3rlimit 40 --max_fuel 0"
let mt_insert mt v =
  let hh0 = HST.get () in
  let mtv = !*mt in
  let hs = MT?.hs mtv in
  insert_ 0ul (Ghost.hide (MT?.i mtv)) (MT?.j mtv) hs v;
  let hh1 = HST.get () in
  RV.rv_loc_elems_included hh0 (MT?.hs mtv) 0ul (V.size_of hs);
  V.loc_vector_within_included hs 0ul (V.size_of hs);
  RV.rv_inv_preserved
    (MT?.rhs mtv)
    (loc_union
      (loc_union
        (RV.rv_loc_elems hh0 hs 0ul (V.size_of hs))
        (V.loc_vector_within hs 0ul (V.size_of hs)))
      (B.loc_all_regions_from false (B.frameOf v)))
    hh0 hh1;
  RV.as_seq_preserved
    (MT?.rhs mtv)
    (loc_union
      (loc_union
        (RV.rv_loc_elems hh0 hs 0ul (V.size_of hs))
        (V.loc_vector_within hs 0ul (V.size_of hs)))
      (B.loc_all_regions_from false (B.frameOf v)))
    hh0 hh1;
  Rgl?.r_sep hreg (MT?.mroot mtv)
    (loc_union
      (loc_union
        (RV.rv_loc_elems hh0 hs 0ul (V.size_of hs))
        (V.loc_vector_within hs 0ul (V.size_of hs)))
      (B.loc_all_regions_from false (B.frameOf v)))
    hh0 hh1;
  mt *= MT (MT?.i mtv)
           (MT?.j mtv + 1ul)
           (MT?.hs mtv)
           false // `rhs` is always deprecated right after an insertion.
           (MT?.rhs mtv)
           (MT?.mroot mtv);
  let hh2 = HST.get () in
  RV.rv_inv_preserved
    (MT?.hs mtv) (B.loc_buffer mt) hh1 hh2;
  RV.rv_inv_preserved
    (MT?.rhs mtv) (B.loc_buffer mt) hh1 hh2;
  RV.as_seq_preserved
    (MT?.hs mtv) (B.loc_buffer mt) hh1 hh2;
  RV.as_seq_preserved
    (MT?.rhs mtv) (B.loc_buffer mt) hh1 hh2;
  Rgl?.r_sep hreg (MT?.mroot mtv) (B.loc_buffer mt) hh1 hh2;
  mt_safe_elts_preserved
    0ul (MT?.hs mtv) (MT?.i mtv) (MT?.j mtv + 1ul) (B.loc_buffer mt)
    hh1 hh2
#reset-options // reset "--max_fuel 0"

val create_mt: r:erid -> init:hash ->
  HST.ST mt_p
   (requires (fun h0 ->
     Rgl?.r_inv hreg h0 init /\
     HH.disjoint r (B.frameOf init)))
   (ensures (fun h0 mt h1 ->
     // memory safety
     modifies (loc_union
                (mt_loc mt)
                (B.loc_all_regions_from false (B.frameOf init)))
              h0 h1 /\
     mt_safe h1 mt /\
     // correctness
     mt_lift h1 mt == High.create_mt (Rgl?.r_repr hreg h0 init)))
#reset-options "--z3rlimit 40"
let create_mt r init =
  let hh0 = HST.get () in
  let mt = create_empty_mt r in
  mt_insert mt init;
  let hh2 = HST.get () in
  mt

/// Construction and Destruction of paths

type path = B.pointer (V.vector hash)

val path_safe:
  HS.mem -> mtr:HH.rid -> path -> GTot Type0
let path_safe h mtr p =
  B.live h p /\ B.freeable p /\
  V.live h (B.get h p 0) /\ V.freeable (B.get h p 0) /\
  HST.is_eternal_region (V.frameOf (B.get h p 0)) /\
  V.forall_all h (B.get h p 0)
    (fun hp -> Rgl?.r_inv hreg h hp /\
               HH.includes mtr (B.frameOf hp)) /\
  HH.extends (V.frameOf (B.get h p 0)) (B.frameOf p) /\
  HH.disjoint mtr (B.frameOf p)

val path_loc: path -> GTot loc
let path_loc p =
  B.loc_all_regions_from false (B.frameOf p)

val lift_path_:
  h:HS.mem -> 
  p:S.seq hash{V.forall_seq p 0 (S.length p) (fun hp -> Rgl?.r_inv hreg h hp)} ->
  GTot (hp:High.path{S.length hp = S.length p}) (decreases (S.length p))
let rec lift_path_ h p =
  if S.length p = 0 then S.empty
  else (S.cons (Rgl?.r_repr hreg h (S.head p))
               (lift_path_ h (S.tail p)))

val lift_path:
  h:HS.mem -> mtr:HH.rid -> p:path{path_safe h mtr p} ->
  GTot (hp:High.path{S.length hp = U32.v (V.size_of (B.get h p 0))})
let lift_path h mtr p =
  lift_path_ h (V.as_seq h (B.get h p 0))

private val path_safe_preserved_:
  mtr:HH.rid -> hvec:V.vector hash -> dl:loc ->
  i:index_t -> j:index_t{i <= j && j <= V.size_of hvec} ->
  h:HS.mem -> h0:HS.mem -> h1:HS.mem ->
  Lemma
    (requires (V.forall_ h hvec i j
                (fun hp ->
                  Rgl?.r_inv hreg h0 hp /\
                  HH.includes mtr (B.frameOf hp)) /\
              loc_disjoint dl (B.loc_all_regions_from false mtr) /\
              modifies dl h0 h1))
    (ensures (V.forall_ h hvec i j
               (fun hp ->
                 Rgl?.r_inv hreg h1 hp /\
                 HH.includes mtr (B.frameOf hp))))
    (decreases (U32.v j))
private let rec path_safe_preserved_ mtr hvec dl i j h h0 h1 =
  if i = j then ()
  else (assert (loc_includes
                 (B.loc_all_regions_from false mtr)
                 (B.loc_all_regions_from false
                   (B.frameOf (V.get h hvec (j - 1ul)))));
       Rgl?.r_sep hreg (V.get h hvec (j - 1ul)) dl h0 h1;
       path_safe_preserved_ mtr hvec dl i (j - 1ul) h h0 h1)

val path_safe_preserved:
  mtr:HH.rid -> p:path ->
  dl:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (path_safe h0 mtr p /\
                  loc_disjoint dl (path_loc p) /\
                  loc_disjoint dl (B.loc_all_regions_from false mtr) /\
                  modifies dl h0 h1))
        (ensures (path_safe h1 mtr p))
let path_safe_preserved mtr p dl h0 h1 =
  assert (loc_includes (path_loc p) (B.loc_buffer p));
  assert (loc_includes (path_loc p) (V.loc_vector (B.get h0 p 0)));
  path_safe_preserved_
    mtr (B.get h0 p 0) dl 0ul (V.size_of (B.get h0 p 0))
    h0 h0 h1

val path_safe_init_preserved:
  mtr:HH.rid -> p:path ->
  dl:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (path_safe h0 mtr p /\
                  V.size_of (B.get h0 p 0) = 0ul /\
                  B.loc_disjoint dl (path_loc p) /\
                  modifies dl h0 h1))
        (ensures (path_safe h1 mtr p /\
                 V.size_of (B.get h1 p 0) = 0ul))
let path_safe_init_preserved mtr p dl h0 h1 =
  assert (loc_includes (path_loc p) (B.loc_buffer p));
  assert (loc_includes (path_loc p) (V.loc_vector (B.get h0 p 0)))

// val path_preserved_:
//   p:S.seq hash -> dl:loc -> h0:HS.mem -> h1:HS.mem ->
//   Lemma (requires (V.forall_seq p 0 (S.length p)
//                     (fun hp -> Rgl?.r_inv hreg h hp /\
//                                HH.includes mtr (B.frameOf hp)) /\
//                   loc_disjoint dl (B.loc_all_regions_from false mtr) /\
//                   modifies dl h0 h1))
//         (ensures (path_safe_preserved mtr p dl h0 h1;
//                  S.equal (lift_path h0 mtr p) (lift_path h1 mtr p)))
// let path_preserved mtr p dl h0 h1 =

val path_preserved:
  mtr:HH.rid -> p:path ->
  dl:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (path_safe h0 mtr p /\
                  loc_disjoint dl (path_loc p) /\
                  loc_disjoint dl (B.loc_all_regions_from false mtr) /\
                  modifies dl h0 h1))
        (ensures (path_safe_preserved mtr p dl h0 h1;
                 S.equal (lift_path h0 mtr p) (lift_path h1 mtr p)))
let path_preserved mtr p dl h0 h1 =
  admit () // So trivial

val init_path:
  mtr:HH.rid -> r:erid ->
  HST.ST path
    (requires (fun h0 -> HH.disjoint mtr r))
    (ensures (fun h0 p h1 ->
      // memory safety
      path_safe h1 mtr p /\
      // correctness
      S.equal (lift_path h1 mtr p) S.empty))
let init_path mtr r =
  let nrid = RV.new_region_ r in
  B.malloc r (hash_vec_r_init nrid) 1ul

val clear_path:
  mtr:HH.rid -> p:path ->
  HST.ST unit
    (requires (fun h0 -> path_safe h0 mtr p))
    (ensures (fun h0 _ h1 ->
      // memory safety
      path_safe h1 mtr p /\
      // correctness
      V.size_of (B.get h1 p 0) = 0ul /\
      S.equal (lift_path h1 mtr p) S.empty))
let clear_path mtr p =
  p *= V.clear !*p

val free_path:
  p:path ->
  HST.ST unit
    (requires (fun h0 ->
      B.live h0 p /\ B.freeable p /\
      V.live h0 (B.get h0 p 0) /\ V.freeable (B.get h0 p 0) /\
      HH.extends (V.frameOf (B.get h0 p 0)) (B.frameOf p)))
    (ensures (fun h0 _ h1 ->
      modifies (path_loc p) h0 h1))
let free_path p =
  V.free !*p;
  B.free p

/// Getting the Merkle root and path

// Construct the rightmost hashes for a given (incomplete) Merkle tree.
// This function calculates the Merkle root as well, which is the final
// accumulator value.
private val construct_rhs:
  lv:uint32_t{lv <= merkle_tree_size_lg} ->
  hs:hash_vv{V.size_of hs = merkle_tree_size_lg} ->
  rhs:hash_vec{V.size_of rhs = merkle_tree_size_lg} ->
  i:index_t ->
  j:index_t{i <= j && U32.v j < pow2 (32 - U32.v lv)} ->
  acc:hash ->
  actd:bool ->
  HST.ST unit
   (requires (fun h0 ->
     RV.rv_inv h0 hs /\ RV.rv_inv h0 rhs /\
     HH.disjoint (V.frameOf hs) (V.frameOf rhs) /\
     Rgl?.r_inv hreg h0 acc /\
     HH.disjoint (B.frameOf acc) (V.frameOf hs) /\
     HH.disjoint (B.frameOf acc) (V.frameOf rhs) /\
     mt_safe_elts h0 lv hs i j))
   (ensures (fun h0 _ h1 ->
     // memory safety
     modifies (loc_union
                (RV.loc_rvector rhs)
                (B.loc_all_regions_from false (B.frameOf acc)))
              h0 h1 /\
     RV.rv_inv h1 rhs /\
     Rgl?.r_inv hreg h1 acc /\
     // correctness
     (mt_safe_elts_spec h0 lv hs i j;
     High.construct_rhs
       (U32.v lv)
       (Rgl?.r_repr hvvreg h0 hs)
       (Rgl?.r_repr hvreg h0 rhs)
       (U32.v i) (U32.v j)
       (Rgl?.r_repr hreg h0 acc) actd ==
     (Rgl?.r_repr hvreg h1 rhs, Rgl?.r_repr hreg h1 acc))))
   (decreases (U32.v j))
// #reset-options "--z3rlimit 400 --max_fuel 1"
// This proof works with the resource limit above, but it's a bit slow.
// It will be admitted until the hint file is generated.
#reset-options "--admit_smt_queries true"
private let rec construct_rhs lv hs rhs i j acc actd =
  let hh0 = HST.get () in
  let ofs = offset_of i in
  let copy = Cpy?.copy hcpy in

  if j = 0ul then ()
  else
    (if j % 2ul = 0ul
    then begin
      Math.Lemmas.pow2_double_mult (32 - U32.v lv - 1);
      mt_safe_elts_rec hh0 lv hs i j;
      construct_rhs (lv + 1ul) hs rhs (i / 2ul) (j / 2ul) acc actd;
      let hh1 = HST.get () in
      // correctness
      mt_safe_elts_spec hh0 lv hs i j;
      High.construct_rhs_even
        (U32.v lv) (Rgl?.r_repr hvvreg hh0 hs) (Rgl?.r_repr hvreg hh0 rhs)
        (U32.v i) (U32.v j) (Rgl?.r_repr hreg hh0 acc) actd;
      assert (High.construct_rhs
               (U32.v lv)
               (Rgl?.r_repr hvvreg hh0 hs)
               (Rgl?.r_repr hvreg hh0 rhs)
               (U32.v i) (U32.v j)
               (Rgl?.r_repr hreg hh0 acc)
               actd ==
             (Rgl?.r_repr hvreg hh1 rhs, Rgl?.r_repr hreg hh1 acc))
    end

    else begin
      if actd
      then begin
        RV.assign_copy hcpy rhs lv acc;
        let hh1 = HST.get () in
        // memory safety
        Rgl?.r_sep hreg acc
          (B.loc_all_regions_from false (V.frameOf rhs)) hh0 hh1;
        RV.rv_inv_preserved
          hs (B.loc_all_regions_from false (V.frameOf rhs))
          hh0 hh1;
        RV.as_seq_preserved
          hs (B.loc_all_regions_from false (V.frameOf rhs))
          hh0 hh1;
        RV.rv_inv_preserved
          (V.index hs lv) (B.loc_all_regions_from false (V.frameOf rhs))
          hh0 hh1;
        V.loc_vector_within_included hs lv (V.size_of hs);
        mt_safe_elts_preserved lv hs i j
          (B.loc_all_regions_from false (V.frameOf rhs))
          hh0 hh1;
        mt_safe_elts_head hh1 lv hs i j;
        hash_vv_rv_inv_r_inv hh1 hs lv (j - 1ul - ofs);

        // correctness
        assert (S.equal (RV.as_seq hh1 rhs)
                        (S.upd (RV.as_seq hh0 rhs) (U32.v lv)
                               (Rgl?.r_repr hreg hh0 acc)));

        hash_2 (V.index (V.index hs lv) (j - 1ul - ofs)) acc acc;
        let hh2 = HST.get () in
        // memory safety
        mt_safe_elts_preserved lv hs i j
          (B.loc_all_regions_from false (B.frameOf acc)) hh1 hh2;
        RV.rv_inv_preserved
          hs (B.loc_region_only false (B.frameOf acc)) hh1 hh2;
        RV.rv_inv_preserved
          rhs (B.loc_region_only false (B.frameOf acc)) hh1 hh2;
        RV.as_seq_preserved
          hs (B.loc_region_only false (B.frameOf acc)) hh1 hh2;
        RV.as_seq_preserved
          rhs (B.loc_region_only false (B.frameOf acc)) hh1 hh2;

        // correctness
        hash_vv_as_seq_get_index hh0 hs lv (j - 1ul - ofs);
        assert (Rgl?.r_repr hreg hh2 acc ==
               High.hash_2 (S.index (S.index (RV.as_seq hh0 hs) (U32.v lv))
                                    (U32.v j - 1 - U32.v ofs))
                           (Rgl?.r_repr hreg hh0 acc))
      end

      else begin
        mt_safe_elts_head hh0 lv hs i j;
        hash_vv_rv_inv_r_inv hh0 hs lv (j - 1ul - ofs);
        hash_vv_rv_inv_disjoint hh0 hs lv (j - 1ul - ofs) (B.frameOf acc);
        copy (V.index (V.index hs lv) (j - 1ul - ofs)) acc;
        let hh1 = HST.get () in
        // memory safety
        V.loc_vector_within_included hs lv (V.size_of hs);
        mt_safe_elts_preserved lv hs i j
          (B.loc_all_regions_from false (B.frameOf acc)) hh0 hh1;
        RV.rv_inv_preserved
          hs (B.loc_all_regions_from false (B.frameOf acc)) hh0 hh1;
        RV.rv_inv_preserved
          rhs (B.loc_all_regions_from false (B.frameOf acc)) hh0 hh1;
        RV.as_seq_preserved
          hs (B.loc_all_regions_from false (B.frameOf acc)) hh0 hh1;
        RV.as_seq_preserved
          rhs (B.loc_all_regions_from false (B.frameOf acc)) hh0 hh1;

        // correctness
        hash_vv_as_seq_get_index hh0 hs lv (j - 1ul - ofs);
        assert (Rgl?.r_repr hreg hh1 acc ==
                 S.index (S.index (RV.as_seq hh0 hs) (U32.v lv))
                         (U32.v j - 1 - U32.v ofs))
      end;
      let hh3 = HST.get () in
      assert (S.equal (RV.as_seq hh3 hs) (RV.as_seq hh0 hs));
      assert (S.equal (RV.as_seq hh3 rhs)
                      (if actd
                      then S.upd (RV.as_seq hh0 rhs) (U32.v lv)
                                 (Rgl?.r_repr hreg hh0 acc)
                      else RV.as_seq hh0 rhs));
      assert (Rgl?.r_repr hreg hh3 acc ==
             (if actd
             then High.hash_2 (S.index (S.index (RV.as_seq hh0 hs) (U32.v lv))
                                       (U32.v j - 1 - U32.v ofs))
                              (Rgl?.r_repr hreg hh0 acc)
             else S.index (S.index (RV.as_seq hh0 hs) (U32.v lv))
                          (U32.v j - 1 - U32.v ofs)));

      mt_safe_elts_rec hh3 lv hs i j;
      construct_rhs (lv + 1ul) hs rhs (i / 2ul) (j / 2ul) acc true;
      let hh4 = HST.get () in      
      mt_safe_elts_spec hh3 (lv + 1ul) hs (i / 2ul) (j / 2ul);
      assert (High.construct_rhs
               (U32.v lv + 1)
               (Rgl?.r_repr hvvreg hh3 hs)
               (Rgl?.r_repr hvreg hh3 rhs)
               (U32.v i / 2) (U32.v j / 2)
               (Rgl?.r_repr hreg hh3 acc) true ==
             (Rgl?.r_repr hvreg hh4 rhs, Rgl?.r_repr hreg hh4 acc));             
      mt_safe_elts_spec hh0 lv hs i j;
      High.construct_rhs_odd
        (U32.v lv) (Rgl?.r_repr hvvreg hh0 hs) (Rgl?.r_repr hvreg hh0 rhs)
        (U32.v i) (U32.v j) (Rgl?.r_repr hreg hh0 acc) actd;
      assert (High.construct_rhs
               (U32.v lv)
               (Rgl?.r_repr hvvreg hh0 hs)
               (Rgl?.r_repr hvreg hh0 rhs)
               (U32.v i) (U32.v j)
               (Rgl?.r_repr hreg hh0 acc) actd ==
             (Rgl?.r_repr hvreg hh4 rhs, Rgl?.r_repr hreg hh4 acc))
    end)
#reset-options // reset "--admit_smt_queries true"

val mt_get_root:
  mt:mt_p ->
  rt:hash ->
  HST.ST unit
   (requires (fun h0 ->
     mt_safe h0 mt /\ Rgl?.r_inv hreg h0 rt /\
     HH.disjoint (B.frameOf mt) (B.frameOf rt)))
   (ensures (fun h0 _ h1 ->
     // memory safety
     modifies (loc_union
                (mt_loc mt)
                (B.loc_all_regions_from false (B.frameOf rt)))
              h0 h1 /\
     mt_safe h1 mt /\
     (let mtv0 = B.get h0 mt 0 in
     let mtv1 = B.get h1 mt 0 in
     MT?.i mtv1 = MT?.i mtv0 /\ MT?.j mtv1 = MT?.j mtv0 /\
     MT?.hs mtv1 == MT?.hs mtv0 /\ MT?.rhs mtv1 == MT?.rhs mtv0 /\
     MT?.rhs_ok mtv1 = true /\
     Rgl?.r_inv hreg h1 rt /\
     // correctness
     High.mt_get_root (mt_lift h0 mt) (Rgl?.r_repr hreg h0 rt) ==
     (mt_lift h1 mt, Rgl?.r_repr hreg h1 rt))))
#reset-options "--z3rlimit 150 --max_fuel 1"
let mt_get_root mt rt =
  let hh0 = HST.get () in
  let mtv = !*mt in
  let i = MT?.i mtv in
  let j = MT?.j mtv in
  let hs = MT?.hs mtv in
  let rhs = MT?.rhs mtv in
  let mroot = MT?.mroot mtv in
  if MT?.rhs_ok mtv
  then begin
    Cpy?.copy hcpy mroot rt;
    let hh1 = HST.get () in
    mt_safe_preserved mt
      (B.loc_all_regions_from false (Rgl?.region_of hreg rt)) hh0 hh1;
    mt_preserved mt
      (B.loc_all_regions_from false (Rgl?.region_of hreg rt)) hh0 hh1;
    High.mt_get_root_rhs_ok_true
      (mt_lift hh0 mt) (Rgl?.r_repr hreg hh0 rt);
    assert (High.mt_get_root (mt_lift hh0 mt) (Rgl?.r_repr hreg hh0 rt) ==
           (mt_lift hh1 mt, Rgl?.r_repr hreg hh1 rt))
  end
  else begin
    construct_rhs 0ul hs rhs i j rt false;
    let hh1 = HST.get () in
    // memory safety
    assert (RV.rv_inv hh1 rhs);
    assert (Rgl?.r_inv hreg hh1 rt);
    assert (B.live hh1 mt);
    RV.rv_inv_preserved
      hs (loc_union
           (RV.loc_rvector rhs)
           (B.loc_all_regions_from false (B.frameOf rt)))
      hh0 hh1;
    RV.as_seq_preserved
      hs (loc_union
           (RV.loc_rvector rhs)
           (B.loc_all_regions_from false (B.frameOf rt)))
      hh0 hh1;
    V.loc_vector_within_included hs 0ul (V.size_of hs);
    mt_safe_elts_preserved 0ul hs i j
      (loc_union
        (RV.loc_rvector rhs)
        (B.loc_all_regions_from false (B.frameOf rt)))
      hh0 hh1;

    // correctness
    mt_safe_elts_spec hh0 0ul hs i j;
    assert (High.construct_rhs 0
             (Rgl?.r_repr hvvreg hh0 hs)
             (Rgl?.r_repr hvreg hh0 rhs)
             (U32.v i) (U32.v j)
             (Rgl?.r_repr hreg hh0 rt) false ==
           (Rgl?.r_repr hvreg hh1 rhs, Rgl?.r_repr hreg hh1 rt));

    Cpy?.copy hcpy rt mroot;
    let hh2 = HST.get () in
    // memory safety
    RV.rv_inv_preserved
      hs (B.loc_all_regions_from false (B.frameOf mroot))
      hh1 hh2;
    RV.rv_inv_preserved
      rhs (B.loc_all_regions_from false (B.frameOf mroot))
      hh1 hh2;
    RV.as_seq_preserved
      hs (B.loc_all_regions_from false (B.frameOf mroot))
      hh1 hh2;
    RV.as_seq_preserved
      rhs (B.loc_all_regions_from false (B.frameOf mroot))
      hh1 hh2;
    B.modifies_buffer_elim
      rt (B.loc_all_regions_from false (B.frameOf mroot))
      hh1 hh2;
    mt_safe_elts_preserved 0ul hs i j
      (B.loc_all_regions_from false (B.frameOf mroot))
      hh1 hh2;

    // correctness
    assert (Rgl?.r_repr hreg hh2 mroot == Rgl?.r_repr hreg hh1 rt);

    mt *= MT i j hs true rhs mroot;
    let hh3 = HST.get () in
    // memory safety
    Rgl?.r_sep hreg rt (B.loc_buffer mt) hh2 hh3;
    RV.rv_inv_preserved hs (B.loc_buffer mt) hh2 hh3;
    RV.rv_inv_preserved rhs (B.loc_buffer mt) hh2 hh3;
    RV.as_seq_preserved hs (B.loc_buffer mt) hh2 hh3;
    RV.as_seq_preserved rhs (B.loc_buffer mt) hh2 hh3;
    Rgl?.r_sep hreg mroot (B.loc_buffer mt) hh2 hh3;
    mt_safe_elts_preserved 0ul hs i j
      (B.loc_buffer mt) hh2 hh3;
    assert (mt_safe hh3 mt);

    // correctness
    High.mt_get_root_rhs_ok_false
      (mt_lift hh0 mt) (Rgl?.r_repr hreg hh0 rt);
    assert (High.mt_get_root (mt_lift hh0 mt) (Rgl?.r_repr hreg hh0 rt) ==
           (High.MT (U32.v i) (U32.v j) 
                    (RV.as_seq hh0 hs) true 
                    (RV.as_seq hh1 rhs)
                    (Rgl?.r_repr hreg hh1 rt),
           Rgl?.r_repr hreg hh1 rt));
    assert (High.mt_get_root (mt_lift hh0 mt) (Rgl?.r_repr hreg hh0 rt) ==
           (mt_lift hh3 mt, Rgl?.r_repr hreg hh3 rt))
  end

inline_for_extraction val path_insert:
  mtr:HH.rid -> p:path -> hp:hash ->
  HST.ST unit
    (requires (fun h0 ->
      path_safe h0 mtr p /\
      not (V.is_full (B.get h0 p 0)) /\
      Rgl?.r_inv hreg h0 hp /\
      HH.disjoint mtr (B.frameOf p) /\
      HH.includes mtr (B.frameOf hp)))
    (ensures (fun h0 _ h1 ->
      // memory safety
      modifies (path_loc p) h0 h1 /\
      path_safe h1 mtr p /\
      // correctness
      V.size_of (B.get h1 p 0) = V.size_of (B.get h0 p 0) + 1ul /\
      S.equal (lift_path h1 mtr p)
              (High.path_insert (lift_path h0 mtr p) (Rgl?.r_repr hreg h0 hp))))
inline_for_extraction let path_insert mtr p hp =
  admit ();
  let hh0 = HST.get () in
  let pv = B.index p 0ul in
  let ipv = V.insert pv hp in
  let hh1 = HST.get () in
  path_safe_preserved_
    mtr ipv (B.loc_all_regions_from false (V.frameOf ipv))
    0ul (V.size_of pv) hh1 hh0 hh1;
  p *= ipv;
  let hh2 = HST.get () in
  path_safe_preserved_
    mtr (B.get hh2 p 0) (B.loc_region_only false (B.frameOf p))
    0ul (V.size_of (B.get hh2 p 0)) hh2 hh1 hh2

private val mt_path_length_step:
  k:index_t -> 
  j:index_t{k <= j} ->
  actd:bool ->
  Tot (sl:uint32_t{U32.v sl = High.mt_path_length_step (U32.v k) (U32.v j) actd})
private let mt_path_length_step k j actd =
  if j = 0ul then 0ul
  else (if k % 2ul = 0ul
       then (if j = k || (j = k + 1ul && not actd) then 0ul else 1ul)
       else 1ul)

inline_for_extraction private val mt_get_path_step:
  lv:uint32_t{lv <= merkle_tree_size_lg} ->
  mtr:HH.rid ->
  hs:hash_vv{V.size_of hs = merkle_tree_size_lg} ->
  rhs:hash_vec{V.size_of rhs = merkle_tree_size_lg} ->
  i:index_t -> 
  j:index_t{j <> 0ul /\ i <= j /\ U32.v j < pow2 (32 - U32.v lv)} ->
  k:index_t{i <= k && k <= j} ->
  p:path ->
  actd:bool ->
  HST.ST unit
   (requires (fun h0 ->
     HH.includes mtr (V.frameOf hs) /\
     HH.includes mtr (V.frameOf rhs) /\
     RV.rv_inv h0 hs /\ RV.rv_inv h0 rhs /\
     mt_safe_elts h0 lv hs i j /\
     path_safe h0 mtr p /\
     V.size_of (B.get h0 p 0) <= lv + 1ul))
   (ensures (fun h0 _ h1 ->
     // memory safety
     modifies (path_loc p) h0 h1 /\
     path_safe h1 mtr p /\
     V.size_of (B.get h1 p 0) == V.size_of (B.get h0 p 0) + mt_path_length_step k j actd /\
     V.size_of (B.get h1 p 0) <= lv + 2ul /\
     // correctness
     (mt_safe_elts_spec h0 lv hs i j;
     S.equal (lift_path h1 mtr p)
             (High.mt_get_path_step 
               (U32.v lv) (RV.as_seq h0 hs) (RV.as_seq h0 rhs)
               (U32.v i) (U32.v j) (U32.v k) (lift_path h0 mtr p) actd))))
inline_for_extraction private let mt_get_path_step lv mtr hs rhs i j k p actd =
  let hh0 = HST.get () in
  let ofs = offset_of i in
  if k % 2ul = 1ul
  then begin
    assert (HH.includes mtr (V.frameOf (V.get hh0 hs lv)));
    assert (RV.rv_inv hh0 (V.get hh0 hs lv));
    assert (HH.extends
             (B.frameOf (V.get hh0 (V.get hh0 hs lv) (k - 1ul - ofs)))
             (V.frameOf (V.get hh0 hs lv)));
    assert (HH.includes mtr
             (B.frameOf (V.get hh0 (V.get hh0 hs lv) (k - 1ul - ofs))));
    path_insert mtr p (V.index (V.index hs lv) (k - 1ul - ofs))
  end
  else begin
    if k = j then ()
    else if k + 1ul = j
    then (if actd
         then (assert (HH.includes mtr (B.frameOf (V.get hh0 rhs lv)));
              path_insert mtr p (V.index rhs lv)))
    else (assert (HH.includes mtr (V.frameOf (V.get hh0 hs lv)));
         assert (RV.rv_inv hh0 (V.get hh0 hs lv));
         assert (HH.extends
                  (B.frameOf (V.get hh0 (V.get hh0 hs lv) (k + 1ul - ofs)))
                  (V.frameOf (V.get hh0 hs lv)));
         assert (HH.includes mtr
                  (B.frameOf (V.get hh0 (V.get hh0 hs lv) (k + 1ul - ofs))));
         path_insert mtr p (V.index (V.index hs lv) (k + 1ul - ofs)))
  end

private val mt_path_length:
  lv:uint32_t{lv <= merkle_tree_size_lg} ->
  k:index_t -> 
  j:index_t{k <= j && U32.v j < pow2 (32 - U32.v lv)} ->
  actd:bool ->
  Tot (l:uint32_t{
        U32.v l = High.mt_path_length (U32.v k) (U32.v j) actd &&
        l <= 32ul - lv})
      (decreases (U32.v j))
private let rec mt_path_length lv k j actd =
  if j = 0ul then 0ul
  else (let nactd = actd || (j % 2ul = 1ul) in
       mt_path_length_step k j actd +
       mt_path_length (lv + 1ul) (k / 2ul) (j / 2ul) nactd)

// private val mt_path_length_spec:
//   h0:HS.mem -> h1:HS.mem ->
//   lv:uint32_t{lv <= merkle_tree_size_lg} ->
//   mtr:HH.rid ->
//   k:index_t -> 
//   j:index_t{k <= j && U32.v j < pow2 (32 - U32.v lv)} ->
//   actd:bool ->
//   p:path ->
//   Lemma (requires (path_safe h0 mtr p /\ path_safe h1 mtr p /\
//                   V.size_of (B.get h0 p 0) <= lv + 1ul /\
//                   V.size_of (B.get h1 p 0) == 
//                   V.size_of (B.get h0 p 0) + mt_path_length lv k j actd))
//         (ensures (S.length (lift_path h1 mtr p) ==
//                  S.length (lift_path h0 mtr p) +
//                  High.mt_path_length (U32.v k) (U32.v j) actd))
// private let mt_path_length_spec h0 h1 lv mtr k j actd p = ()

// Construct a Merkle path for a given index `k`, hashes `hs`,
// and rightmost hashes `rhs`.
// Caution: it copies "pointers" in the Merkle tree to the output path.
private val mt_get_path_:
  lv:uint32_t{lv <= merkle_tree_size_lg} ->
  mtr:HH.rid ->
  hs:hash_vv{V.size_of hs = merkle_tree_size_lg} ->
  rhs:hash_vec{V.size_of rhs = merkle_tree_size_lg} ->
  i:index_t -> j:index_t{i <= j /\ U32.v j < pow2 (32 - U32.v lv)} ->
  k:index_t{i <= k && k <= j} ->
  p:path ->
  actd:bool ->
  HST.ST unit
   (requires (fun h0 ->
     HH.includes mtr (V.frameOf hs) /\
     HH.includes mtr (V.frameOf rhs) /\
     RV.rv_inv h0 hs /\ RV.rv_inv h0 rhs /\
     mt_safe_elts h0 lv hs i j /\
     path_safe h0 mtr p /\
     V.size_of (B.get h0 p 0) <= lv + 1ul))
   (ensures (fun h0 _ h1 ->
     // memory safety
     modifies (path_loc p) h0 h1 /\
     path_safe h1 mtr p /\
     V.size_of (B.get h1 p 0) == 
     V.size_of (B.get h0 p 0) + mt_path_length lv k j actd /\
     // correctness
     (mt_safe_elts_spec h0 lv hs i j;
     S.equal (lift_path h1 mtr p)
             (High.mt_get_path_ (U32.v lv) (RV.as_seq h0 hs) (RV.as_seq h0 rhs)
               (U32.v i) (U32.v j) (U32.v k) (lift_path h0 mtr p) actd))))
   (decreases (32 - U32.v lv))
// This proof works, but it's a bit slow.
// It will be admitted until the hint file is generated.
#reset-options "--admit_smt_queries true"
private let rec mt_get_path_ lv mtr hs rhs i j k p actd =
  let hh0 = HST.get () in
  let ofs = offset_of i in
  if j = 0ul then ()
  else
    (mt_get_path_step lv mtr hs rhs i j k p actd;

    let hh1 = HST.get () in
    mt_safe_elts_spec hh0 lv hs i j;
    assert (S.equal (lift_path hh1 mtr p)
                    (High.mt_get_path_step 
                      (U32.v lv) (RV.as_seq hh0 hs) (RV.as_seq hh0 rhs)
                      (U32.v i) (U32.v j) (U32.v k)
                      (lift_path hh0 mtr p) actd));
    RV.rv_inv_preserved hs (path_loc p) hh0 hh1;
    RV.rv_inv_preserved rhs (path_loc p) hh0 hh1;
    RV.as_seq_preserved hs (path_loc p) hh0 hh1;
    RV.as_seq_preserved rhs (path_loc p) hh0 hh1;
    V.loc_vector_within_included hs lv (V.size_of hs);
    mt_safe_elts_preserved lv hs i j (path_loc p) hh0 hh1;

    mt_get_path_ (lv + 1ul) mtr hs rhs (i / 2ul) (j / 2ul) (k / 2ul) p
      (if j % 2ul = 0ul then actd else true);

    let hh2 = HST.get () in

    mt_safe_elts_spec hh1 (lv + 1ul) hs (i / 2ul) (j / 2ul);
    assert (S.equal (lift_path hh2 mtr p)
                    (High.mt_get_path_ (U32.v lv + 1)
                      (RV.as_seq hh1 hs) (RV.as_seq hh1 rhs)
                      (U32.v i / 2) (U32.v j / 2) (U32.v k / 2)
                      (lift_path hh1 mtr p)
                      (if U32.v j % 2 = 0 then actd else true))))
#reset-options // reset "--admit_smt_queries true"

private val hash_vv_rv_inv_includes:
  h:HS.mem -> hvv:hash_vv ->
  i:uint32_t -> j:uint32_t ->
  Lemma (requires (RV.rv_inv h hvv /\
                  i < V.size_of hvv /\
                  j < V.size_of (V.get h hvv i)))
        (ensures (HH.includes
                   (Rgl?.region_of hvvreg hvv)
                   (Rgl?.region_of hreg (V.get h (V.get h hvv i) j))))
private let hash_vv_rv_inv_includes h hvv i j = ()

#reset-options "--z3rlimit 40"
val mt_get_path:
  mt:mt_p ->
  idx:index_t ->
  p:path ->
  root:hash ->
  HST.ST index_t
   (requires (fun h0 ->
     MT?.i (B.get h0 mt 0) <= idx /\ idx < MT?.j (B.get h0 mt 0) /\
     mt_safe h0 mt /\
     path_safe h0 (B.frameOf mt) p /\
     V.size_of (B.get h0 p 0) == 0ul /\
     Rgl?.r_inv hreg h0 root /\
     HH.disjoint (B.frameOf root) (B.frameOf mt) /\
     HH.disjoint (B.frameOf root) (B.frameOf p)))
   (ensures (fun h0 _ h1 ->
     // memory safety
     modifies (loc_union
                (mt_loc mt)
                (loc_union
                  (path_loc p)
                  (B.loc_all_regions_from false (B.frameOf root))))
              h0 h1 /\
     mt_safe h1 mt /\
     path_safe h1 (B.frameOf mt) p /\
     Rgl?.r_inv hreg h1 root /\
     V.size_of (B.get h1 p 0) == 
     1ul + mt_path_length 0ul idx (MT?.j (B.get h0 mt 0)) false /\
     // correctness
     High.mt_get_path
       (mt_lift h0 mt) (U32.v idx) (Rgl?.r_repr hreg h0 root) ==
     (U32.v (MT?.j (B.get h1 mt 0)),
     lift_path h1 (B.frameOf mt) p,
     Rgl?.r_repr hreg h1 root)))
// #reset-options "--z3rlimit 300 --max_fuel 1"
// This proof works, but it's a bit slow.
// It will be admitted until the hint file is generated.
#reset-options "--admit_smt_queries true"
let mt_get_path mt idx p root =
  let copy = Cpy?.copy hcpy in
  let hh0 = HST.get () in
  mt_get_root mt root;

  let hh1 = HST.get () in
  path_safe_init_preserved (B.frameOf mt) p
    (B.loc_union (mt_loc mt)
      (B.loc_all_regions_from false (B.frameOf root)))
    hh0 hh1;
  assert (High.mt_get_root (mt_lift hh0 mt) (Rgl?.r_repr hreg hh0 root) ==
         (mt_lift hh1 mt, Rgl?.r_repr hreg hh1 root));
  assert (S.equal (lift_path hh1 (B.frameOf mt) p) S.empty);

  let mtv = !*mt in
  let i = MT?.i mtv in
  let ofs = offset_of (MT?.i mtv) in
  let j = MT?.j mtv in
  let hs = MT?.hs mtv in
  let rhs = MT?.rhs mtv in
  let ih = V.index (V.index hs 0ul) (idx - ofs) in
  hash_vv_rv_inv_includes hh1 hs 0ul (idx - ofs);
  hash_vv_rv_inv_r_inv hh1 hs 0ul (idx - ofs);
  path_insert (B.frameOf mt) p ih;

  let hh2 = HST.get () in
  hash_vv_as_seq_get_index hh1 hs 0ul (idx - ofs);
  assert (S.equal (lift_path hh2 (B.frameOf mt) p)
                  (High.path_insert
                    (lift_path hh1 (B.frameOf mt) p)
                    (S.index (S.index (RV.as_seq hh1 hs) 0) (U32.v idx - U32.v ofs))));
  B.modifies_buffer_elim root (path_loc p) hh1 hh2;
  mt_safe_preserved mt (path_loc p) hh1 hh2;
  mt_preserved mt (path_loc p) hh1 hh2;
  assert (V.size_of (B.get hh2 p 0) == 1ul);

  mt_get_path_ 0ul (B.frameOf mt) hs rhs i j idx p false;

  let hh3 = HST.get () in
  B.modifies_buffer_elim root (path_loc p) hh2 hh3;
  mt_safe_preserved mt (path_loc p) hh2 hh3;
  mt_preserved mt (path_loc p) hh2 hh3;
  assert (V.size_of (B.get hh3 p 0) == 
         1ul + mt_path_length 0ul idx (MT?.j (B.get hh0 mt 0)) false);
  assert (S.length (lift_path hh3 (B.frameOf mt) p) ==
         S.length (lift_path hh2 (B.frameOf mt) p) +
         High.mt_path_length (U32.v idx) (U32.v (MT?.j (B.get hh0 mt 0))) false);

  mt_safe_elts_spec hh2 0ul hs i j;
  assert (S.equal (lift_path hh3 (B.frameOf mt) p)
                  (High.mt_get_path_ 0 (RV.as_seq hh2 hs) (RV.as_seq hh2 rhs)
                    (U32.v i) (U32.v j) (U32.v idx)
                    (lift_path hh2 (B.frameOf mt) p) false));
  assert (High.mt_get_path
           (mt_lift hh0 mt) (U32.v idx) (Rgl?.r_repr hreg hh0 root) ==
         (U32.v (MT?.j (B.get hh3 mt 0)),
         lift_path hh3 (B.frameOf mt) p,
         Rgl?.r_repr hreg hh3 root));
  j
#reset-options // reset "--admit_smt_queries true"

/// Flushing

private val mt_flush_to_modifies_rec_helper:
  lv:uint32_t{lv < merkle_tree_size_lg} ->
  hs:hash_vv{V.size_of hs = merkle_tree_size_lg} ->
  h:HS.mem ->
  Lemma (loc_union
          (loc_union
            (RV.rs_loc_elem hvreg (V.as_seq h hs) (U32.v lv))
            (V.loc_vector_within hs lv (lv + 1ul)))
          (loc_union
            (RV.rv_loc_elems h hs (lv + 1ul) (V.size_of hs))
            (V.loc_vector_within hs (lv + 1ul) (V.size_of hs))) ==
        loc_union
          (RV.rv_loc_elems h hs lv (V.size_of hs))
          (V.loc_vector_within hs lv (V.size_of hs)))
private let mt_flush_to_modifies_rec_helper lv hs h =
  admit ()

private val mt_flush_to_:
  lv:uint32_t{lv < merkle_tree_size_lg} ->
  hs:hash_vv{V.size_of hs = merkle_tree_size_lg} ->
  pi:index_t ->
  i:index_t{i >= pi} ->
  j:Ghost.erased index_t{
    Ghost.reveal j >= i &&
    U32.v (Ghost.reveal j) < pow2 (32 - U32.v lv)} ->
  HST.ST unit
   (requires (fun h0 ->
     RV.rv_inv h0 hs /\
     mt_safe_elts h0 lv hs pi (Ghost.reveal j)))
   (ensures (fun h0 _ h1 ->
     // memory safety
     modifies (loc_union
                (RV.rv_loc_elems h0 hs lv (V.size_of hs))
                (V.loc_vector_within hs lv (V.size_of hs)))
              h0 h1 /\
     RV.rv_inv h1 hs /\
     mt_safe_elts h1 lv hs i (Ghost.reveal j) /\
     // correctness
     (mt_safe_elts_spec h0 lv hs pi (Ghost.reveal j);
     S.equal (RV.as_seq h1 hs)
             (High.mt_flush_to_
               (U32.v lv) (RV.as_seq h0 hs) (U32.v pi)
               (U32.v i) (U32.v (Ghost.reveal j))))))
   (decreases (U32.v i))
// #reset-options "--z3rlimit 800 --max_fuel 1"
// This proof works with the resource limit above, but it's a bit slow.
// It will be admitted until the hint file is generated.
#reset-options "--admit_smt_queries true"
private let rec mt_flush_to_ lv hs pi i j =
  let hh0 = HST.get () in

  // Base conditions
  mt_safe_elts_rec hh0 lv hs pi (Ghost.reveal j);
  V.loc_vector_within_included hs 0ul lv;
  V.loc_vector_within_included hs lv (lv + 1ul);
  V.loc_vector_within_included hs (lv + 1ul) (V.size_of hs);
  V.loc_vector_within_disjoint hs lv (lv + 1ul) (lv + 1ul) (V.size_of hs);

  let oi = offset_of i in
  let opi = offset_of pi in
  if oi = opi then ()
  else begin

    /// 1) Flush hashes at the level `lv`, where the new vector is
    /// not yet connected to `hs`.
    let ofs = oi - opi in
    let hvec = V.index hs lv in
    let flushed = RV.flush hvec ofs in
    let hh1 = HST.get () in

    // 1-0) Basic disjointness conditions for `RV.assign`
    V.forall2_forall_left hh0 hs 0ul (V.size_of hs) lv
      (fun b1 b2 -> HH.disjoint (Rgl?.region_of hvreg b1)
                                (Rgl?.region_of hvreg b2));
    V.forall2_forall_right hh0 hs 0ul (V.size_of hs) lv
      (fun b1 b2 -> HH.disjoint (Rgl?.region_of hvreg b1)
                                (Rgl?.region_of hvreg b2));
    V.forall_preserved
      hs 0ul lv
      (fun b -> HH.disjoint (Rgl?.region_of hvreg hvec)
                            (Rgl?.region_of hvreg b))
      (RV.loc_rvector hvec)
      hh0 hh1;
    V.forall_preserved
      hs (lv + 1ul) (V.size_of hs)
      (fun b -> HH.disjoint (Rgl?.region_of hvreg hvec)
                            (Rgl?.region_of hvreg b))
      (RV.loc_rvector hvec)
      hh0 hh1;
    assert (Rgl?.region_of hvreg hvec == Rgl?.region_of hvreg flushed);

    // 1-1) For the `modifies` postcondition.
    assert (modifies (RV.rs_loc_elem hvreg (V.as_seq hh0 hs) (U32.v lv)) hh0 hh1);

    // 1-2) Preservation
    RV.rv_loc_elems_preserved
      hs (lv + 1ul) (V.size_of hs)
      (RV.loc_rvector (V.get hh0 hs lv)) hh0 hh1;

    // 1-3) For `mt_safe_elts`
    assert (V.size_of flushed == Ghost.reveal j - offset_of i); // head updated
    mt_safe_elts_preserved
      (lv + 1ul) hs (pi / 2ul) (Ghost.reveal j / 2ul)
      (RV.loc_rvector (V.get hh0 hs lv)) hh0 hh1; // tail not yet

    // 1-4) For the `rv_inv` postcondition
    RV.rs_loc_elems_elem_disj
      hvreg (V.as_seq hh0 hs) (V.frameOf hs)
      0 (U32.v (V.size_of hs)) 0 (U32.v lv) (U32.v lv);
    RV.rs_loc_elems_parent_disj
      hvreg (V.as_seq hh0 hs) (V.frameOf hs)
      0 (U32.v lv);
    RV.rv_elems_inv_preserved
      hs 0ul lv (RV.loc_rvector (V.get hh0 hs lv))
      hh0 hh1;
    assert (RV.rv_elems_inv hh1 hs 0ul lv);
    RV.rs_loc_elems_elem_disj
      hvreg (V.as_seq hh0 hs) (V.frameOf hs)
      0 (U32.v (V.size_of hs))
      (U32.v lv + 1) (U32.v (V.size_of hs))
      (U32.v lv);
    RV.rs_loc_elems_parent_disj
      hvreg (V.as_seq hh0 hs) (V.frameOf hs)
      (U32.v lv + 1) (U32.v (V.size_of hs));
    RV.rv_elems_inv_preserved
      hs (lv + 1ul) (V.size_of hs) (RV.loc_rvector (V.get hh0 hs lv))
      hh0 hh1;
    assert (RV.rv_elems_inv hh1 hs (lv + 1ul) (V.size_of hs));

    assert (rv_itself_inv hh1 hs);
    assert (elems_reg hh1 hs);

    // 1-5) Correctness
    assert (S.equal (RV.as_seq hh1 flushed)
                    (S.slice (RV.as_seq hh0 (V.get hh0 hs lv)) (U32.v ofs)
                             (S.length (RV.as_seq hh0 (V.get hh0 hs lv)))));

    /// 2) Assign the flushed vector to `hs` at the level `lv`.
    RV.assign hs lv flushed;
    let hh2 = HST.get () in

    // 2-1) For the `modifies` postcondition.
    assert (modifies (V.loc_vector_within hs lv (lv + 1ul)) hh1 hh2);
    assert (modifies (loc_union
                       (RV.rs_loc_elem hvreg (V.as_seq hh0 hs) (U32.v lv))
                       (V.loc_vector_within hs lv (lv + 1ul))) hh0 hh2);

    // 2-2) Preservation
    V.loc_vector_within_disjoint hs lv (lv + 1ul) (lv + 1ul) (V.size_of hs);
    RV.rv_loc_elems_preserved
      hs (lv + 1ul) (V.size_of hs)
      (V.loc_vector_within hs lv (lv + 1ul)) hh1 hh2;

    // 2-3) For `mt_safe_elts`
    assert (V.size_of (V.get hh2 hs lv) ==
           Ghost.reveal j - offset_of i);
    mt_safe_elts_preserved
      (lv + 1ul) hs (pi / 2ul) (Ghost.reveal j / 2ul)
      (V.loc_vector_within hs lv (lv + 1ul)) hh1 hh2;

    // 2-4) Correctness
    RV.as_seq_sub_preserved hs 0ul lv (loc_rvector flushed) hh0 hh1;
    RV.as_seq_sub_preserved hs (lv + 1ul) merkle_tree_size_lg (loc_rvector flushed) hh0 hh1;
    assert (S.equal (RV.as_seq hh2 hs)
                    (S.append
                      (RV.as_seq_sub hh0 hs 0ul lv)
                      (S.cons (RV.as_seq hh1 flushed)
                              (RV.as_seq_sub hh0 hs (lv + 1ul) merkle_tree_size_lg))));
    assume (S.equal (RV.as_seq hh2 hs)
                    (S.upd (RV.as_seq hh0 hs) (U32.v lv) (RV.as_seq hh1 flushed)));

    // if `lv = 31` then `pi <= i <= j < 2` thus `oi = opi`, 
    // contradicting the branch.
    assert (lv + 1ul < merkle_tree_size_lg);
    assert (U32.v (Ghost.reveal j / 2ul) < pow2 (32 - U32.v (lv + 1ul)));
    assert (RV.rv_inv hh2 hs);
    assert (mt_safe_elts hh2 (lv + 1ul) hs (pi / 2ul) (Ghost.reveal j / 2ul));

    /// 3) Recursion
    mt_flush_to_ (lv + 1ul) hs (pi / 2ul) (i / 2ul)
      (Ghost.hide (Ghost.reveal j / 2ul));
    let hh3 = HST.get () in

    // 3-0) Memory safety brought from the postcondition of the recursion
    assert (modifies
             (loc_union
               (loc_union
                 (RV.rs_loc_elem hvreg (V.as_seq hh0 hs) (U32.v lv))
                 (V.loc_vector_within hs lv (lv + 1ul)))
               (loc_union
                 (RV.rv_loc_elems hh0 hs (lv + 1ul) (V.size_of hs))
                 (V.loc_vector_within hs (lv + 1ul) (V.size_of hs))))
             hh0 hh3);
    mt_flush_to_modifies_rec_helper lv hs hh0;
    V.loc_vector_within_disjoint hs lv (lv + 1ul) (lv + 1ul) (V.size_of hs);
    V.loc_vector_within_included hs lv (lv + 1ul);
    RV.rv_loc_elems_included hh2 hs (lv + 1ul) (V.size_of hs);
    assert (loc_disjoint
             (V.loc_vector_within hs lv (lv + 1ul))
             (RV.rv_loc_elems hh2 hs (lv + 1ul) (V.size_of hs)));
    V.get_preserved hs lv
      (loc_union
        (RV.rv_loc_elems hh2 hs (lv + 1ul) (V.size_of hs))
        (V.loc_vector_within hs (lv + 1ul) (V.size_of hs)))
      hh2 hh3;
    assert (V.size_of (V.get hh3 hs lv) ==
           Ghost.reveal j - offset_of i);
    assert (RV.rv_inv hh3 hs);
    mt_safe_elts_constr hh3 lv hs i (Ghost.reveal j);
    assert (mt_safe_elts hh3 lv hs i (Ghost.reveal j));

    // 3-1) Correctness
    mt_safe_elts_spec hh2 (lv + 1ul) hs (pi / 2ul) (Ghost.reveal j / 2ul);
    assert (S.equal (RV.as_seq hh3 hs)
                    (High.mt_flush_to_ (U32.v lv + 1) (RV.as_seq hh2 hs)
                      (U32.v pi / 2) (U32.v i / 2) (U32.v (Ghost.reveal j) / 2)));
    mt_safe_elts_spec hh0 lv hs pi (Ghost.reveal j);
    High.mt_flush_to_rec 
      (U32.v lv) (RV.as_seq hh0 hs)
      (U32.v pi) (U32.v i) (U32.v (Ghost.reveal j));
    assert (S.equal (RV.as_seq hh3 hs)
                    (High.mt_flush_to_ (U32.v lv) (RV.as_seq hh0 hs)
                      (U32.v pi) (U32.v i) (U32.v (Ghost.reveal j))))
  end
#reset-options // reset "--admit_smt_queries true"

val mt_flush_to:
  mt:mt_p ->
  idx:index_t ->
  HST.ST unit
   (requires (fun h0 ->
     mt_safe h0 mt /\ idx >= MT?.i (B.get h0 mt 0) /\
     idx < MT?.j (B.get h0 mt 0)))
   (ensures (fun h0 _ h1 ->
     // memory safety
     modifies (mt_loc mt) h0 h1 /\
     mt_safe h1 mt /\
     // correctness
     High.mt_flush_to (mt_lift h0 mt) (U32.v idx) == mt_lift h1 mt))
#reset-options "--z3rlimit 80 --max_fuel 1"
let rec mt_flush_to mt idx =
  let hh0 = HST.get () in
  let mtv = !*mt in
  let hs = MT?.hs mtv in
  mt_flush_to_ 0ul hs (MT?.i mtv) idx (Ghost.hide (MT?.j mtv));
  let hh1 = HST.get () in
  RV.rv_loc_elems_included hh0 hs 0ul (V.size_of hs);
  V.loc_vector_within_included hs 0ul (V.size_of hs);
  RV.rv_inv_preserved
    (MT?.rhs mtv)
    (loc_union
      (RV.rv_loc_elems hh0 hs 0ul (V.size_of hs))
      (V.loc_vector_within hs 0ul (V.size_of hs)))
    hh0 hh1;
  RV.as_seq_preserved
    (MT?.rhs mtv)
    (loc_union
      (RV.rv_loc_elems hh0 hs 0ul (V.size_of hs))
      (V.loc_vector_within hs 0ul (V.size_of hs)))
    hh0 hh1;
  Rgl?.r_sep hreg (MT?.mroot mtv)
    (loc_union
      (RV.rv_loc_elems hh0 hs 0ul (V.size_of hs))
      (V.loc_vector_within hs 0ul (V.size_of hs)))
    hh0 hh1;
  mt *= MT idx (MT?.j mtv) hs (MT?.rhs_ok mtv) (MT?.rhs mtv) (MT?.mroot mtv);

  let hh2 = HST.get () in
  RV.rv_inv_preserved (MT?.hs mtv) (B.loc_buffer mt) hh1 hh2;
  RV.rv_inv_preserved (MT?.rhs mtv) (B.loc_buffer mt) hh1 hh2;
  RV.as_seq_preserved (MT?.hs mtv) (B.loc_buffer mt) hh1 hh2;
  RV.as_seq_preserved (MT?.rhs mtv) (B.loc_buffer mt) hh1 hh2;
  Rgl?.r_sep hreg (MT?.mroot mtv) (B.loc_buffer mt) hh1 hh2;
  mt_safe_elts_preserved 0ul hs idx (MT?.j mtv) (B.loc_buffer mt) hh1 hh2

val mt_flush:
  mt:mt_p ->
  HST.ST unit
   (requires (fun h0 ->
     mt_safe h0 mt /\
     MT?.j (B.get h0 mt 0) > MT?.i (B.get h0 mt 0)))
   (ensures (fun h0 _ h1 ->
     // memory safety
     modifies (mt_loc mt) h0 h1 /\
     mt_safe h1 mt /\
     // correctness
     High.mt_flush (mt_lift h0 mt) == mt_lift h1 mt))
let mt_flush mt =
  let mtv = !*mt in
  mt_flush_to mt (MT?.j mtv - 1ul)

/// Client-side verification

val lift_path_index:
  h:HS.mem -> mtr:HH.rid -> 
  p:path -> i:uint32_t ->
  Lemma (requires (path_safe h mtr p /\
                  i < V.size_of (B.get h p 0)))
        (ensures (Rgl?.r_repr hreg h (V.get h (B.get h p 0) i) ==
                 S.index (lift_path h mtr p) (U32.v i)))
let rec lift_path_index h mtr p i =
  admit ()

private val mt_verify_:
  k:index_t ->
  j:index_t{k <= j} ->
  mtr:HH.rid -> p:path ->
  ppos:uint32_t ->
  acc:hash ->
  actd:bool ->
  HST.ST unit
   (requires (fun h0 ->
     path_safe h0 mtr p /\ Rgl?.r_inv hreg h0 acc /\
     HH.disjoint (B.frameOf p) (B.frameOf acc) /\
     HH.disjoint mtr (B.frameOf acc) /\
     // Below is a very relaxed condition,
     // but sufficient to ensure (+) for uint32_t is sound.
     ppos <= 64ul - mt_path_length 0ul k j actd /\
     ppos + mt_path_length 0ul k j actd <= V.size_of (B.get h0 p 0)))
   (ensures (fun h0 _ h1 ->
     // memory safety
     modifies (B.loc_all_regions_from false (B.frameOf acc)) h0 h1 /\
     Rgl?.r_inv hreg h1 acc /\
     // correctness
     Rgl?.r_repr hreg h1 acc ==
     High.mt_verify_ (U32.v k) (U32.v j) (lift_path h0 mtr p)
       (U32.v ppos) (Rgl?.r_repr hreg h0 acc) actd))
#reset-options "--z3rlimit 200 --max_fuel 8"
private let rec mt_verify_ k j mtr p ppos acc actd =
  let hh0 = HST.get () in
  if j = 0ul then ()
  // cwinter: is this correct?
  // else if ppos = V.size_of !*p then ()
  // joonwonc: there was a bug; it's fixed now and we don't need the above 
  //           condition anymore, but it's not proven yet.
  else (let nactd = actd || (j % 2ul = 1ul) in
       if k % 2ul = 0ul then begin
         if j = k || (j = k + 1ul && not actd) then
           mt_verify_ (k / 2ul) (j / 2ul) mtr p ppos acc nactd
         else begin
           let phash = V.index !*p ppos in
           hash_2 acc phash acc;
           let hh1 = HST.get () in
           path_preserved mtr p
             (B.loc_all_regions_from false (B.frameOf acc)) hh0 hh1;
           lift_path_index hh0 mtr p ppos;
           assert (Rgl?.r_repr hreg hh1 acc ==
                  High.hash_2 (Rgl?.r_repr hreg hh0 acc)
                              (S.index (lift_path hh0 mtr p) (U32.v ppos)));
           mt_verify_ (k / 2ul) (j / 2ul) mtr p (ppos + 1ul) acc nactd
         end
       end
       else begin
         let phash = V.index !*p ppos in
         hash_2 phash acc acc;
         let hh1 = HST.get () in
         path_preserved mtr p
           (B.loc_all_regions_from false (B.frameOf acc)) hh0 hh1;
         lift_path_index hh0 mtr p ppos;
         assert (Rgl?.r_repr hreg hh1 acc ==
                High.hash_2 (S.index (lift_path hh0 mtr p) (U32.v ppos))
                            (Rgl?.r_repr hreg hh0 acc));
         mt_verify_ (k / 2ul) (j / 2ul) mtr p (ppos + 1ul) acc nactd
       end)

private val buf_eq:
  #a:eqtype -> b1:B.buffer a -> b2:B.buffer a ->
  len:uint32_t ->
  HST.ST bool
   (requires (fun h0 ->
     B.live h0 b1 /\ B.live h0 b2 /\
     len <= B.len b1 /\ len <= B.len b2))
   (ensures (fun h0 b h1 -> 
     // memory safety
     h0 == h1 /\
     // correctness
     (b ==> S.equal (B.as_seq h0 (B.gsub b1 0ul len))
                    (B.as_seq h0 (B.gsub b2 0ul len)))))
private let rec buf_eq #a b1 b2 len =
  admit ();
  if len = 0ul then true
  else (let a1 = B.index b1 (len - 1ul) in
       let a2 = B.index b2 (len - 1ul) in
       let teq = buf_eq b1 b2 (len - 1ul) in
       a1 = a2 && teq)

val mt_verify_precondition:
  k:index_t ->
  j:index_t{k < j} ->
  mtr:HH.rid -> 
  p:path ->
  rt:hash ->
  HST.ST bool
    (requires (fun h0 ->
      path_safe h0 mtr p /\ Rgl?.r_inv hreg h0 rt /\
      HST.is_eternal_region (B.frameOf rt) /\
      HH.disjoint (B.frameOf p) (B.frameOf rt) /\
      HH.disjoint mtr (B.frameOf rt)))
    (ensures (fun _ r h1 -> r ==> 
      path_safe h1 mtr p /\ Rgl?.r_inv hreg h1 rt /\
      HST.is_eternal_region (B.frameOf rt) /\
      HH.disjoint (B.frameOf p) (B.frameOf rt) /\
      HH.disjoint mtr (B.frameOf rt) /\
      V.size_of (B.get h1 p 0) == 1ul + mt_path_length 0ul k j false))
let mt_verify_precondition k j mtr p rt =
  // cwinter: add memory checks?
  let psz = V.size_of !*p in
  psz = 1ul + mt_path_length 0ul k j false

val mt_verify:
  k:index_t ->
  j:index_t{k < j} ->
  mtr:HH.rid -> 
  p:path ->
  rt:hash ->
  HST.ST bool
   (requires (fun h0 ->
     path_safe h0 mtr p /\ Rgl?.r_inv hreg h0 rt /\
     HST.is_eternal_region (B.frameOf rt) /\
     HH.disjoint (B.frameOf p) (B.frameOf rt) /\
     HH.disjoint mtr (B.frameOf rt) /\
     V.size_of (B.get h0 p 0) == 1ul + mt_path_length 0ul k j false))
   (ensures (fun h0 b h1 ->
     // memory safety:
     // `rt` is not modified in this function, but we use a trick
     // to allocate an auxiliary buffer in the extended region of `rt`.
     modifies (B.loc_all_regions_from false (B.frameOf rt)) h0 h1 /\
     Rgl?.r_inv hreg h1 rt /\
     // correctness
     S.equal (Rgl?.r_repr hreg h0 rt) (Rgl?.r_repr hreg h1 rt) /\
     b == High.mt_verify (U32.v k) (U32.v j)
            (lift_path h0 mtr p) (Rgl?.r_repr hreg h0 rt)))
let mt_verify k j mtr p rt =
  let hh0 = HST.get () in
  let nrid = RV.new_region_ (B.frameOf rt) in
  let ih = Rgl?.r_init hreg nrid in
  let copy = Cpy?.copy hcpy in
  copy (V.index !*p 0ul) ih;
  let hh1 = HST.get () in
  path_safe_preserved
    mtr p (B.loc_all_regions_from false (B.frameOf rt)) hh0 hh1;
  path_preserved mtr p (B.loc_all_regions_from false (B.frameOf rt)) hh0 hh1;
  lift_path_index hh0 mtr p 0ul;
  assert (Rgl?.r_repr hreg hh1 ih == S.index (lift_path hh0 mtr p) 0);

  mt_verify_ k j mtr p 1ul ih false;
  let hh2 = HST.get () in
  assert (Rgl?.r_repr hreg hh2 ih ==
         High.mt_verify_ (U32.v k) (U32.v j) (lift_path hh1 mtr p)
           1 (Rgl?.r_repr hreg hh1 ih) false);
  let r = buf_eq ih rt hash_size in
  Rgl?.r_free hreg ih;
  r
