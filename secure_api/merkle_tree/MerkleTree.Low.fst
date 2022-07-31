module MerkleTree.Low

open EverCrypt.Helpers

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

module U32 = FStar.UInt32
module U64 = FStar.UInt64

module MTH = MerkleTree.New.High
module MTS = MerkleTree.Spec

open Lib.IntTypes

open MerkleTree.Low.Datastructures
open MerkleTree.Low.Hashfunctions
open MerkleTree.Low.VectorExtras

#set-options "--z3rlimit 10 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

type const_pointer (a:Type0) = b:CB.const_buffer a{CB.length b == 1 /\ CB.qual_of b == CB.MUTABLE}

/// Low-level Merkle tree data structure
///
// NOTE: because of a lack of 64-bit LowStar.Buffer support, currently
// we cannot change below to some other types.
type index_t = uint32_t

let uint32_32_max = 4294967295ul
inline_for_extraction
let uint32_max = 4294967295UL
let uint64_max = 18446744073709551615UL
let offset_range_limit = uint32_max

type offset_t = uint64_t
inline_for_extraction noextract unfold let u32_64 = Int.Cast.uint32_to_uint64
inline_for_extraction noextract unfold let u64_32 = Int.Cast.uint64_to_uint32

private inline_for_extraction
let offsets_connect (x:offset_t) (y:offset_t): Tot bool = y >= x && (y - x) <= offset_range_limit

private inline_for_extraction
let split_offset (tree:offset_t) (index:offset_t{offsets_connect tree index}): Tot index_t =
  [@inline_let] let diff = U64.sub_mod index tree in
  assert (diff <= offset_range_limit);
  Int.Cast.uint64_to_uint32 diff

private inline_for_extraction
let add64_fits (x:offset_t) (i:index_t): Tot bool = uint64_max - x >= (u32_64 i)

private inline_for_extraction
let join_offset (tree:offset_t) (i:index_t{add64_fits tree i}): Tot (r:offset_t{offsets_connect tree r}) =
  U64.add tree (u32_64 i)

inline_for_extraction val merkle_tree_size_lg: uint32_t
let merkle_tree_size_lg = 32ul

// A Merkle tree `MT i j hs rhs_ok rhs` stores all necessary hashes to generate
// a Merkle path for each element from the index `i` to `j-1`.
// - Parameters
// `hs`: a 2-dim store for hashes, where `hs[0]` contains leaf hash values.
// `rhs_ok`: to check the rightmost hashes are up-to-date
// `rhs`: a store for "rightmost" hashes, manipulated only when required to
//        calculate some merkle paths that need the rightmost hashes
//        as a part of them.
// `mroot`: during the construction of `rhs` we can also calculate the Merkle
//          root of the tree. If `rhs_ok` is true then it has the up-to-date
//          root value.
noeq type merkle_tree =
| MT: hash_size:hash_size_t ->
      offset:offset_t ->
      i:index_t -> j:index_t{i <= j /\ add64_fits offset j} ->
      hs:hash_vv hash_size {V.size_of hs = merkle_tree_size_lg} ->
      rhs_ok:bool ->
      rhs:hash_vec #hash_size {V.size_of rhs = merkle_tree_size_lg} ->
      mroot:hash #hash_size ->
      hash_spec:Ghost.erased (MTS.hash_fun_t #(U32.v hash_size)) ->
      hash_fun:hash_fun_t #hash_size #hash_spec ->
      merkle_tree

type mt_p = B.pointer merkle_tree
type const_mt_p = const_pointer merkle_tree

inline_for_extraction
let merkle_tree_conditions (#hsz:Ghost.erased hash_size_t) (offset:uint64_t) (i j:uint32_t) (hs:hash_vv hsz) (rhs_ok:bool) (rhs:hash_vec #hsz) (mroot:hash #hsz): Tot bool =
  j >= i && add64_fits offset j &&
  V.size_of hs = merkle_tree_size_lg &&
  V.size_of rhs = merkle_tree_size_lg

// The maximum number of currently held elements in the tree is (2^32 - 1).
// cwinter: even when using 64-bit indices, we fail if the underlying 32-bit
// vector is full; this can be fixed if necessary.
private inline_for_extraction
val mt_not_full_nst: mtv:merkle_tree -> Tot bool
let mt_not_full_nst mtv = MT?.j mtv < uint32_32_max

val mt_not_full: HS.mem -> mt_p -> GTot bool
let mt_not_full h mt = mt_not_full_nst (B.get h mt 0)

/// (Memory) Safety

val offset_of: i:index_t -> Tot index_t
let offset_of i = if i % 2ul = 0ul then i else i - 1ul

// `mt_safe_elts` says that it is safe to access an element from `i` to `j - 1`
// at level `lv` in the Merkle tree, i.e., hs[lv][k] (i <= k < j) is a valid
// element.
inline_for_extraction noextract
val mt_safe_elts:
  #hsz:hash_size_t ->
  h:HS.mem -> lv:uint32_t{lv <= merkle_tree_size_lg} ->
  hs:hash_vv hsz {V.size_of hs = merkle_tree_size_lg} ->
  i:index_t -> j:index_t{j >= i} ->
  GTot Type0 (decreases (32 - U32.v lv))
let rec mt_safe_elts #hsz h lv hs i j =
  if lv = merkle_tree_size_lg then true
  else (let ofs = offset_of i in
       V.size_of (V.get h hs lv) == j - ofs /\
       mt_safe_elts #hsz h (lv + 1ul) hs (i / 2ul) (j / 2ul))

#push-options "--initial_fuel 1 --max_fuel 1"
val mt_safe_elts_constr:
  #hsz:hash_size_t ->
  h:HS.mem -> lv:uint32_t{lv < merkle_tree_size_lg} ->
  hs:hash_vv hsz {V.size_of hs = merkle_tree_size_lg} ->
  i:index_t -> j:index_t{j >= i} ->
  Lemma (requires (V.size_of (V.get h hs lv) == j - offset_of i /\
                  mt_safe_elts #hsz h (lv + 1ul) hs (i / 2ul) (j / 2ul)))
        (ensures (mt_safe_elts #hsz h lv hs i j))
let mt_safe_elts_constr #_ h lv hs i j = ()

val mt_safe_elts_head:
  #hsz:hash_size_t ->
  h:HS.mem -> lv:uint32_t{lv < merkle_tree_size_lg} ->
  hs:hash_vv hsz {V.size_of hs = merkle_tree_size_lg} ->
  i:index_t -> j:index_t{j >= i} ->
  Lemma (requires (mt_safe_elts #hsz h lv hs i j))
        (ensures (V.size_of (V.get h hs lv) == j - offset_of i))
let mt_safe_elts_head #_ h lv hs i j = ()

val mt_safe_elts_rec:
  #hsz:hash_size_t ->
  h:HS.mem -> lv:uint32_t{lv < merkle_tree_size_lg} ->
  hs:hash_vv hsz {V.size_of hs = merkle_tree_size_lg} ->
  i:index_t -> j:index_t{j >= i} ->
  Lemma (requires (mt_safe_elts #hsz h lv hs i j))
        (ensures (mt_safe_elts #hsz h (lv + 1ul) hs (i / 2ul) (j / 2ul)))
let mt_safe_elts_rec #_ h lv hs i j = ()

val mt_safe_elts_init:
  #hsz:hash_size_t ->
  h:HS.mem -> lv:uint32_t{lv <= merkle_tree_size_lg} ->
  hs:hash_vv hsz {V.size_of hs = merkle_tree_size_lg} ->
  Lemma (requires (V.forall_ h hs lv (V.size_of hs)
                    (fun hv -> V.size_of hv = 0ul)))
        (ensures (mt_safe_elts #hsz h lv hs 0ul 0ul))
        (decreases (32 - U32.v lv))
let rec mt_safe_elts_init #hsz h lv hs =
  if lv = merkle_tree_size_lg then ()
  else mt_safe_elts_init #hsz h (lv + 1ul) hs
#pop-options

val mt_safe_elts_preserved:
  #hsz:hash_size_t ->
  lv:uint32_t{lv <= merkle_tree_size_lg} ->
  hs:hash_vv hsz {V.size_of hs = merkle_tree_size_lg} ->
  i:index_t -> j:index_t{j >= i} ->
  p:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (V.live h0 hs /\
                  mt_safe_elts #hsz h0 lv hs i j /\
                  loc_disjoint p (V.loc_vector_within hs lv (V.size_of hs)) /\
                  modifies p h0 h1))
        (ensures (mt_safe_elts #hsz h1 lv hs i j))
        (decreases (32 - U32.v lv))
        [SMTPat (V.live h0 hs);
        SMTPat (mt_safe_elts #hsz h0 lv hs i j);
        SMTPat (loc_disjoint p (RV.loc_rvector hs));
        SMTPat (modifies p h0 h1)]
#push-options "--z3rlimit 100 --initial_fuel 2 --max_fuel 2"
let rec mt_safe_elts_preserved #hsz lv hs i j p h0 h1 =
  if lv = merkle_tree_size_lg then ()
  else (V.get_preserved hs lv p h0 h1;
       mt_safe_elts_preserved #hsz (lv + 1ul) hs (i / 2ul) (j / 2ul) p h0 h1)
#pop-options

// `mt_safe` is the invariant of a Merkle tree through its lifetime.
// It includes liveness, regionality, disjointness (to each data structure),
// and valid element access (`mt_safe_elts`).
inline_for_extraction noextract
val mt_safe: HS.mem -> mt_p -> GTot Type0
let mt_safe h mt =
  B.live h mt /\ B.freeable mt /\
  (let mtv = B.get h mt 0 in
  // Liveness & Accessibility
  RV.rv_inv h (MT?.hs mtv) /\
  RV.rv_inv h (MT?.rhs mtv) /\
  Rgl?.r_inv (hreg (MT?.hash_size mtv)) h (MT?.mroot mtv) /\
  mt_safe_elts h 0ul (MT?.hs mtv) (MT?.i mtv) (MT?.j mtv) /\
  // Regionality
  HH.extends (V.frameOf (MT?.hs mtv)) (B.frameOf mt) /\
  HH.extends (V.frameOf (MT?.rhs mtv)) (B.frameOf mt) /\
  HH.extends (B.frameOf (MT?.mroot mtv)) (B.frameOf mt) /\
  HH.disjoint (V.frameOf (MT?.hs mtv)) (V.frameOf (MT?.rhs mtv)) /\
  HH.disjoint (V.frameOf (MT?.hs mtv)) (B.frameOf (MT?.mroot mtv)) /\
  HH.disjoint (V.frameOf (MT?.rhs mtv)) (B.frameOf (MT?.mroot mtv)))

// Since a Merkle tree satisfies regionality, it's ok to take all regions from
// a tree pointer as a location of the tree.
val mt_loc: mt_p -> GTot loc
let mt_loc mt = B.loc_all_regions_from false (B.frameOf mt)

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
  Rgl?.r_sep (hreg (MT?.hash_size mtv)) (MT?.mroot mtv) p h0 h1;
  V.loc_vector_within_included (MT?.hs mtv) 0ul (V.size_of (MT?.hs mtv));
  mt_safe_elts_preserved 0ul (MT?.hs mtv) (MT?.i mtv) (MT?.j mtv) p h0 h1

/// Lifting to a high-level Merkle tree structure

val mt_safe_elts_spec:
  #hsz:hash_size_t ->
  h:HS.mem ->
  lv:uint32_t{lv <= merkle_tree_size_lg} ->
  hs:hash_vv hsz {V.size_of hs = merkle_tree_size_lg} ->
  i:index_t ->
  j:index_t{j >= i} ->
  Lemma (requires (RV.rv_inv h hs /\
                  mt_safe_elts #hsz h lv hs i j))
        (ensures (MTH.hs_wf_elts #(U32.v hsz)
                   (U32.v lv) (RV.as_seq h hs)
                   (U32.v i) (U32.v j)))
        (decreases (32 - U32.v lv))
#push-options "--z3rlimit 100 --initial_fuel 2 --max_fuel 2"
let rec mt_safe_elts_spec #_ h lv hs i j =
  if lv = merkle_tree_size_lg then ()
  else mt_safe_elts_spec h (lv + 1ul) hs (i / 2ul) (j / 2ul)
#pop-options

val merkle_tree_lift:
  h:HS.mem ->
  mtv:merkle_tree{
    RV.rv_inv h (MT?.hs mtv) /\
    RV.rv_inv h (MT?.rhs mtv) /\
    Rgl?.r_inv (hreg (MT?.hash_size mtv)) h (MT?.mroot mtv) /\
    mt_safe_elts #(MT?.hash_size mtv) h 0ul (MT?.hs mtv) (MT?.i mtv) (MT?.j mtv)} ->
  GTot (r:MTH.merkle_tree #(U32.v (MT?.hash_size mtv)) {MTH.mt_wf_elts #_ r})
let merkle_tree_lift h mtv =
  mt_safe_elts_spec h 0ul (MT?.hs mtv) (MT?.i mtv) (MT?.j mtv);
  MTH.MT #(U32.v (MT?.hash_size mtv))
    (U32.v (MT?.i mtv))
    (U32.v (MT?.j mtv))
    (RV.as_seq h (MT?.hs mtv))
    (MT?.rhs_ok mtv)
    (RV.as_seq h (MT?.rhs mtv))
    (Rgl?.r_repr (hreg (MT?.hash_size mtv)) h (MT?.mroot mtv))
    (Ghost.reveal (MT?.hash_spec mtv))

val mt_lift:
  h:HS.mem -> mt:mt_p{mt_safe h mt} ->
  GTot (r:MTH.merkle_tree #(U32.v (MT?.hash_size (B.get h mt 0))) {MTH.mt_wf_elts #_ r})
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

// Note that the public function for creation is `mt_create` defined below,
// which builds a tree with an initial hash.
#push-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"
private
val create_empty_mt:
  hash_size:hash_size_t ->
  hash_spec:Ghost.erased (MTS.hash_fun_t #(U32.v hash_size)) ->
  hash_fun:hash_fun_t #hash_size #hash_spec ->
  r:HST.erid ->
  HST.ST mt_p
   (requires (fun _ -> true))
   (ensures (fun h0 mt h1 ->
     let dmt = B.get h1 mt 0 in
     // memory safety
     B.frameOf mt = r /\
     modifies (mt_loc mt) h0 h1 /\
     mt_safe h1 mt /\
     mt_not_full h1 mt /\
     // correctness
     MT?.hash_size dmt = hash_size /\
     MT?.offset dmt = 0UL /\
     merkle_tree_lift h1 dmt == MTH.create_empty_mt #_ #(Ghost.reveal hash_spec) ()))
let create_empty_mt hsz hash_spec hash_fun r =
  [@inline_let] let hrg = hreg hsz in
  [@inline_let] let hvrg = hvreg hsz in
  [@inline_let] let hvvrg = hvvreg hsz in
  let hs_region = HST.new_region r in
  let hs = RV.alloc_rid hvrg merkle_tree_size_lg hs_region in
  let h0 = HST.get () in
  mt_safe_elts_init #hsz h0 0ul hs;
  let rhs_region = HST.new_region r in
  let rhs = RV.alloc_rid hrg merkle_tree_size_lg rhs_region in
  let h1 = HST.get () in
  assert (RV.as_seq h1 rhs == S.create 32 (MTH.hash_init #(U32.v hsz)));
  RV.rv_inv_preserved hs (V.loc_vector rhs) h0 h1;
  RV.as_seq_preserved hs (V.loc_vector rhs) h0 h1;
  V.loc_vector_within_included hs 0ul (V.size_of hs);
  mt_safe_elts_preserved #hsz 0ul hs 0ul 0ul (V.loc_vector rhs) h0 h1;
  let mroot_region = HST.new_region r in
  let mroot = rg_alloc hrg mroot_region in
  let h2 = HST.get () in
  RV.as_seq_preserved hs loc_none h1 h2;
  RV.as_seq_preserved rhs loc_none h1 h2;
  mt_safe_elts_preserved #hsz 0ul hs 0ul 0ul loc_none h1 h2;
  let mt = B.malloc r (MT hsz 0UL 0ul 0ul hs false rhs mroot hash_spec hash_fun) 1ul in
  let h3 = HST.get () in
  RV.as_seq_preserved hs loc_none h2 h3;
  RV.as_seq_preserved rhs loc_none h2 h3;
  Rgl?.r_sep hrg mroot loc_none h2 h3;
  mt_safe_elts_preserved #hsz 0ul hs 0ul 0ul loc_none h2 h3;
  mt
#pop-options

/// Destruction (free)

val mt_free: mt:mt_p ->
  HST.ST unit
   (requires (fun h0 -> mt_safe h0 mt))
   (ensures (fun h0 _ h1 -> modifies (mt_loc mt) h0 h1))
#push-options "--z3rlimit 100"
let mt_free mt =
  let mtv = !*mt in
  RV.free (MT?.hs mtv);
  RV.free (MT?.rhs mtv);
  [@inline_let] let rg = hreg (MT?.hash_size mtv) in
  rg_free rg (MT?.mroot mtv);
  B.free mt
#pop-options

/// Insertion

private
val as_seq_sub_upd:
  #a:Type0 -> #rst:Type -> #rg:regional rst a ->
  h:HS.mem -> rv:rvector #a #rst rg ->
  i:uint32_t{i < V.size_of rv} -> v:Rgl?.repr rg ->
  Lemma (requires (RV.rv_inv h rv))
        (ensures (S.equal (S.upd (RV.as_seq h rv) (U32.v i) v)
                          (S.append
                            (RV.as_seq_sub h rv 0ul i)
                            (S.cons v (RV.as_seq_sub h rv (i + 1ul) (V.size_of rv))))))
#push-options "--z3rlimit 20"
let as_seq_sub_upd #a #rst #rg h rv i v =
  Seq.Properties.slice_upd (RV.as_seq h rv) 0 (U32.v i) (U32.v i) v;
  Seq.Properties.slice_upd (RV.as_seq h rv) (U32.v i + 1) (U32.v (V.size_of rv)) (U32.v i) v;
  RV.as_seq_seq_slice rg h (V.as_seq h rv)
    0 (U32.v (V.size_of rv)) 0 (U32.v i);
  assert (S.equal (S.slice (RV.as_seq h rv) 0 (U32.v i))
                  (RV.as_seq_sub h rv 0ul i));
  RV.as_seq_seq_slice rg h (V.as_seq h rv)
    0 (U32.v (V.size_of rv)) (U32.v i + 1) (U32.v (V.size_of rv));
  assert (S.equal (S.slice (RV.as_seq h rv) (U32.v i + 1) (U32.v (V.size_of rv)))
                  (RV.as_seq_sub h rv (i + 1ul) (V.size_of rv)));
  assert (S.index (S.upd (RV.as_seq h rv) (U32.v i) v) (U32.v i) == v)
#pop-options

// `hash_vv_insert_copy` inserts a hash element at a level `lv`, by copying
// and pushing its content to `hs[lv]`. For detailed insertion procedure, see
// `insert_` and `mt_insert`.
#push-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1"
private
inline_for_extraction
val hash_vv_insert_copy:
  #hsz:hash_size_t ->
  lv:uint32_t{lv < merkle_tree_size_lg} ->
  i:Ghost.erased index_t ->
  j:index_t{
   Ghost.reveal i <= j &&
    U32.v j < pow2 (32 - U32.v lv) - 1 &&
    j < uint32_32_max} ->
  hs:hash_vv hsz {V.size_of hs = merkle_tree_size_lg} ->
  v:hash #hsz ->
  HST.ST unit
    (requires (fun h0 ->
      RV.rv_inv h0 hs /\
      Rgl?.r_inv (hreg hsz) h0 v /\
      HH.disjoint (V.frameOf hs) (B.frameOf v) /\
      mt_safe_elts #hsz h0 lv hs (Ghost.reveal i) j))
    (ensures (fun h0 _ h1 ->
      // memory safety
      modifies (loc_union
                 (RV.rs_loc_elem (hvreg hsz) (V.as_seq h0 hs) (U32.v lv))
                 (V.loc_vector_within hs lv (lv + 1ul)))
               h0 h1 /\
      RV.rv_inv h1 hs /\
      Rgl?.r_inv (hreg hsz) h1 v /\
      V.size_of (V.get h1 hs lv) == j + 1ul - offset_of (Ghost.reveal i) /\
      V.size_of (V.get h1 hs lv) == V.size_of (V.get h0 hs lv) + 1ul /\
      mt_safe_elts #hsz h1 (lv + 1ul) hs (Ghost.reveal i / 2ul) (j / 2ul) /\
      RV.rv_loc_elems h0 hs (lv + 1ul) (V.size_of hs) ==
      RV.rv_loc_elems h1 hs (lv + 1ul) (V.size_of hs) /\
      // correctness
      (mt_safe_elts_spec #hsz h0 lv hs (Ghost.reveal i) j;
      S.equal (RV.as_seq h1 hs)
      (MTH.hashess_insert
        (U32.v lv) (U32.v (Ghost.reveal i)) (U32.v j)
        (RV.as_seq h0 hs) (Rgl?.r_repr (hreg hsz) h0 v))) /\
      S.equal (S.index (RV.as_seq h1 hs) (U32.v lv))
      (S.snoc (S.index (RV.as_seq h0 hs) (U32.v lv))
      (Rgl?.r_repr (hreg hsz) h0 v))))
let hash_vv_insert_copy #hsz lv i j hs v =
  let hh0 = HST.get () in
  mt_safe_elts_rec hh0 lv hs (Ghost.reveal i) j;

  /// 1) Insert an element at the level `lv`, where the new vector is not yet
  /// connected to `hs`.
  let ihv = RV.insert_copy (hcpy hsz) (V.index hs lv) v in
  let hh1 = HST.get () in

  // 1-0) Basic disjointness conditions
  V.forall2_forall_left hh0 hs 0ul (V.size_of hs) lv
    (fun b1 b2 -> HH.disjoint (Rgl?.region_of (hvreg hsz) b1)
                              (Rgl?.region_of (hvreg hsz) b2));
  V.forall2_forall_right hh0 hs 0ul (V.size_of hs) lv
    (fun b1 b2 -> HH.disjoint (Rgl?.region_of (hvreg hsz) b1)
                              (Rgl?.region_of (hvreg hsz) b2));
  V.loc_vector_within_included hs lv (lv + 1ul);
  V.loc_vector_within_included hs (lv + 1ul) (V.size_of hs);
  V.loc_vector_within_disjoint hs lv (lv + 1ul) (lv + 1ul) (V.size_of hs);

  // 1-1) For the `modifies` postcondition.
  assert (modifies (RV.rs_loc_elem (hvreg hsz) (V.as_seq hh0 hs) (U32.v lv)) hh0 hh1);

  // 1-2) Preservation
  Rgl?.r_sep (hreg hsz) v (RV.loc_rvector (V.get hh0 hs lv)) hh0 hh1;
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
    (hvreg hsz) (V.as_seq hh0 hs) (V.frameOf hs)
    0 (U32.v (V.size_of hs)) 0 (U32.v lv) (U32.v lv);
  RV.rs_loc_elems_parent_disj
    (hvreg hsz) (V.as_seq hh0 hs) (V.frameOf hs)
    0 (U32.v lv);
  RV.rv_elems_inv_preserved
    hs 0ul lv (RV.loc_rvector (V.get hh0 hs lv))
    hh0 hh1;
  assert (RV.rv_elems_inv hh1 hs 0ul lv);

  RV.rs_loc_elems_elem_disj
    (hvreg hsz) (V.as_seq hh0 hs) (V.frameOf hs)
    0 (U32.v (V.size_of hs))
    (U32.v lv + 1) (U32.v (V.size_of hs))
    (U32.v lv);
  RV.rs_loc_elems_parent_disj
    (hvreg hsz) (V.as_seq hh0 hs) (V.frameOf hs)
    (U32.v lv + 1) (U32.v (V.size_of hs));
  RV.rv_elems_inv_preserved
    hs (lv + 1ul) (V.size_of hs) (RV.loc_rvector (V.get hh0 hs lv))
    hh0 hh1;
  assert (RV.rv_elems_inv hh1 hs (lv + 1ul) (V.size_of hs));

  // assert (rv_itself_inv hh1 hs);
  // assert (elems_reg hh1 hs);

  // 1-5) Correctness
  assert (S.equal (RV.as_seq hh1 ihv)
                  (S.snoc (RV.as_seq hh0 (V.get hh0 hs lv)) (Rgl?.r_repr (hreg hsz) hh0 v)));

  /// 2) Assign the updated vector to `hs` at the level `lv`.
  RV.assign hs lv ihv;
  let hh2 = HST.get () in

  // 2-1) For the `modifies` postcondition.
  assert (modifies (V.loc_vector_within hs lv (lv + 1ul)) hh1 hh2);
  assert (modifies (loc_union
                     (RV.rs_loc_elem (hvreg hsz) (V.as_seq hh0 hs) (U32.v lv))
                     (V.loc_vector_within hs lv (lv + 1ul))) hh0 hh2);

  // 2-2) Preservation
  Rgl?.r_sep (hreg hsz) v (RV.loc_rvector hs) hh1 hh2;
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
  as_seq_sub_upd hh0 hs lv (RV.as_seq hh1 ihv)
#pop-options

private
val insert_index_helper_even:
  lv:uint32_t{lv < merkle_tree_size_lg} ->
  j:index_t{U32.v j < pow2 (32 - U32.v lv) - 1} ->
  Lemma (requires (j % 2ul <> 1ul))
        (ensures (U32.v j % 2 <> 1 /\ j / 2ul == (j + 1ul) / 2ul))
let insert_index_helper_even lv j = ()

#push-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"
private
val insert_index_helper_odd:
  lv:uint32_t{lv < merkle_tree_size_lg} ->
  i:index_t ->
  j:index_t{i <= j && U32.v j < pow2 (32 - U32.v lv) - 1} ->
  Lemma (requires (j % 2ul = 1ul /\
                  j < uint32_32_max))
        (ensures (U32.v j % 2 = 1 /\
                 U32.v (j / 2ul) < pow2 (32 - U32.v (lv + 1ul)) - 1 /\
                 (j + 1ul) / 2ul == j / 2ul + 1ul /\
                 j - offset_of i > 0ul))
let insert_index_helper_odd lv i j = ()
#pop-options

private
val loc_union_assoc_4:
  a:loc -> b:loc -> c:loc -> d:loc ->
  Lemma (loc_union (loc_union a b) (loc_union c d) ==
        loc_union (loc_union a c) (loc_union b d))
let loc_union_assoc_4 a b c d =
  loc_union_assoc (loc_union a b) c d;
  loc_union_assoc a b c;
  loc_union_assoc a c b;
  loc_union_assoc (loc_union a c) b d

private
val insert_modifies_rec_helper:
  #hsz:hash_size_t ->
  lv:uint32_t{lv < merkle_tree_size_lg} ->
  hs:hash_vv hsz {V.size_of hs = merkle_tree_size_lg} ->
  aloc:loc ->
  h:HS.mem ->
  Lemma (loc_union
          (loc_union
            (loc_union
              (RV.rs_loc_elem (hvreg hsz) (V.as_seq h hs) (U32.v lv))
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
#push-options "--z3rlimit 100 --initial_fuel 2 --max_fuel 2"
let insert_modifies_rec_helper #hsz lv hs aloc h =
  assert (V.loc_vector_within hs lv (V.size_of hs) ==
         loc_union (V.loc_vector_within hs lv (lv + 1ul))
                   (V.loc_vector_within hs (lv + 1ul) (V.size_of hs)));
  RV.rs_loc_elems_rec_inverse (hvreg hsz) (V.as_seq h hs) (U32.v lv) (U32.v (V.size_of hs));
  assert (RV.rv_loc_elems h hs lv (V.size_of hs) ==
         loc_union (RV.rs_loc_elem (hvreg hsz) (V.as_seq h hs) (U32.v lv))
                   (RV.rv_loc_elems h hs (lv + 1ul) (V.size_of hs)));

  // Applying some association rules...
  loc_union_assoc
    (loc_union
      (RV.rs_loc_elem (hvreg hsz) (V.as_seq h hs) (U32.v lv))
      (V.loc_vector_within hs lv (lv + 1ul))) aloc
    (loc_union
      (loc_union
        (RV.rv_loc_elems h hs (lv + 1ul) (V.size_of hs))
        (V.loc_vector_within hs (lv + 1ul) (V.size_of hs)))
      aloc);
  loc_union_assoc
    (loc_union
      (RV.rv_loc_elems h hs (lv + 1ul) (V.size_of hs))
      (V.loc_vector_within hs (lv + 1ul) (V.size_of hs))) aloc aloc;
  loc_union_assoc
    (loc_union
      (RV.rs_loc_elem (hvreg hsz) (V.as_seq h hs) (U32.v lv))
      (V.loc_vector_within hs lv (lv + 1ul)))
    (loc_union
      (RV.rv_loc_elems h hs (lv + 1ul) (V.size_of hs))
      (V.loc_vector_within hs (lv + 1ul) (V.size_of hs)))
    aloc;
  loc_union_assoc_4
    (RV.rs_loc_elem (hvreg hsz) (V.as_seq h hs) (U32.v lv))
    (V.loc_vector_within hs lv (lv + 1ul))
    (RV.rv_loc_elems h hs (lv + 1ul) (V.size_of hs))
    (V.loc_vector_within hs (lv + 1ul) (V.size_of hs))
#pop-options

private
val insert_modifies_union_loc_weakening:
  l1:loc -> l2:loc -> l3:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (modifies l1 h0 h1))
        (ensures (modifies (loc_union (loc_union l1 l2) l3) h0 h1))
let insert_modifies_union_loc_weakening l1 l2 l3 h0 h1 =
  B.loc_includes_union_l l1 l2 l1;
  B.loc_includes_union_l (loc_union l1 l2) l3 (loc_union l1 l2)

private
val insert_snoc_last_helper:
  #a:Type -> s:S.seq a{S.length s > 0} -> v:a ->
  Lemma (S.index (S.snoc s v) (S.length s - 1) == S.last s)
let insert_snoc_last_helper #a s v = ()

private
val rv_inv_rv_elems_reg:
  #a:Type0 -> #rst:Type -> #rg:regional rst a ->
  h:HS.mem -> rv:rvector rg ->
  i:uint32_t -> j:uint32_t{i <= j && j <= V.size_of rv} ->
  Lemma (requires (RV.rv_inv h rv))
        (ensures (RV.rv_elems_reg h rv i j))
let rv_inv_rv_elems_reg #a #rst #rg h rv i j = ()

// `insert_` recursively inserts proper hashes to each level `lv` by
// accumulating a compressed hash. For example, if there are three leaf elements
// in the tree, `insert_` will change `hs` as follow:
// (`hij` is a compressed hash from `hi` to `hj`)
//
//     BEFORE INSERTION        AFTER INSERTION
// lv
// 0   h0  h1  h2       ====>  h0  h1  h2  h3
// 1   h01                     h01 h23
// 2                           h03
//
private
val insert_:
  #hsz:hash_size_t ->
  #hash_spec:Ghost.erased (MTS.hash_fun_t #(U32.v hsz)) ->
  lv:uint32_t{lv < merkle_tree_size_lg} ->
  i:Ghost.erased index_t ->
  j:index_t{
    Ghost.reveal i <= j &&
    U32.v j < pow2 (32 - U32.v lv) - 1 &&
    j < uint32_32_max} ->
  hs:hash_vv hsz {V.size_of hs = merkle_tree_size_lg} ->
  acc:hash #hsz ->
  hash_fun:hash_fun_t #hsz #hash_spec ->
  HST.ST unit
         (requires (fun h0 ->
           RV.rv_inv h0 hs /\
           Rgl?.r_inv (hreg hsz) h0 acc /\
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
           Rgl?.r_inv (hreg hsz) h1 acc /\
           mt_safe_elts h1 lv hs (Ghost.reveal i) (j + 1ul) /\
           // correctness
           (mt_safe_elts_spec h0 lv hs (Ghost.reveal i) j;
           S.equal (RV.as_seq h1 hs)
                   (MTH.insert_ #(U32.v hsz) #hash_spec (U32.v lv) (U32.v (Ghost.reveal i)) (U32.v j)
                     (RV.as_seq h0 hs) (Rgl?.r_repr (hreg hsz) h0 acc)))))
         (decreases (U32.v j))
#push-options "--z3rlimit 800 --initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"
let rec insert_ #hsz #hash_spec lv i j hs acc hash_fun =
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
       assert (Rgl?.r_inv (hreg hsz) hh1 acc);
       hash_fun (V.index lvhs (V.size_of lvhs - 2ul)) acc acc;
       let hh2 = HST.get () in

       // 3-1) For the `modifies` postcondition
       assert (modifies (B.loc_all_regions_from false (B.frameOf acc)) hh1 hh2);
       assert (modifies
                (loc_union
                  (loc_union
                    (RV.rs_loc_elem (hvreg hsz) (V.as_seq hh0 hs) (U32.v lv))
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
       assert (Rgl?.r_inv (hreg hsz) hh2 acc);

       // 3-3) For `mt_safe_elts`
       V.get_preserved hs lv
         (B.loc_region_only false (B.frameOf acc)) hh1 hh2; // head preserved
       mt_safe_elts_preserved
         (lv + 1ul) hs (Ghost.reveal i / 2ul) (j / 2ul)
         (B.loc_region_only false (B.frameOf acc)) hh1 hh2; // tail preserved

       // 3-4) Correctness
       insert_snoc_last_helper
         (RV.as_seq hh0 (V.get hh0 hs lv))
         (Rgl?.r_repr (hreg hsz) hh0 acc);
       assert (S.equal (Rgl?.r_repr (hreg hsz) hh2 acc) // `nacc` in `MTH.insert_`
                       ((Ghost.reveal hash_spec)
                         (S.last (S.index (RV.as_seq hh0 hs) (U32.v lv)))
                         (Rgl?.r_repr (hreg hsz) hh0 acc)));

       /// 4) Recursion
       insert_ (lv + 1ul)
         (Ghost.hide (Ghost.reveal i / 2ul)) (j / 2ul)
         hs acc hash_fun;
       let hh3 = HST.get () in

       // 4-0) Memory safety brought from the postcondition of the recursion
       assert (RV.rv_inv hh3 hs);
       assert (Rgl?.r_inv (hreg hsz) hh3 acc);
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
                      (RV.rs_loc_elem (hvreg hsz) (V.as_seq hh0 hs) (U32.v lv))
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
       (MTH.insert_ #(U32.v hsz) #(Ghost.reveal hash_spec) (U32.v lv + 1) (U32.v (Ghost.reveal i) / 2) (U32.v j / 2)
         (RV.as_seq hh2 hs) (Rgl?.r_repr (hreg hsz) hh2 acc)));
       mt_safe_elts_spec hh0 lv hs (Ghost.reveal i) j;
       MTH.insert_rec #(U32.v hsz) #(Ghost.reveal hash_spec) (U32.v lv) (U32.v (Ghost.reveal i)) (U32.v j)
         (RV.as_seq hh0 hs) (Rgl?.r_repr (hreg hsz) hh0 acc);
       assert (S.equal (RV.as_seq hh3 hs)
       (MTH.insert_ #(U32.v hsz) #(Ghost.reveal hash_spec) (U32.v lv) (U32.v (Ghost.reveal i)) (U32.v j)
         (RV.as_seq hh0 hs) (Rgl?.r_repr (hreg hsz) hh0 acc))))
  else (insert_index_helper_even lv j;
       // memory safety
       assert (mt_safe_elts hh1 (lv + 1ul) hs (Ghost.reveal i / 2ul) ((j + 1ul) / 2ul));
       mt_safe_elts_constr hh1 lv hs (Ghost.reveal i) (j + 1ul);
       assert (mt_safe_elts hh1 lv hs (Ghost.reveal i) (j + 1ul));
       assert (modifies
                (loc_union
                  (RV.rs_loc_elem (hvreg hsz) (V.as_seq hh0 hs) (U32.v lv))
                  (V.loc_vector_within hs lv (lv + 1ul)))
                hh0 hh1);
       insert_modifies_union_loc_weakening
         (loc_union
           (RV.rs_loc_elem (hvreg hsz) (V.as_seq hh0 hs) (U32.v lv))
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
       MTH.insert_base #(U32.v hsz) #(Ghost.reveal hash_spec) (U32.v lv) (U32.v (Ghost.reveal i)) (U32.v j)
         (RV.as_seq hh0 hs) (Rgl?.r_repr (hreg hsz) hh0 acc);
       assert (S.equal (RV.as_seq hh1 hs)
              (MTH.insert_ #(U32.v hsz) #(Ghost.reveal hash_spec) (U32.v lv) (U32.v (Ghost.reveal i)) (U32.v j)
                (RV.as_seq hh0 hs) (Rgl?.r_repr (hreg hsz) hh0 acc))));

  /// 5) Proving the postcondition after recursion
  let hh4 = HST.get () in

  // 5-1) For the `modifies` postcondition.
  assert (modifies
           (loc_union
             (loc_union
               (loc_union
                 (RV.rs_loc_elem (hvreg hsz) (V.as_seq hh0 hs) (U32.v lv))
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
  assert (Rgl?.r_inv (hreg hsz) hh4 acc);

  // 5-4) Correctness
  mt_safe_elts_spec hh0 lv hs (Ghost.reveal i) j;
  assert (S.equal (RV.as_seq hh4 hs)
                  (MTH.insert_ #(U32.v hsz) #hash_spec (U32.v lv) (U32.v (Ghost.reveal i)) (U32.v j)
                    (RV.as_seq hh0 hs) (Rgl?.r_repr (hreg hsz) hh0 acc))) // QED
#pop-options

private inline_for_extraction
val mt_insert_pre_nst: mtv:merkle_tree -> v:hash #(MT?.hash_size mtv) -> Tot bool
let mt_insert_pre_nst mtv v = mt_not_full_nst mtv && add64_fits (MT?.offset mtv) ((MT?.j mtv) + 1ul)

val mt_insert_pre: #hsz:Ghost.erased hash_size_t -> mt:const_mt_p -> v:hash #hsz -> HST.ST bool
  (requires (fun h0 -> mt_safe h0 (CB.cast mt) /\ (MT?.hash_size (B.get h0 (CB.cast mt) 0)) = Ghost.reveal hsz))
  (ensures (fun _ _ _ -> True))
let mt_insert_pre #hsz mt v =
  let mt = !*(CB.cast mt) in
  assert (MT?.hash_size mt == (MT?.hash_size mt));
  mt_insert_pre_nst mt v

// `mt_insert` inserts a hash to a Merkle tree. Note that this operation
// manipulates the content in `v`, since it uses `v` as an accumulator during
// insertion.
#push-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"
val mt_insert:
  hsz:Ghost.erased hash_size_t ->
  mt:mt_p -> v:hash #hsz ->
  HST.ST unit
   (requires (fun h0 ->
     let dmt = B.get h0 mt 0 in
     mt_safe h0 mt /\
     Rgl?.r_inv (hreg hsz) h0 v /\
     HH.disjoint (B.frameOf mt) (B.frameOf v) /\
     MT?.hash_size dmt = Ghost.reveal hsz /\
     mt_insert_pre_nst dmt v))
   (ensures (fun h0 _ h1 ->
     // memory safety
     modifies (loc_union
                (mt_loc mt)
                (B.loc_all_regions_from false (B.frameOf v)))
              h0 h1 /\
     mt_safe h1 mt /\
     // correctness
     MT?.hash_size (B.get h1 mt 0) = Ghost.reveal hsz /\
     mt_lift h1 mt == MTH.mt_insert (mt_lift h0 mt) (Rgl?.r_repr (hreg hsz) h0 v)))
#pop-options
#push-options "--z3rlimit 40"
let mt_insert hsz mt v =
  let hh0 = HST.get () in
  let mtv = !*mt in
  let hs = MT?.hs mtv in
  let hsz = MT?.hash_size mtv in
  insert_ #hsz #(Ghost.reveal (MT?.hash_spec mtv)) 0ul (Ghost.hide (MT?.i mtv)) (MT?.j mtv) hs v (MT?.hash_fun mtv);
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
  Rgl?.r_sep (hreg hsz) (MT?.mroot mtv)
    (loc_union
      (loc_union
        (RV.rv_loc_elems hh0 hs 0ul (V.size_of hs))
        (V.loc_vector_within hs 0ul (V.size_of hs)))
      (B.loc_all_regions_from false (B.frameOf v)))
    hh0 hh1;
  mt *= MT (MT?.hash_size mtv)
           (MT?.offset mtv)
           (MT?.i mtv)
           (MT?.j mtv + 1ul)
           (MT?.hs mtv)
           false // `rhs` is always deprecated right after an insertion.
           (MT?.rhs mtv)
           (MT?.mroot mtv)
           (MT?.hash_spec mtv)
           (MT?.hash_fun mtv);
  let hh2 = HST.get () in
  RV.rv_inv_preserved
    (MT?.hs mtv) (B.loc_buffer mt) hh1 hh2;
  RV.rv_inv_preserved
    (MT?.rhs mtv) (B.loc_buffer mt) hh1 hh2;
  RV.as_seq_preserved
    (MT?.hs mtv) (B.loc_buffer mt) hh1 hh2;
  RV.as_seq_preserved
    (MT?.rhs mtv) (B.loc_buffer mt) hh1 hh2;
  Rgl?.r_sep (hreg hsz) (MT?.mroot mtv) (B.loc_buffer mt) hh1 hh2;
  mt_safe_elts_preserved
    0ul (MT?.hs mtv) (MT?.i mtv) (MT?.j mtv + 1ul) (B.loc_buffer mt)
    hh1 hh2
#pop-options

// `mt_create` initiates a Merkle tree with a given initial hash `init`.
// A valid Merkle tree should contain at least one element.
val mt_create_custom:
  hsz:hash_size_t ->
  hash_spec:Ghost.erased (MTS.hash_fun_t #(U32.v hsz)) ->
  r:HST.erid -> init:hash #hsz -> hash_fun:hash_fun_t #hsz #hash_spec -> HST.ST mt_p
   (requires (fun h0 ->
     Rgl?.r_inv (hreg hsz) h0 init /\
     HH.disjoint r (B.frameOf init)))
   (ensures (fun h0 mt h1 ->
     // memory safety
     modifies (loc_union (mt_loc mt) (B.loc_all_regions_from false (B.frameOf init))) h0 h1 /\
     mt_safe h1 mt /\
     // correctness
     MT?.hash_size (B.get h1 mt 0) = hsz /\
     mt_lift h1 mt == MTH.mt_create (U32.v hsz) (Ghost.reveal hash_spec) (Rgl?.r_repr (hreg hsz) h0 init)))
#push-options "--z3rlimit 40"
let mt_create_custom hsz hash_spec r init hash_fun =
  let hh0 = HST.get () in
  let mt = create_empty_mt hsz hash_spec hash_fun r in
  mt_insert hsz mt init;
  let hh2 = HST.get () in
  mt
#pop-options

/// Construction and Destruction of paths

// Since each element pointer in `path` is from the target Merkle tree and
// each element has different location in `MT?.hs` (thus different region id),
// we cannot use the regionality property for `path`s. Hence here we manually
// define invariants and representation.
noeq type path =
| Path: hash_size:hash_size_t ->
        hashes:V.vector (hash #hash_size) ->
        path
type path_p = B.pointer path
type const_path_p = const_pointer path

private
let phashes (h:HS.mem) (p:path_p)
: GTot (V.vector (hash #(Path?.hash_size (B.get h p 0)))) 
= Path?.hashes (B.get h p 0)

// Memory safety of a path as an invariant
inline_for_extraction noextract
val path_safe:
  h:HS.mem -> mtr:HH.rid -> p:path_p -> GTot Type0
let path_safe h mtr p =
  B.live h p /\ B.freeable p /\
  V.live h (phashes h p) /\ V.freeable (phashes h p) /\
  HST.is_eternal_region (V.frameOf (phashes h p)) /\
  (let hsz = Path?.hash_size (B.get h p 0) in
  V.forall_all h (phashes h p)
    (fun hp -> Rgl?.r_inv (hreg hsz) h hp /\
               HH.includes mtr (Rgl?.region_of (hreg hsz) hp)) /\
  HH.extends (V.frameOf (phashes h p)) (B.frameOf p) /\
  HH.disjoint mtr (B.frameOf p))

val path_loc: path_p -> GTot loc
let path_loc p = B.loc_all_regions_from false (B.frameOf p)

val lift_path_:
  #hsz:hash_size_t ->
  h:HS.mem ->
  hs:S.seq (hash #hsz) ->
  i:nat ->
  j:nat{
    i <= j /\ j <= S.length hs /\
    V.forall_seq hs i j (fun hp -> Rgl?.r_inv (hreg hsz) h hp)} ->
  GTot (hp:MTH.path #(U32.v hsz) {S.length hp = j - i}) (decreases j)
let rec lift_path_ #hsz h hs i j =
  if i = j then S.empty
  else (S.snoc (lift_path_ h hs i (j - 1))
               (Rgl?.r_repr (hreg hsz) h (S.index hs (j - 1))))

// Representation of a path
val lift_path:
  #hsz:hash_size_t ->
  h:HS.mem -> mtr:HH.rid -> p:path_p {path_safe h mtr p /\ (Path?.hash_size (B.get h p 0)) = hsz} ->
  GTot (hp:MTH.path #(U32.v hsz) {S.length hp = U32.v (V.size_of (phashes h p))})
let lift_path #hsz h mtr p =
  lift_path_ h (V.as_seq h (phashes h p))
    0 (S.length (V.as_seq h (phashes h p)))

val lift_path_index_:
  #hsz:hash_size_t ->
  h:HS.mem ->
  hs:S.seq (hash #hsz) ->
  i:nat -> j:nat{i <= j && j <= S.length hs} ->
  k:nat{i <= k && k < j} ->
  Lemma (requires (V.forall_seq hs i j (fun hp -> Rgl?.r_inv (hreg hsz) h hp)))
        (ensures (Rgl?.r_repr (hreg hsz) h (S.index hs k) ==
                 S.index (lift_path_ h hs i j) (k - i)))
        (decreases j)
        [SMTPat (S.index (lift_path_ h hs i j) (k - i))]
#push-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"
let rec lift_path_index_ #hsz h hs i j k =
  if i = j then ()
  else if k = j - 1 then ()
  else lift_path_index_ #hsz h hs i (j - 1) k
#pop-options

val lift_path_index:
  h:HS.mem -> mtr:HH.rid ->
  p:path_p -> i:uint32_t ->
  Lemma (requires (path_safe h mtr p /\
                  i < V.size_of (phashes h p)))
        (ensures (let hsz = Path?.hash_size (B.get h p 0) in
                 Rgl?.r_repr (hreg hsz) h (V.get h (phashes h p) i) ==
                 S.index (lift_path #(hsz) h mtr p) (U32.v i)))
let lift_path_index h mtr p i =
  lift_path_index_ h (V.as_seq h (phashes h p))
    0 (S.length (V.as_seq h (phashes h p))) (U32.v i)

val lift_path_eq:
  #hsz:hash_size_t ->
  h:HS.mem ->
  hs1:S.seq (hash #hsz) -> hs2:S.seq (hash #hsz) ->
  i:nat -> j:nat ->
  Lemma (requires (i <= j /\ j <= S.length hs1 /\ j <= S.length hs2 /\
                  S.equal (S.slice hs1 i j) (S.slice hs2 i j) /\
                  V.forall_seq hs1 i j (fun hp -> Rgl?.r_inv (hreg hsz) h hp) /\
                  V.forall_seq hs2 i j (fun hp -> Rgl?.r_inv (hreg hsz) h hp)))
        (ensures (S.equal (lift_path_ h hs1 i j) (lift_path_ h hs2 i j)))
let lift_path_eq #hsz h hs1 hs2 i j =
  assert (forall (k:nat{i <= k && k < j}).
           S.index (lift_path_ h hs1 i j) (k - i) ==
           Rgl?.r_repr (hreg hsz) h (S.index hs1 k));
  assert (forall (k:nat{i <= k && k < j}).
           S.index (lift_path_ h hs2 i j) (k - i) ==
           Rgl?.r_repr (hreg hsz) h (S.index hs2 k));
  assert (forall (k:nat{k < j - i}).
           S.index (lift_path_ h hs1 i j) k ==
           Rgl?.r_repr (hreg hsz) h (S.index hs1 (k + i)));
  assert (forall (k:nat{k < j - i}).
           S.index (lift_path_ h hs2 i j) k ==
           Rgl?.r_repr (hreg hsz) h (S.index hs2 (k + i)));
  assert (forall (k:nat{k < j - i}).
           S.index (S.slice hs1 i j) k == S.index (S.slice hs2 i j) k);
  assert (forall (k:nat{i <= k && k < j}).
           S.index (S.slice hs1 i j) (k - i) == S.index (S.slice hs2 i j) (k - i))

private
val path_safe_preserved_:
  #hsz:hash_size_t ->
  mtr:HH.rid -> hs:S.seq (hash #hsz) ->
  i:nat -> j:nat{i <= j && j <= S.length hs} ->
  dl:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma
    (requires (V.forall_seq hs i j
                (fun hp ->
                  Rgl?.r_inv (hreg hsz) h0 hp /\
                  HH.includes mtr (Rgl?.region_of (hreg hsz) hp)) /\
              loc_disjoint dl (B.loc_all_regions_from false mtr) /\
              modifies dl h0 h1))
    (ensures (V.forall_seq hs i j
               (fun hp ->
                 Rgl?.r_inv (hreg hsz) h1 hp /\
                 HH.includes mtr (Rgl?.region_of (hreg hsz) hp))))
    (decreases j)
let rec path_safe_preserved_ #hsz mtr hs i j dl h0 h1 =
  if i = j then ()
  else (assert (loc_includes
                 (B.loc_all_regions_from false mtr)
                 (B.loc_all_regions_from false
                   (Rgl?.region_of (hreg hsz) (S.index hs (j - 1)))));
       Rgl?.r_sep (hreg hsz) (S.index hs (j - 1)) dl h0 h1;
       path_safe_preserved_ mtr hs i (j - 1) dl h0 h1)

val path_safe_preserved:
  mtr:HH.rid -> p:path_p ->
  dl:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (path_safe h0 mtr p /\
                  loc_disjoint dl (path_loc p) /\
                  loc_disjoint dl (B.loc_all_regions_from false mtr) /\
                  modifies dl h0 h1))
        (ensures (path_safe h1 mtr p))
let path_safe_preserved mtr p dl h0 h1 =
  assert (loc_includes (path_loc p) (B.loc_buffer p));
  assert (loc_includes (path_loc p) (V.loc_vector (phashes h0 p)));
  path_safe_preserved_
    mtr (V.as_seq h0 (phashes h0 p))
    0 (S.length (V.as_seq h0 (phashes h0 p))) dl h0 h1

val path_safe_init_preserved:
  mtr:HH.rid -> p:path_p ->
  dl:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (path_safe h0 mtr p /\
                  V.size_of (phashes h0 p) = 0ul /\
                  B.loc_disjoint dl (path_loc p) /\
                  modifies dl h0 h1))
        (ensures (path_safe h1 mtr p /\
                 V.size_of (phashes h1 p) = 0ul))
let path_safe_init_preserved mtr p dl h0 h1 =
  assert (loc_includes (path_loc p) (B.loc_buffer p));
  assert (loc_includes (path_loc p) (V.loc_vector (phashes h0 p)))

val path_preserved_:
  #hsz:hash_size_t ->
  mtr:HH.rid ->
  hs:S.seq (hash #hsz) ->
  i:nat -> j:nat{i <= j && j <= S.length hs} ->
  dl:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (V.forall_seq hs i j
                    (fun hp -> Rgl?.r_inv (hreg hsz) h0 hp /\
                               HH.includes mtr (Rgl?.region_of (hreg hsz) hp)) /\
                  loc_disjoint dl (B.loc_all_regions_from false mtr) /\
                  modifies dl h0 h1))
        (ensures (path_safe_preserved_ mtr hs i j dl h0 h1;
                 S.equal (lift_path_ h0 hs i j)
                         (lift_path_ h1 hs i j)))
        (decreases j)
#push-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"
let rec path_preserved_ #hsz mtr hs i j dl h0 h1 =
  if i = j then ()
  else (path_safe_preserved_ mtr hs i (j - 1) dl h0 h1;
       path_preserved_ mtr hs i (j - 1) dl h0 h1;
       assert (loc_includes
                (B.loc_all_regions_from false mtr)
                (B.loc_all_regions_from false
                  (Rgl?.region_of (hreg hsz) (S.index hs (j - 1)))));
       Rgl?.r_sep (hreg hsz) (S.index hs (j - 1)) dl h0 h1)
#pop-options

val path_preserved:
  mtr:HH.rid -> p:path_p ->
  dl:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (path_safe h0 mtr p /\
                  loc_disjoint dl (path_loc p) /\
                  loc_disjoint dl (B.loc_all_regions_from false mtr) /\
                  modifies dl h0 h1))
        (ensures (path_safe_preserved mtr p dl h0 h1;                 
                 let hsz0 = (Path?.hash_size (B.get h0 p 0)) in
                 let hsz1 = (Path?.hash_size (B.get h1 p 0)) in
                 let b:MTH.path = lift_path #hsz0 h0 mtr p in
                 let a:MTH.path = lift_path #hsz1 h1 mtr p in
                 hsz0 = hsz1 /\ S.equal b a))
let path_preserved mtr p dl h0 h1 =
  assert (loc_includes (path_loc p) (B.loc_buffer p));
  assert (loc_includes (path_loc p) (V.loc_vector (phashes h0 p)));
  path_preserved_ mtr (V.as_seq h0 (phashes h0 p))
    0 (S.length (V.as_seq h0 (phashes h0 p)))
    dl h0 h1

val init_path:
  hsz:hash_size_t ->
  mtr:HH.rid -> r:HST.erid ->
  HST.ST path_p
    (requires (fun h0 -> HH.disjoint mtr r))
    (ensures (fun h0 p h1 ->
      // memory safety
      path_safe h1 mtr p /\
      // correctness
      Path?.hash_size (B.get h1 p 0) = hsz /\
      S.equal (lift_path #hsz h1 mtr p) S.empty))
let init_path hsz mtr r =
  let nrid = HST.new_region r in
  (B.malloc r (Path hsz (rg_alloc (hvreg hsz) nrid)) 1ul)

val clear_path:
  mtr:HH.rid -> p:path_p ->
  HST.ST unit
    (requires (fun h0 -> path_safe h0 mtr p))
    (ensures (fun h0 _ h1 ->
      // memory safety
      path_safe h1 mtr p /\
      // correctness
      V.size_of (phashes h1 p) = 0ul /\
      S.equal (lift_path #(Path?.hash_size (B.get h1 p 0)) h1 mtr p) S.empty))
let clear_path mtr p =
  let pv = !*p in
  p *= Path (Path?.hash_size pv) (V.clear (Path?.hashes pv))

val free_path:
  p:path_p ->
  HST.ST unit
    (requires (fun h0 ->
      B.live h0 p /\ B.freeable p /\
      V.live h0 (phashes h0 p) /\ V.freeable (phashes h0 p) /\
      HH.extends (V.frameOf (phashes h0 p)) (B.frameOf p)))
    (ensures (fun h0 _ h1 ->
      modifies (path_loc p) h0 h1))
let free_path p =
  let pv = !*p in
  V.free (Path?.hashes pv);
  B.free p

/// Getting the Merkle root and path

// Construct "rightmost hashes" for a given (incomplete) Merkle tree.
// This function calculates the Merkle root as well, which is the final
// accumulator value.
private
val construct_rhs:
  #hsz:hash_size_t ->
  #hash_spec:Ghost.erased (MTS.hash_fun_t #(U32.v hsz)) ->
  lv:uint32_t{lv <= merkle_tree_size_lg} ->
  hs:hash_vv hsz {V.size_of hs = merkle_tree_size_lg} ->
  rhs:hash_vec #hsz {V.size_of rhs = merkle_tree_size_lg} ->
  i:index_t ->
  j:index_t{i <= j && (U32.v j) < pow2 (32 - U32.v lv)} ->
  acc:hash #hsz ->
  actd:bool ->
  hash_fun:hash_fun_t #hsz #(Ghost.reveal hash_spec) ->
  HST.ST unit
   (requires (fun h0 ->
     RV.rv_inv h0 hs /\ RV.rv_inv h0 rhs /\
     HH.disjoint (V.frameOf hs) (V.frameOf rhs) /\
     Rgl?.r_inv (hreg hsz) h0 acc /\
     HH.disjoint (B.frameOf acc) (V.frameOf hs) /\
     HH.disjoint (B.frameOf acc) (V.frameOf rhs) /\
     mt_safe_elts #hsz h0 lv hs i j))
   (ensures (fun h0 _ h1 ->
     // memory safety
     modifies (loc_union
                (RV.loc_rvector rhs)
                (B.loc_all_regions_from false (B.frameOf acc)))
              h0 h1 /\
     RV.rv_inv h1 rhs /\
     Rgl?.r_inv (hreg hsz) h1 acc /\
     // correctness
     (mt_safe_elts_spec #hsz h0 lv hs i j;
     MTH.construct_rhs #(U32.v hsz) #(Ghost.reveal hash_spec)
       (U32.v lv)
       (Rgl?.r_repr (hvvreg hsz) h0 hs)
       (Rgl?.r_repr (hvreg hsz) h0 rhs)
       (U32.v i) (U32.v j)
       (Rgl?.r_repr (hreg hsz) h0 acc) actd ==
     (Rgl?.r_repr (hvreg hsz) h1 rhs, Rgl?.r_repr (hreg hsz) h1 acc)
     )))
   (decreases (U32.v j))

#push-options "--z3rlimit 250 --initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"
let rec construct_rhs #hsz #hash_spec lv hs rhs i j acc actd hash_fun =
  let hh0 = HST.get () in

  if j = 0ul then begin
    assert (RV.rv_inv hh0 hs);
    assert (mt_safe_elts #hsz hh0 lv hs i j);
    mt_safe_elts_spec #hsz hh0 lv hs 0ul 0ul;
    assert (MTH.hs_wf_elts #(U32.v hsz)
                           (U32.v lv) (RV.as_seq hh0 hs)
                           (U32.v i) (U32.v j));
    let hh1 = HST.get() in
    assert (MTH.construct_rhs #(U32.v hsz) #(Ghost.reveal hash_spec)
                              (U32.v lv)
                              (Rgl?.r_repr (hvvreg hsz) hh0 hs)
                              (Rgl?.r_repr (hvreg hsz) hh0 rhs)
                              (U32.v i) (U32.v j)
           (Rgl?.r_repr (hreg hsz) hh0 acc) actd ==
             (Rgl?.r_repr (hvreg hsz) hh1 rhs, Rgl?.r_repr (hreg hsz) hh1 acc))
  end
  else
    let ofs = offset_of i in
    begin
    (if j % 2ul = 0ul
    then begin
      Math.Lemmas.pow2_double_mult (32 - U32.v lv - 1);
      mt_safe_elts_rec #hsz hh0 lv hs i j;
      construct_rhs #hsz #hash_spec (lv + 1ul) hs rhs (i / 2ul) (j / 2ul) acc actd hash_fun;
      let hh1 = HST.get () in
      // correctness
      mt_safe_elts_spec #hsz hh0 lv hs i j;
      MTH.construct_rhs_even #(U32.v hsz) #hash_spec
        (U32.v lv) (Rgl?.r_repr (hvvreg hsz) hh0 hs) (Rgl?.r_repr (hvreg hsz) hh0 rhs)
        (U32.v i) (U32.v j) (Rgl?.r_repr (hreg hsz) hh0 acc) actd;
      assert (MTH.construct_rhs #(U32.v hsz) #hash_spec
               (U32.v lv)
               (Rgl?.r_repr (hvvreg hsz) hh0 hs)
               (Rgl?.r_repr (hvreg hsz) hh0 rhs)
               (U32.v i) (U32.v j)
               (Rgl?.r_repr (hreg hsz) hh0 acc)
               actd ==
             (Rgl?.r_repr (hvreg hsz) hh1 rhs, Rgl?.r_repr (hreg hsz) hh1 acc))
    end
    else begin
      if actd
      then begin
        RV.assign_copy (hcpy hsz) rhs lv acc;        
        let hh1 = HST.get () in
        // memory safety
        Rgl?.r_sep (hreg hsz) acc
          (B.loc_all_regions_from false (V.frameOf rhs)) hh0 hh1;
        RV.rv_inv_preserved
          hs (B.loc_all_regions_from false (V.frameOf rhs))
          hh0 hh1;
        RV.as_seq_preserved
          hs (B.loc_all_regions_from false (V.frameOf rhs))
          hh0 hh1;
        RV.rv_inv_preserved
          (V.get hh0 hs lv) (B.loc_all_regions_from false (V.frameOf rhs))
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
                               (Rgl?.r_repr (hreg hsz) hh0 acc)));

        hash_fun (V.index (V.index hs lv) (j - 1ul - ofs)) acc acc;
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
        assert (Rgl?.r_repr (hreg hsz) hh2 acc ==
               (Ghost.reveal hash_spec) (S.index (S.index (RV.as_seq hh0 hs) (U32.v lv))
                                        (U32.v j - 1 - U32.v ofs))
               (Rgl?.r_repr (hreg hsz) hh0 acc))
      end
      else begin
        mt_safe_elts_head hh0 lv hs i j;
        hash_vv_rv_inv_r_inv hh0 hs lv (j - 1ul - ofs);
        hash_vv_rv_inv_disjoint hh0 hs lv (j - 1ul - ofs) (B.frameOf acc);
        Cpy?.copy (hcpy hsz) hsz (V.index (V.index hs lv) (j - 1ul - ofs)) acc;
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
        assert (Rgl?.r_repr (hreg hsz) hh1 acc ==
                 S.index (S.index (RV.as_seq hh0 hs) (U32.v lv))
                         (U32.v j - 1 - U32.v ofs))
      end;
      let hh3 = HST.get () in
      assert (S.equal (RV.as_seq hh3 hs) (RV.as_seq hh0 hs));
      assert (S.equal (RV.as_seq hh3 rhs)
                      (if actd
                      then S.upd (RV.as_seq hh0 rhs) (U32.v lv)
                                 (Rgl?.r_repr (hreg hsz) hh0 acc)
                      else RV.as_seq hh0 rhs));
      assert (Rgl?.r_repr (hreg hsz) hh3 acc ==
             (if actd
             then (Ghost.reveal hash_spec) (S.index (S.index (RV.as_seq hh0 hs) (U32.v lv))
                                           (U32.v j - 1 - U32.v ofs))
                              (Rgl?.r_repr (hreg hsz) hh0 acc)
             else S.index (S.index (RV.as_seq hh0 hs) (U32.v lv))
                          (U32.v j - 1 - U32.v ofs)));

      mt_safe_elts_rec hh3 lv hs i j;
      construct_rhs #hsz #hash_spec (lv + 1ul) hs rhs (i / 2ul) (j / 2ul) acc true hash_fun;
      let hh4 = HST.get () in
      mt_safe_elts_spec hh3 (lv + 1ul) hs (i / 2ul) (j / 2ul);
      assert (MTH.construct_rhs #(U32.v hsz) #hash_spec
               (U32.v lv + 1)
               (Rgl?.r_repr (hvvreg hsz) hh3 hs)
               (Rgl?.r_repr (hvreg hsz) hh3 rhs)
               (U32.v i / 2) (U32.v j / 2)
               (Rgl?.r_repr (hreg hsz) hh3 acc) true ==
             (Rgl?.r_repr (hvreg hsz) hh4 rhs, Rgl?.r_repr (hreg hsz) hh4 acc));
      mt_safe_elts_spec hh0 lv hs i j;
      MTH.construct_rhs_odd #(U32.v hsz) #hash_spec
        (U32.v lv) (Rgl?.r_repr (hvvreg hsz) hh0 hs) (Rgl?.r_repr (hvreg hsz) hh0 rhs)
        (U32.v i) (U32.v j) (Rgl?.r_repr (hreg hsz) hh0 acc) actd;
      assert (MTH.construct_rhs #(U32.v hsz) #hash_spec
               (U32.v lv)
               (Rgl?.r_repr (hvvreg hsz) hh0 hs)
               (Rgl?.r_repr (hvreg hsz) hh0 rhs)
               (U32.v i) (U32.v j)
               (Rgl?.r_repr (hreg hsz) hh0 acc) actd ==
             (Rgl?.r_repr (hvreg hsz) hh4 rhs, Rgl?.r_repr (hreg hsz) hh4 acc))
    end)
  end
#pop-options

private inline_for_extraction
val mt_get_root_pre_nst: mtv:merkle_tree -> rt:hash #(MT?.hash_size mtv) -> Tot bool
let mt_get_root_pre_nst mtv rt = true

val mt_get_root_pre:
  #hsz:Ghost.erased hash_size_t ->
  mt:const_mt_p ->
  rt:hash #hsz ->
  HST.ST bool
   (requires (fun h0 ->
     let mt = CB.cast mt in
     MT?.hash_size (B.get h0 mt 0) = Ghost.reveal hsz /\
     mt_safe h0 mt /\ Rgl?.r_inv (hreg hsz) h0 rt /\
     HH.disjoint (B.frameOf mt) (B.frameOf rt)))
   (ensures (fun _ _ _ -> True))
let mt_get_root_pre #hsz mt rt =
  let mt = CB.cast mt in
  let mt = !*mt in
  let hsz = MT?.hash_size mt in
  assert (MT?.hash_size mt = hsz);
  mt_get_root_pre_nst mt rt

// `mt_get_root` returns the Merkle root. If it's already calculated with
// up-to-date hashes, the root is returned immediately. Otherwise it calls
// `construct_rhs` to build rightmost hashes and to calculate the Merkle root
// as well.
val mt_get_root:
  #hsz:Ghost.erased hash_size_t ->
  mt:const_mt_p ->
  rt:hash #hsz ->
  HST.ST unit
   (requires (fun h0 ->
     let mt = CB.cast mt in
     let dmt = B.get h0 mt 0 in
     MT?.hash_size dmt = (Ghost.reveal hsz) /\
     mt_get_root_pre_nst dmt rt /\
     mt_safe h0 mt /\ Rgl?.r_inv (hreg hsz) h0 rt /\
     HH.disjoint (B.frameOf mt) (B.frameOf rt)))
   (ensures (fun h0 _ h1 ->
     let mt = CB.cast mt in
     // memory safety
     modifies (loc_union
                (mt_loc mt)
                (B.loc_all_regions_from false (B.frameOf rt)))
              h0 h1 /\
     mt_safe h1 mt /\
     (let mtv0 = B.get h0 mt 0 in
     let mtv1 = B.get h1 mt 0 in
     MT?.hash_size mtv0 = (Ghost.reveal hsz) /\
     MT?.hash_size mtv1 = (Ghost.reveal hsz) /\
     MT?.i mtv1 = MT?.i mtv0 /\ MT?.j mtv1 = MT?.j mtv0 /\
     MT?.hs mtv1 == MT?.hs mtv0 /\ MT?.rhs mtv1 == MT?.rhs mtv0 /\
     MT?.offset mtv1 == MT?.offset mtv0 /\
     MT?.rhs_ok mtv1 = true /\
     Rgl?.r_inv (hreg hsz) h1 rt /\
     // correctness
     MTH.mt_get_root (mt_lift h0 mt) (Rgl?.r_repr (hreg hsz) h0 rt) ==
     (mt_lift h1 mt, Rgl?.r_repr (hreg hsz) h1 rt))))
#push-options "--z3rlimit 150 --initial_fuel 1 --max_fuel 1"
let mt_get_root #hsz mt rt =
  let mt = CB.cast mt in
  let hh0 = HST.get () in
  let mtv = !*mt in
  let prefix = MT?.offset mtv in
  let i = MT?.i mtv in
  let j = MT?.j mtv in
  let hs = MT?.hs mtv in
  let rhs = MT?.rhs mtv in
  let mroot = MT?.mroot mtv in
  let hash_size = MT?.hash_size mtv in
  let hash_spec = MT?.hash_spec mtv in
  let hash_fun = MT?.hash_fun mtv in
  if MT?.rhs_ok mtv
  then begin
    Cpy?.copy (hcpy hash_size) hash_size mroot rt;
    let hh1 = HST.get () in
    mt_safe_preserved mt
      (B.loc_all_regions_from false (Rgl?.region_of (hreg hsz) rt)) hh0 hh1;
    mt_preserved mt
      (B.loc_all_regions_from false (Rgl?.region_of (hreg hsz) rt)) hh0 hh1;
    MTH.mt_get_root_rhs_ok_true
      (mt_lift hh0 mt) (Rgl?.r_repr (hreg hsz) hh0 rt);
    assert (MTH.mt_get_root (mt_lift hh0 mt) (Rgl?.r_repr (hreg hsz) hh0 rt) ==
           (mt_lift hh1 mt, Rgl?.r_repr (hreg hsz) hh1 rt))
  end
  else begin
    construct_rhs #hash_size #hash_spec 0ul hs rhs i j rt false hash_fun;
    let hh1 = HST.get () in
    // memory safety
    assert (RV.rv_inv hh1 rhs);
    assert (Rgl?.r_inv (hreg hsz) hh1 rt);
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
    assert (MTH.construct_rhs #(U32.v hash_size) #hash_spec 0
             (Rgl?.r_repr (hvvreg hsz) hh0 hs)
             (Rgl?.r_repr (hvreg hsz) hh0 rhs)
             (U32.v i) (U32.v j)
             (Rgl?.r_repr (hreg hsz) hh0 rt) false ==
           (Rgl?.r_repr (hvreg hsz) hh1 rhs, Rgl?.r_repr (hreg hsz) hh1 rt));

    Cpy?.copy (hcpy hash_size) hash_size rt mroot;
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
    assert (Rgl?.r_repr (hreg hsz) hh2 mroot == Rgl?.r_repr (hreg hsz) hh1 rt);

    mt *= MT hash_size prefix i j hs true rhs mroot hash_spec hash_fun;
    let hh3 = HST.get () in
    // memory safety
    Rgl?.r_sep (hreg hsz) rt (B.loc_buffer mt) hh2 hh3;
    RV.rv_inv_preserved hs (B.loc_buffer mt) hh2 hh3;
    RV.rv_inv_preserved rhs (B.loc_buffer mt) hh2 hh3;
    RV.as_seq_preserved hs (B.loc_buffer mt) hh2 hh3;
    RV.as_seq_preserved rhs (B.loc_buffer mt) hh2 hh3;
    Rgl?.r_sep (hreg hsz) mroot (B.loc_buffer mt) hh2 hh3;
    mt_safe_elts_preserved 0ul hs i j
      (B.loc_buffer mt) hh2 hh3;
    assert (mt_safe hh3 mt);

    // correctness
    MTH.mt_get_root_rhs_ok_false
      (mt_lift hh0 mt) (Rgl?.r_repr (hreg hsz) hh0 rt);
    assert (MTH.mt_get_root (mt_lift hh0 mt) (Rgl?.r_repr (hreg hsz) hh0 rt) ==
           (MTH.MT #(U32.v hash_size)
                   (U32.v i) (U32.v j)
                   (RV.as_seq hh0 hs)
                   true
                   (RV.as_seq hh1 rhs)
                   (Rgl?.r_repr (hreg hsz) hh1 rt)
                   hash_spec,
                   Rgl?.r_repr (hreg hsz) hh1 rt));
    assert (MTH.mt_get_root (mt_lift hh0 mt) (Rgl?.r_repr (hreg hsz) hh0 rt) ==
           (mt_lift hh3 mt, Rgl?.r_repr (hreg hsz) hh3 rt))
  end
#pop-options

inline_for_extraction
val mt_path_insert:
  #hsz:hash_size_t ->
  mtr:HH.rid -> p:path_p -> hp:hash #hsz ->
  HST.ST unit
    (requires (fun h0 ->
      path_safe h0 mtr p /\
      not (V.is_full (phashes h0 p)) /\
     Rgl?.r_inv (hreg hsz) h0 hp /\
      HH.disjoint mtr (B.frameOf p) /\
      HH.includes mtr (B.frameOf hp) /\
      Path?.hash_size (B.get h0 p 0) = hsz))
    (ensures (fun h0 _ h1 ->      
      // memory safety
      modifies (path_loc p) h0 h1 /\
      path_safe h1 mtr p /\      
      // correctness
      (let hsz0 = Path?.hash_size (B.get h0 p 0) in
       let hsz1 = Path?.hash_size (B.get h1 p 0) in
       (let before:(S.seq (MTH.hash #(U32.v hsz0))) = lift_path h0 mtr p in       
        let after:(S.seq (MTH.hash #(U32.v hsz1))) = lift_path h1 mtr p in
        V.size_of (phashes h1 p) = V.size_of (phashes h0 p) + 1ul /\
        hsz = hsz0 /\ hsz = hsz1 /\        
        (let hspec:(S.seq (MTH.hash #(U32.v hsz))) = (MTH.path_insert #(U32.v hsz) before (Rgl?.r_repr (hreg hsz) h0 hp)) in
          S.equal hspec after)))))
#push-options "--z3rlimit 20 --initial_fuel 1 --max_fuel 1"
let mt_path_insert #hsz mtr p hp =  
  let pth = !*p in
  let pv = Path?.hashes pth in
  let hh0 = HST.get () in
  let ipv = V.insert pv hp in
  let hh1 = HST.get () in
  path_safe_preserved_
    mtr (V.as_seq hh0 pv) 0 (S.length (V.as_seq hh0 pv))
    (B.loc_all_regions_from false (V.frameOf ipv)) hh0 hh1;
  path_preserved_
    mtr (V.as_seq hh0 pv) 0 (S.length (V.as_seq hh0 pv))
    (B.loc_all_regions_from false (V.frameOf ipv)) hh0 hh1;
  Rgl?.r_sep (hreg hsz) hp
    (B.loc_all_regions_from false (V.frameOf ipv)) hh0 hh1;
  p *= Path hsz ipv;
  let hh2 = HST.get () in
  path_safe_preserved_
    mtr (V.as_seq hh1 ipv) 0 (S.length (V.as_seq hh1 ipv))
    (B.loc_region_only false (B.frameOf p)) hh1 hh2;
  path_preserved_
    mtr (V.as_seq hh1 ipv) 0 (S.length (V.as_seq hh1 ipv))
    (B.loc_region_only false (B.frameOf p)) hh1 hh2;
  Rgl?.r_sep (hreg hsz) hp
    (B.loc_region_only false (B.frameOf p)) hh1 hh2;
  assert (S.equal (lift_path hh2 mtr p)
                  (lift_path_ hh1 (S.snoc (V.as_seq hh0 pv) hp)
                    0 (S.length (V.as_seq hh1 ipv))));
  lift_path_eq hh1 (S.snoc (V.as_seq hh0 pv) hp) (V.as_seq hh0 pv)
    0 (S.length (V.as_seq hh0 pv))
#pop-options

// For given a target index `k`, the number of elements (in the tree) `j`,
// and a boolean flag (to check the existence of rightmost hashes), we can
// calculate a required Merkle path length.
//
// `mt_path_length` is a postcondition of `mt_get_path`, and a precondition
// of `mt_verify`. For detailed description, see `mt_get_path` and `mt_verify`.
private
val mt_path_length_step:
  k:index_t ->
  j:index_t{k <= j} ->
  actd:bool ->
  Tot (sl:uint32_t{U32.v sl = MTH.mt_path_length_step (U32.v k) (U32.v j) actd})
let mt_path_length_step k j actd =
  if j = 0ul then 0ul
  else (if k % 2ul = 0ul
       then (if j = k || (j = k + 1ul && not actd) then 0ul else 1ul)
       else 1ul)

private inline_for_extraction
val mt_path_length:
  lv:uint32_t{lv <= merkle_tree_size_lg} ->
  k:index_t ->
  j:index_t{k <= j && U32.v j < pow2 (32 - U32.v lv)} ->
  actd:bool ->
  Tot (l:uint32_t{
        U32.v l = MTH.mt_path_length (U32.v k) (U32.v j) actd &&
        l <= 32ul - lv})
      (decreases (U32.v j))
#push-options "--z3rlimit 10 --initial_fuel 1 --max_fuel 1"
let rec mt_path_length lv k j actd =
  if j = 0ul then 0ul
  else (let nactd = actd || (j % 2ul = 1ul) in
       mt_path_length_step k j actd +
       mt_path_length (lv + 1ul) (k / 2ul) (j / 2ul) nactd)
#pop-options

val mt_get_path_length:
  mtr:HH.rid ->
  p:const_path_p ->
  HST.ST uint32_t 
    (requires (fun h0 -> path_safe h0 mtr (CB.cast p)))
    (ensures (fun h0 _ h1 -> True))
let mt_get_path_length mtr p = 
  let pd = !*(CB.cast p) in
  V.size_of (Path?.hashes pd)

private inline_for_extraction
val mt_make_path_step:
  #hsz:hash_size_t ->
  lv:uint32_t{lv <= merkle_tree_size_lg} ->
  mtr:HH.rid ->
  hs:hash_vv hsz {V.size_of hs = merkle_tree_size_lg} ->
  rhs:hash_vec #hsz {V.size_of rhs = merkle_tree_size_lg} ->
  i:index_t ->
  j:index_t{j <> 0ul /\ i <= j /\ U32.v j < pow2 (32 - U32.v lv)} ->
  k:index_t{i <= k && k <= j} ->
  p:path_p ->
  actd:bool ->
  HST.ST unit
   (requires (fun h0 ->
     HH.includes mtr (V.frameOf hs) /\
     HH.includes mtr (V.frameOf rhs) /\
     RV.rv_inv h0 hs /\ RV.rv_inv h0 rhs /\
     mt_safe_elts h0 lv hs i j /\
     path_safe h0 mtr p /\
     Path?.hash_size (B.get h0 p 0) = hsz /\
     V.size_of (phashes h0 p) <= lv + 1ul))
   (ensures (fun h0 _ h1 ->
     // memory safety
     modifies (path_loc p) h0 h1 /\
     path_safe h1 mtr p /\
     V.size_of (phashes h1 p) == V.size_of (phashes h0 p) + mt_path_length_step k j actd /\
     V.size_of (phashes h1 p) <= lv + 2ul /\
     // correctness
     (mt_safe_elts_spec h0 lv hs i j;
      (let hsz0 = Path?.hash_size (B.get h0 p 0) in
       let hsz1 = Path?.hash_size (B.get h1 p 0) in
       let before:(S.seq (MTH.hash #(U32.v hsz0))) = lift_path h0 mtr p in       
       let after:(S.seq (MTH.hash #(U32.v hsz1))) = lift_path h1 mtr p in       
       hsz = hsz0 /\ hsz = hsz1 /\
       S.equal after
               (MTH.mt_make_path_step
                 (U32.v lv) (RV.as_seq h0 hs) (RV.as_seq h0 rhs)
                 (U32.v i) (U32.v j) (U32.v k) before actd)))))
#push-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1 --initial_ifuel 2 --max_ifuel 2"
let mt_make_path_step #hsz lv mtr hs rhs i j k p actd =
  let pth = !*p in
  let hh0 = HST.get () in
  let ofs = offset_of i in
  if k % 2ul = 1ul
  then begin
    hash_vv_rv_inv_includes hh0 hs lv (k - 1ul - ofs);
    assert (HH.includes mtr
             (B.frameOf (V.get hh0 (V.get hh0 hs lv) (k - 1ul - ofs))));
    assert(Path?.hash_size pth = hsz);
    mt_path_insert #hsz mtr p (V.index (V.index hs lv) (k - 1ul - ofs))
  end
  else begin
    if k = j then ()
    else if k + 1ul = j
    then (if actd
         then (assert (HH.includes mtr (B.frameOf (V.get hh0 rhs lv)));
              mt_path_insert mtr p (V.index rhs lv)))
    else (hash_vv_rv_inv_includes hh0 hs lv (k + 1ul - ofs);
         assert (HH.includes mtr
                  (B.frameOf (V.get hh0 (V.get hh0 hs lv) (k + 1ul - ofs))));
         mt_path_insert mtr p (V.index (V.index hs lv) (k + 1ul - ofs)))
  end
#pop-options

private inline_for_extraction
val mt_get_path_step_pre_nst:
  #hsz:Ghost.erased hash_size_t ->
  mtr:HH.rid ->
  p:path ->
  i:uint32_t ->
  Tot bool
let mt_get_path_step_pre_nst #hsz mtr p i =
  i < V.size_of (Path?.hashes p)

val mt_get_path_step_pre:
  #hsz:Ghost.erased hash_size_t ->
  mtr:HH.rid ->
  p:const_path_p ->
  i:uint32_t ->
  HST.ST bool
    (requires (fun h0 ->       
                   path_safe h0 mtr (CB.cast p) /\ 
                   (let pv = B.get h0 (CB.cast p) 0 in
                    Path?.hash_size pv = Ghost.reveal hsz /\
                    live h0 (Path?.hashes pv) /\
                    mt_get_path_step_pre_nst #hsz mtr pv i)))
    (ensures (fun _ _ _ -> True))
let mt_get_path_step_pre #hsz mtr p i = 
  let p = CB.cast p in
  mt_get_path_step_pre_nst #hsz mtr !*p i

val mt_get_path_step:
  #hsz:Ghost.erased hash_size_t ->
  mtr:HH.rid ->
  p:const_path_p ->
  i:uint32_t ->
  HST.ST (hash #hsz)
    (requires (fun h0 ->       
                   path_safe h0 mtr (CB.cast p) /\ 
                   (let pv = B.get h0 (CB.cast p) 0 in
                    Path?.hash_size pv = Ghost.reveal hsz /\
                    live h0 (Path?.hashes pv) /\
                    i < V.size_of (Path?.hashes pv))))
    (ensures (fun h0 r h1 -> True ))
let mt_get_path_step #hsz mtr p i = 
  let pd = !*(CB.cast p) in
  V.index #(hash #(Path?.hash_size pd)) (Path?.hashes pd) i

private
val mt_get_path_:
  #hsz:hash_size_t ->
  lv:uint32_t{lv <= merkle_tree_size_lg} ->
  mtr:HH.rid ->
  hs:hash_vv hsz {V.size_of hs = merkle_tree_size_lg} ->
  rhs:hash_vec #hsz {V.size_of rhs = merkle_tree_size_lg} ->
  i:index_t -> j:index_t{i <= j /\ U32.v j < pow2 (32 - U32.v lv)} ->
  k:index_t{i <= k && k <= j} ->
  p:path_p ->
  actd:bool ->
  HST.ST unit
   (requires (fun h0 ->
     HH.includes mtr (V.frameOf hs) /\
     HH.includes mtr (V.frameOf rhs) /\
     RV.rv_inv h0 hs /\ RV.rv_inv h0 rhs /\
     mt_safe_elts h0 lv hs i j /\
     path_safe h0 mtr p /\
     Path?.hash_size (B.get h0 p 0) = hsz /\
     V.size_of (phashes h0 p) <= lv + 1ul))
   (ensures (fun h0 _ h1 ->
     // memory safety
     modifies (path_loc p) h0 h1 /\
     path_safe h1 mtr p /\
     V.size_of (phashes h1 p) ==
     V.size_of (phashes h0 p) + mt_path_length lv k j actd /\
     // correctness
     (mt_safe_elts_spec h0 lv hs i j;
      (let hsz0 = Path?.hash_size (B.get h0 p 0) in
       let hsz1 = Path?.hash_size (B.get h1 p 0) in
       let before:(S.seq (MTH.hash #(U32.v hsz0))) = lift_path h0 mtr p in       
       let after:(S.seq (MTH.hash #(U32.v hsz1))) = lift_path h1 mtr p in       
       hsz = hsz0 /\ hsz = hsz1 /\
       S.equal after
               (MTH.mt_get_path_ (U32.v lv) (RV.as_seq h0 hs) (RV.as_seq h0 rhs)
                 (U32.v i) (U32.v j) (U32.v k) before actd)))))
   (decreases (32 - U32.v lv))
#push-options "--z3rlimit 300 --initial_fuel 1 --max_fuel 1 --max_ifuel 2 --initial_ifuel 2"
let rec mt_get_path_ #hsz lv mtr hs rhs i j k p actd =
  let hh0 = HST.get () in
  mt_safe_elts_spec hh0 lv hs i j;

  let ofs = offset_of i in
  if j = 0ul then ()
  else
    (mt_make_path_step lv mtr hs rhs i j k p actd;

    let hh1 = HST.get () in
    mt_safe_elts_spec hh0 lv hs i j;
    assert (S.equal (lift_path hh1 mtr p)
                    (MTH.mt_make_path_step
                      (U32.v lv) (RV.as_seq hh0 hs) (RV.as_seq hh0 rhs)
                      (U32.v i) (U32.v j) (U32.v k)
                      (lift_path hh0 mtr p) actd));

    RV.rv_inv_preserved hs (path_loc p) hh0 hh1;
    RV.rv_inv_preserved rhs (path_loc p) hh0 hh1;
    RV.as_seq_preserved hs (path_loc p) hh0 hh1;
    RV.as_seq_preserved rhs (path_loc p) hh0 hh1;
    V.loc_vector_within_included hs lv (V.size_of hs);
    mt_safe_elts_preserved lv hs i j (path_loc p) hh0 hh1;
    assert (mt_safe_elts hh1 lv hs i j);
    mt_safe_elts_rec hh1 lv hs i j;
    mt_safe_elts_spec hh1 (lv + 1ul) hs (i / 2ul) (j / 2ul);

    mt_get_path_ (lv + 1ul) mtr hs rhs (i / 2ul) (j / 2ul) (k / 2ul) p
      (if j % 2ul = 0ul then actd else true);

    let hh2 = HST.get () in
    assert (S.equal (lift_path hh2 mtr p)
                    (MTH.mt_get_path_ (U32.v lv + 1)
                      (RV.as_seq hh1 hs) (RV.as_seq hh1 rhs)
                      (U32.v i / 2) (U32.v j / 2) (U32.v k / 2)
                      (lift_path hh1 mtr p)
                      (if U32.v j % 2 = 0 then actd else true)));
    assert (S.equal (lift_path hh2 mtr p)
                    (MTH.mt_get_path_ (U32.v lv)
                      (RV.as_seq hh0 hs) (RV.as_seq hh0 rhs)
                      (U32.v i) (U32.v j) (U32.v k)
                      (lift_path hh0 mtr p) actd)))
#pop-options

private inline_for_extraction
val mt_get_path_pre_nst:
  mtv:merkle_tree ->
  idx:offset_t ->
  p:path ->
  root:(hash #(MT?.hash_size mtv)) ->
  Tot bool
let mt_get_path_pre_nst mtv idx p root =
  offsets_connect (MT?.offset mtv) idx &&
  Path?.hash_size p = MT?.hash_size mtv &&
  ([@inline_let] let idx = split_offset (MT?.offset mtv) idx in
   MT?.i mtv <= idx && idx < MT?.j mtv &&
   V.size_of (Path?.hashes p) = 0ul)

val mt_get_path_pre:
  #hsz:Ghost.erased hash_size_t ->
  mt:const_mt_p ->
  idx:offset_t ->
  p:const_path_p ->
  root:hash #hsz ->
  HST.ST bool
   (requires (fun h0 ->
     let mt = CB.cast mt in
     let p = CB.cast p in
     let dmt = B.get h0 mt 0 in
     let dp = B.get h0 p 0 in
     MT?.hash_size dmt = (Ghost.reveal hsz) /\
     Path?.hash_size dp = (Ghost.reveal hsz) /\
     mt_safe h0 mt /\
     path_safe h0 (B.frameOf mt) p /\    
     Rgl?.r_inv (hreg hsz) h0 root /\
     HH.disjoint (B.frameOf root) (B.frameOf mt) /\
     HH.disjoint (B.frameOf root) (B.frameOf p)))
   (ensures (fun _ _ _ -> True))
let mt_get_path_pre #_ mt idx p root =
  let mt = CB.cast mt in
  let p = CB.cast p in
  let mtv = !*mt in
  mt_get_path_pre_nst mtv idx !*p root

val mt_get_path_loc_union_helper:
  l1:loc -> l2:loc ->
  Lemma (loc_union (loc_union l1 l2) l2 == loc_union l1 l2)
let mt_get_path_loc_union_helper l1 l2 = ()

// Construct a Merkle path for a given index `idx`, hashes `mt.hs`, and rightmost
// hashes `mt.rhs`. Note that this operation copies "pointers" into the Merkle tree
// to the output path.
#push-options "--z3rlimit 60"
val mt_get_path:
  #hsz:Ghost.erased hash_size_t ->
  mt:const_mt_p ->
  idx:offset_t ->
  p:path_p ->
  root:hash #hsz ->
  HST.ST index_t
   (requires (fun h0 ->
     let mt = CB.cast mt in
     let dmt = B.get h0 mt 0 in
     MT?.hash_size dmt = Ghost.reveal hsz /\
     Path?.hash_size (B.get h0 p 0) = Ghost.reveal hsz /\
     mt_get_path_pre_nst (B.get h0 mt 0) idx (B.get h0 p 0) root /\
     mt_safe h0 mt /\
     path_safe h0 (B.frameOf mt) p /\
     Rgl?.r_inv (hreg hsz) h0 root /\
     HH.disjoint (B.frameOf root) (B.frameOf mt) /\
     HH.disjoint (B.frameOf root) (B.frameOf p)))
   (ensures (fun h0 _ h1 ->
     let mt = CB.cast mt in
     let mtv0 = B.get h0 mt 0 in
     let mtv1 = B.get h1 mt 0 in
     let idx = split_offset (MT?.offset mtv0) idx in
     MT?.hash_size mtv0 = Ghost.reveal hsz /\
     MT?.hash_size mtv1 = Ghost.reveal hsz /\
     Path?.hash_size (B.get h0 p 0) = Ghost.reveal hsz /\
     Path?.hash_size (B.get h1 p 0) = Ghost.reveal hsz /\
     // memory safety
     modifies (loc_union
                (loc_union
                  (mt_loc mt)
                  (B.loc_all_regions_from false (B.frameOf root)))
                (path_loc p))
              h0 h1 /\
     mt_safe h1 mt /\
     path_safe h1 (B.frameOf mt) p /\
     Rgl?.r_inv (hreg hsz) h1 root /\
     V.size_of (phashes h1 p) ==
     1ul + mt_path_length 0ul idx (MT?.j mtv0) false /\
     // correctness
     (let sj, sp, srt =
       MTH.mt_get_path
         (mt_lift h0 mt) (U32.v idx) (Rgl?.r_repr (hreg hsz) h0 root) in
     sj == U32.v (MT?.j mtv1) /\
     S.equal sp (lift_path #hsz h1 (B.frameOf mt) p) /\
     srt == Rgl?.r_repr (hreg hsz) h1 root)))
#pop-options
#push-options "--z3rlimit 300 --initial_fuel 1 --max_fuel 1"
let mt_get_path #hsz mt idx p root =
  let ncmt = CB.cast mt in
  let mtframe = B.frameOf ncmt in
  let hh0 = HST.get () in
  mt_get_root mt root;
  let mtv = !*ncmt in
  let hsz = MT?.hash_size mtv in
  
  let hh1 = HST.get () in
  path_safe_init_preserved mtframe p
    (B.loc_union (mt_loc ncmt)
      (B.loc_all_regions_from false (B.frameOf root)))
    hh0 hh1;
  assert (MTH.mt_get_root (mt_lift hh0 ncmt) (Rgl?.r_repr (hreg hsz) hh0 root) ==
         (mt_lift hh1 ncmt, Rgl?.r_repr (hreg hsz) hh1 root));
  assert (S.equal (lift_path #hsz hh1 mtframe p) S.empty);

  let idx = split_offset (MT?.offset mtv) idx in
  let i = MT?.i mtv in
  let ofs = offset_of (MT?.i mtv) in
  let j = MT?.j mtv in
  let hs = MT?.hs mtv in
  let rhs = MT?.rhs mtv in

  assert (mt_safe_elts hh1 0ul hs i j);
  assert (V.size_of (V.get hh1 hs 0ul) == j - ofs);
  assert (idx < j);

  hash_vv_rv_inv_includes hh1 hs 0ul (idx - ofs);
  hash_vv_rv_inv_r_inv hh1 hs 0ul (idx - ofs);
  hash_vv_as_seq_get_index hh1 hs 0ul (idx - ofs);

  let ih = V.index (V.index hs 0ul) (idx - ofs) in
  mt_path_insert #hsz mtframe p ih;

  let hh2 = HST.get () in
  assert (S.equal (lift_path hh2 mtframe p)
                  (MTH.path_insert
                    (lift_path hh1 mtframe p)
                    (S.index (S.index (RV.as_seq hh1 hs) 0) (U32.v idx - U32.v ofs))));
  Rgl?.r_sep (hreg hsz) root (path_loc p) hh1 hh2;
  mt_safe_preserved ncmt (path_loc p) hh1 hh2;
  mt_preserved ncmt (path_loc p) hh1 hh2;
  assert (V.size_of (phashes hh2 p) == 1ul);

  mt_get_path_ 0ul mtframe hs rhs i j idx p false;

  let hh3 = HST.get () in

  // memory safety
  mt_get_path_loc_union_helper
    (loc_union (mt_loc ncmt)
               (B.loc_all_regions_from false (B.frameOf root)))
    (path_loc p);
  Rgl?.r_sep (hreg hsz) root (path_loc p) hh2 hh3;
  mt_safe_preserved ncmt (path_loc p) hh2 hh3;
  mt_preserved ncmt (path_loc p) hh2 hh3;
  assert (V.size_of (phashes hh3 p) ==
         1ul + mt_path_length 0ul idx (MT?.j (B.get hh0 ncmt 0)) false);
  assert (S.length (lift_path #hsz hh3 mtframe p) ==
         S.length (lift_path #hsz hh2 mtframe p) +
         MTH.mt_path_length (U32.v idx) (U32.v (MT?.j (B.get hh0 ncmt 0))) false);

  assert (modifies (loc_union
                     (loc_union
                       (mt_loc ncmt)
                       (B.loc_all_regions_from false (B.frameOf root)))
                     (path_loc p))
                   hh0 hh3);
  assert (mt_safe hh3 ncmt);
  assert (path_safe hh3 mtframe p);
  assert (Rgl?.r_inv (hreg hsz) hh3 root);
  assert (V.size_of (phashes hh3 p) ==
         1ul + mt_path_length 0ul idx (MT?.j (B.get hh0 ncmt 0)) false);

  // correctness
  mt_safe_elts_spec hh2 0ul hs i j;
  assert (S.equal (lift_path hh3 mtframe p)
                  (MTH.mt_get_path_ 0 (RV.as_seq hh2 hs) (RV.as_seq hh2 rhs)
                    (U32.v i) (U32.v j) (U32.v idx)
                    (lift_path hh2 mtframe p) false));
  assert (MTH.mt_get_path
           (mt_lift hh0 ncmt) (U32.v idx) (Rgl?.r_repr (hreg hsz) hh0 root) ==
         (U32.v (MT?.j (B.get hh3 ncmt 0)),
         lift_path hh3 mtframe p,
         Rgl?.r_repr (hreg hsz) hh3 root));
  j
#pop-options

/// Flushing

private val
mt_flush_to_modifies_rec_helper:
  #hsz:hash_size_t ->
  lv:uint32_t{lv < merkle_tree_size_lg} ->
  hs:hash_vv hsz {V.size_of hs = merkle_tree_size_lg} ->
  h:HS.mem ->
  Lemma (loc_union
          (loc_union
            (RV.rs_loc_elem (hvreg hsz) (V.as_seq h hs) (U32.v lv))
            (V.loc_vector_within hs lv (lv + 1ul)))
          (loc_union
            (RV.rv_loc_elems h hs (lv + 1ul) (V.size_of hs))
            (V.loc_vector_within hs (lv + 1ul) (V.size_of hs))) ==
        loc_union
          (RV.rv_loc_elems h hs lv (V.size_of hs))
          (V.loc_vector_within hs lv (V.size_of hs)))
#push-options "--initial_fuel 2 --max_fuel 2"
let mt_flush_to_modifies_rec_helper #hsz lv hs h =
  assert (V.loc_vector_within hs lv (V.size_of hs) ==
         loc_union (V.loc_vector_within hs lv (lv + 1ul))
                   (V.loc_vector_within hs (lv + 1ul) (V.size_of hs)));
  RV.rs_loc_elems_rec_inverse (hvreg hsz) (V.as_seq h hs) (U32.v lv) (U32.v (V.size_of hs));
  assert (RV.rv_loc_elems h hs lv (V.size_of hs) ==
         loc_union (RV.rs_loc_elem (hvreg hsz) (V.as_seq h hs) (U32.v lv))
                   (RV.rv_loc_elems h hs (lv + 1ul) (V.size_of hs)));
  loc_union_assoc_4
    (RV.rs_loc_elem (hvreg hsz) (V.as_seq h hs) (U32.v lv))
    (V.loc_vector_within hs lv (lv + 1ul))
    (RV.rv_loc_elems h hs (lv + 1ul) (V.size_of hs))
    (V.loc_vector_within hs (lv + 1ul) (V.size_of hs))
#pop-options

private
val mt_flush_to_:
  hsz:hash_size_t ->
  lv:uint32_t{lv < merkle_tree_size_lg} ->
  hs:hash_vv hsz {V.size_of hs = merkle_tree_size_lg} ->
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
             (MTH.mt_flush_to_
               (U32.v lv) (RV.as_seq h0 hs) (U32.v pi)
               (U32.v i) (U32.v (Ghost.reveal j))))))
   (decreases (U32.v i))
#restart-solver
#push-options "--z3rlimit 1500 --fuel 1 --ifuel 0"
let rec mt_flush_to_ hsz lv hs pi i j =
  let hh0 = HST.get () in

  // Base conditions
  mt_safe_elts_rec hh0 lv hs pi (Ghost.reveal j);
  V.loc_vector_within_included hs 0ul lv;
  V.loc_vector_within_included hs lv (lv + 1ul);
  V.loc_vector_within_included hs (lv + 1ul) (V.size_of hs);
  V.loc_vector_within_disjoint hs lv (lv + 1ul) (lv + 1ul) (V.size_of hs);

  let oi = offset_of i in
  let opi = offset_of pi in
  if oi = opi then mt_safe_elts_spec hh0 lv hs pi (Ghost.reveal j)
  else begin

    /// 1) Flush hashes at the level `lv`, where the new vector is
    /// not yet connected to `hs`.
    let ofs = oi - opi in
    let hvec = V.index hs lv in
    let flushed:(rvector (hreg hsz)) = rv_flush_inplace hvec ofs in
    let hh1 = HST.get () in

    // 1-0) Basic disjointness conditions for `RV.assign`
    V.forall2_forall_left hh0 hs 0ul (V.size_of hs) lv
      (fun b1 b2 -> HH.disjoint (Rgl?.region_of (hvreg hsz) b1)
                                (Rgl?.region_of (hvreg hsz) b2));
    V.forall2_forall_right hh0 hs 0ul (V.size_of hs) lv
      (fun b1 b2 -> HH.disjoint (Rgl?.region_of (hvreg hsz) b1)
                                (Rgl?.region_of (hvreg hsz) b2));
    V.forall_preserved
      hs 0ul lv
      (fun b -> HH.disjoint (Rgl?.region_of (hvreg hsz) hvec)
                            (Rgl?.region_of (hvreg hsz) b))
      (RV.loc_rvector hvec)
      hh0 hh1;
    V.forall_preserved
      hs (lv + 1ul) (V.size_of hs)
      (fun b -> HH.disjoint (Rgl?.region_of (hvreg hsz) hvec)
                            (Rgl?.region_of (hvreg hsz) b))
      (RV.loc_rvector hvec)
      hh0 hh1;
    assert (Rgl?.region_of (hvreg hsz) hvec == Rgl?.region_of (hvreg hsz) flushed);

    // 1-1) For the `modifies` postcondition.
    assert (modifies (RV.rs_loc_elem (hvreg hsz) (V.as_seq hh0 hs) (U32.v lv)) hh0 hh1);

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
      (hvreg hsz) (V.as_seq hh0 hs) (V.frameOf hs)
      0 (U32.v (V.size_of hs)) 0 (U32.v lv) (U32.v lv);
    RV.rs_loc_elems_parent_disj
      (hvreg hsz) (V.as_seq hh0 hs) (V.frameOf hs)
      0 (U32.v lv);
    RV.rv_elems_inv_preserved
      hs 0ul lv (RV.loc_rvector (V.get hh0 hs lv))
      hh0 hh1;
    assert (RV.rv_elems_inv hh1 hs 0ul lv);
    RV.rs_loc_elems_elem_disj
      (hvreg hsz) (V.as_seq hh0 hs) (V.frameOf hs)
      0 (U32.v (V.size_of hs))
      (U32.v lv + 1) (U32.v (V.size_of hs))
      (U32.v lv);
    RV.rs_loc_elems_parent_disj
      (hvreg hsz) (V.as_seq hh0 hs) (V.frameOf hs)
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
                       (RV.rs_loc_elem (hvreg hsz) (V.as_seq hh0 hs) (U32.v lv))
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
    as_seq_sub_upd hh0 hs lv (RV.as_seq hh1 flushed);

    // if `lv = 31` then `pi <= i <= j < 2` thus `oi = opi`,
    // contradicting the branch.
    assert (lv + 1ul < merkle_tree_size_lg);
    assert (U32.v (Ghost.reveal j / 2ul) < pow2 (32 - U32.v (lv + 1ul)));
    assert (RV.rv_inv hh2 hs);
    assert (mt_safe_elts hh2 (lv + 1ul) hs (pi / 2ul) (Ghost.reveal j / 2ul));

    /// 3) Recursion
    mt_flush_to_ hsz (lv + 1ul) hs (pi / 2ul) (i / 2ul)
      (Ghost.hide (Ghost.reveal j / 2ul));
    let hh3 = HST.get () in

    // 3-0) Memory safety brought from the postcondition of the recursion
    assert (modifies
             (loc_union
               (loc_union
                 (RV.rs_loc_elem (hvreg hsz) (V.as_seq hh0 hs) (U32.v lv))
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
                    (MTH.mt_flush_to_ (U32.v lv + 1) (RV.as_seq hh2 hs)
                      (U32.v pi / 2) (U32.v i / 2) (U32.v (Ghost.reveal j) / 2)));
    mt_safe_elts_spec hh0 lv hs pi (Ghost.reveal j);
    MTH.mt_flush_to_rec
      (U32.v lv) (RV.as_seq hh0 hs)
      (U32.v pi) (U32.v i) (U32.v (Ghost.reveal j));
    assert (S.equal (RV.as_seq hh3 hs)
                    (MTH.mt_flush_to_ (U32.v lv) (RV.as_seq hh0 hs)
                      (U32.v pi) (U32.v i) (U32.v (Ghost.reveal j))))
  end
#pop-options


// `mt_flush_to` flushes old hashes in the Merkle tree. It removes hash elements
// from `MT?.i` to **`offset_of (idx - 1)`**, but maintains the tree structure,
// i.e., the tree still holds some old internal hashes (compressed from old
// hashes) which are required to generate Merkle paths for remaining hashes.
//
// Note that `mt_flush_to` (and `mt_flush`) always remain at least one base hash
// elements. If there are `MT?.j` number of elements in the tree, because of the
// precondition `MT?.i <= idx < MT?.j` we still have `idx`-th element after
// flushing.

private inline_for_extraction
val mt_flush_to_pre_nst: mtv:merkle_tree -> idx:offset_t -> Tot bool
let mt_flush_to_pre_nst mtv idx =
  offsets_connect (MT?.offset mtv) idx &&
  ([@inline_let] let idx = split_offset (MT?.offset mtv) idx in
   idx >= MT?.i mtv &&
   idx < MT?.j mtv)

val mt_flush_to_pre: mt:const_mt_p -> idx:offset_t -> HST.ST bool
  (requires (fun h0 -> mt_safe h0 (CB.cast mt)))
  (ensures (fun _ _ _ -> True))
let mt_flush_to_pre mt idx =
  let mt = CB.cast mt in
  let h0 = HST.get() in
  let mtv = !*mt in
  mt_flush_to_pre_nst mtv idx

#push-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1"
val mt_flush_to:
  mt:mt_p ->
  idx:offset_t ->
  HST.ST unit
   (requires (fun h0 -> mt_safe h0 mt /\ mt_flush_to_pre_nst (B.get h0 mt 0) idx))
   (ensures (fun h0 _ h1 ->
     // memory safety
     modifies (mt_loc mt) h0 h1 /\
     mt_safe h1 mt /\
     // correctness
     (let mtv0 = B.get h0 mt 0 in
      let mtv1 = B.get h1 mt 0 in
      let off = MT?.offset mtv0 in
      let idx = split_offset off idx in
      MT?.hash_size mtv0 = MT?.hash_size mtv1 /\
      MTH.mt_flush_to (mt_lift h0 mt) (U32.v idx) == mt_lift h1 mt)))
let mt_flush_to mt idx =
  let hh0 = HST.get () in
  let mtv = !*mt in
  let offset = MT?.offset mtv in
  let j = MT?.j mtv in
  let hsz = MT?.hash_size mtv in
  let idx = split_offset offset idx in
  let hs = MT?.hs mtv in
  mt_flush_to_ hsz 0ul hs (MT?.i mtv) idx (Ghost.hide (MT?.j mtv));
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
  Rgl?.r_sep (hreg (MT?.hash_size mtv)) (MT?.mroot mtv)
    (loc_union
      (RV.rv_loc_elems hh0 hs 0ul (V.size_of hs))
      (V.loc_vector_within hs 0ul (V.size_of hs)))
    hh0 hh1;
  mt *= MT (MT?.hash_size mtv)
           (MT?.offset mtv) idx (MT?.j mtv)
           hs
           (MT?.rhs_ok mtv) (MT?.rhs mtv)
           (MT?.mroot mtv)
           (MT?.hash_spec mtv) (MT?.hash_fun mtv);
  let hh2 = HST.get () in
  RV.rv_inv_preserved (MT?.hs mtv) (B.loc_buffer mt) hh1 hh2;
  RV.rv_inv_preserved (MT?.rhs mtv) (B.loc_buffer mt) hh1 hh2;
  RV.as_seq_preserved (MT?.hs mtv) (B.loc_buffer mt) hh1 hh2;
  RV.as_seq_preserved (MT?.rhs mtv) (B.loc_buffer mt) hh1 hh2;
  Rgl?.r_sep (hreg (MT?.hash_size mtv)) (MT?.mroot mtv) (B.loc_buffer mt) hh1 hh2;
  mt_safe_elts_preserved 0ul hs idx (MT?.j mtv) (B.loc_buffer mt) hh1 hh2
#pop-options

private inline_for_extraction
val mt_flush_pre_nst: mt:merkle_tree -> Tot bool
let mt_flush_pre_nst mt = MT?.j mt > MT?.i mt

val mt_flush_pre: mt:const_mt_p -> HST.ST bool (requires (fun h0 -> mt_safe h0 (CB.cast mt))) (ensures (fun _ _ _ -> True))
let mt_flush_pre mt = mt_flush_pre_nst !*(CB.cast mt)

val mt_flush:
  mt:mt_p ->
  HST.ST unit
   (requires (fun h0 -> mt_safe h0 mt /\ mt_flush_pre_nst (B.get h0 mt 0)))
   (ensures (fun h0 _ h1 ->
     let mtv0 = B.get h0 mt 0 in
     let mtv1 = B.get h1 mt 0 in
     // memory safety
     modifies (mt_loc mt) h0 h1 /\
     mt_safe h1 mt /\
     // correctness
     MT?.hash_size mtv0 = MT?.hash_size mtv1 /\
     MTH.mt_flush (mt_lift h0 mt) == mt_lift h1 mt))
#push-options "--z3rlimit 200 --initial_fuel 1 --max_fuel 1"
let mt_flush mt =
  let mtv = !*mt in
  let off = MT?.offset mtv in
  let j = MT?.j mtv in
  let j1 = j - 1ul in
  assert (j1 < uint32_32_max);
  assert (off < uint64_max);
  assert (UInt.fits (U64.v off + U32.v j1) 64);
  let jo = join_offset off j1 in
  mt_flush_to mt jo
#pop-options


/// Retraction

private
val mt_retract_to_:
  #hsz:hash_size_t ->
  hs:hash_vv hsz {V.size_of hs = merkle_tree_size_lg} ->
  lv:uint32_t{lv < V.size_of hs} ->
  i:index_t ->
  s:index_t ->
  j:index_t{i <= s && s <= j && v j < pow2 (U32.v (V.size_of hs) - v lv)}
  -> HST.ST unit
   (requires (fun h0 ->
     RV.rv_inv h0 hs /\
     mt_safe_elts h0 lv hs i j))
   (ensures (fun h0 _ h1 ->
     // memory safety
     (modifies (loc_union
                 (RV.rv_loc_elems h0 hs lv (V.size_of hs))
                 (V.loc_vector_within hs lv (V.size_of hs)))
              h0 h1) /\
     RV.rv_inv h1 hs /\
     mt_safe_elts h1 lv hs i s /\
     // correctness
     (mt_safe_elts_spec h0 lv hs i j;
     S.equal (RV.as_seq h1 hs)
             (MTH.mt_retract_to_
               (RV.as_seq h0 hs) (U32.v lv)
               (U32.v i) (U32.v s) (U32.v j)))
     ))
   (decreases (U32.v merkle_tree_size_lg - U32.v lv))
#push-options "--z3rlimit 300 --initial_fuel 1 --max_fuel 1"
private
let rec mt_retract_to_ #hsz hs lv i s j =
  let hh0 = HST.get () in

  // Base conditions
  mt_safe_elts_rec hh0 lv hs i j;
  V.loc_vector_within_included hs 0ul lv;
  V.loc_vector_within_included hs lv (lv + 1ul);
  V.loc_vector_within_included hs (lv + 1ul) (V.size_of hs);
  V.loc_vector_within_disjoint hs lv (lv + 1ul) (lv + 1ul) (V.size_of hs);

  if lv >= V.size_of hs then ()
  else begin

    // 1) Retract hashes at level `lv`.
    let hvec = V.index hs lv in
    let old_len = j - offset_of i in
    let new_len = s - offset_of i in
    let retracted = RV.shrink hvec new_len in

    let hh1 = HST.get () in

    // 1-0) Basic disjointness conditions for `RV.assign`
    V.forall2_forall_left hh0 hs 0ul (V.size_of hs) lv
      (fun b1 b2 -> HH.disjoint (Rgl?.region_of (hvreg hsz) b1)
                                (Rgl?.region_of (hvreg hsz) b2));
    V.forall2_forall_right hh0 hs 0ul (V.size_of hs) lv
      (fun b1 b2 -> HH.disjoint (Rgl?.region_of (hvreg hsz) b1)
                                (Rgl?.region_of (hvreg hsz) b2));
    V.forall_preserved
      hs 0ul lv
      (fun b -> HH.disjoint (Rgl?.region_of (hvreg hsz) hvec)
                            (Rgl?.region_of (hvreg hsz) b))
      (RV.loc_rvector hvec)
      hh0 hh1;
    V.forall_preserved
      hs (lv + 1ul) (V.size_of hs)
      (fun b -> HH.disjoint (Rgl?.region_of (hvreg hsz) hvec)
                            (Rgl?.region_of (hvreg hsz) b))
      (RV.loc_rvector hvec)
      hh0 hh1;
    assert (Rgl?.region_of (hvreg hsz) hvec == Rgl?.region_of (hvreg hsz) retracted);

    // 1-1) For the `modifies` postcondition.
    assert (modifies (RV.rs_loc_elem (hvreg hsz) (V.as_seq hh0 hs) (U32.v lv)) hh0 hh1);

    // 1-2) Preservation
    RV.rv_loc_elems_preserved
      hs (lv + 1ul) (V.size_of hs)
      (RV.loc_rvector (V.get hh0 hs lv)) hh0 hh1;

    // 1-3) For `mt_safe_elts`
    assert (V.size_of retracted == new_len);
    mt_safe_elts_preserved
      (lv + 1ul) hs (i / 2ul) (j / 2ul)
      (RV.loc_rvector (V.get hh0 hs lv)) hh0 hh1;

    // 1-4) For the `rv_inv` postcondition
    RV.rs_loc_elems_elem_disj
      (hvreg hsz) (V.as_seq hh0 hs) (V.frameOf hs)
      0 (U32.v (V.size_of hs)) 0 (U32.v lv) (U32.v lv);
    RV.rs_loc_elems_parent_disj
      (hvreg hsz) (V.as_seq hh0 hs) (V.frameOf hs)
      0 (U32.v lv);
    RV.rv_elems_inv_preserved
      hs 0ul lv (RV.loc_rvector (V.get hh0 hs lv))
      hh0 hh1;
    assert (RV.rv_elems_inv hh1 hs 0ul lv);
    RV.rs_loc_elems_elem_disj
      (hvreg hsz) (V.as_seq hh0 hs) (V.frameOf hs)
      0 (U32.v (V.size_of hs))
      (U32.v lv + 1) (U32.v (V.size_of hs))
      (U32.v lv);
    RV.rs_loc_elems_parent_disj
      (hvreg hsz) (V.as_seq hh0 hs) (V.frameOf hs)
      (U32.v lv + 1) (U32.v (V.size_of hs));
    RV.rv_elems_inv_preserved
      hs (lv + 1ul) (V.size_of hs) (RV.loc_rvector (V.get hh0 hs lv))
      hh0 hh1;
    assert (RV.rv_elems_inv hh1 hs (lv + 1ul) (V.size_of hs));

    assert (rv_itself_inv hh1 hs);
    assert (elems_reg hh1 hs);

    // 1-5) Correctness
    assert (S.equal (RV.as_seq hh1 retracted)
                    (S.slice (RV.as_seq hh0 (V.get hh0 hs lv)) 0 (U32.v new_len)));

    RV.assign hs lv retracted;

    let hh2 = HST.get() in

    // 2-1) For the `modifies` postcondition.
    assert (modifies (V.loc_vector_within hs lv (lv + 1ul)) hh1 hh2);
    assert (modifies (loc_union
                       (RV.rs_loc_elem (hvreg hsz) (V.as_seq hh0 hs) (U32.v lv))
                       (V.loc_vector_within hs lv (lv + 1ul))) hh0 hh2);

    // 2-2) Preservation
    V.loc_vector_within_disjoint hs lv (lv + 1ul) (lv + 1ul) (V.size_of hs);
    RV.rv_loc_elems_preserved
      hs (lv + 1ul) (V.size_of hs)
      (V.loc_vector_within hs lv (lv + 1ul)) hh1 hh2;

    // 2-3) For `mt_safe_elts`
    assert (V.size_of (V.get hh2 hs lv) == s - offset_of i);
    mt_safe_elts_preserved
      (lv + 1ul) hs (i / 2ul) (j / 2ul)
      (V.loc_vector_within hs lv (lv + 1ul)) hh1 hh2;

    // 2-4) Correctness
    RV.as_seq_sub_preserved hs 0ul lv (loc_rvector retracted) hh0 hh1;
    RV.as_seq_sub_preserved hs (lv + 1ul) merkle_tree_size_lg (loc_rvector retracted) hh0 hh1;
    assert (S.equal (RV.as_seq hh2 hs)
                    (S.append
                      (RV.as_seq_sub hh0 hs 0ul lv)
                      (S.cons (RV.as_seq hh1 retracted)
                              (RV.as_seq_sub hh0 hs (lv + 1ul) merkle_tree_size_lg))));
    as_seq_sub_upd hh0 hs lv (RV.as_seq hh1 retracted);

    if lv + 1ul < V.size_of hs then
    begin
      assert (mt_safe_elts hh2 (lv + 1ul) hs (i / 2ul) (j / 2ul));
      mt_safe_elts_spec hh2 (lv + 1ul) hs (i / 2ul) (j / 2ul);

      mt_retract_to_ hs (lv + 1ul) (i / 2ul) (s / 2ul) (j / 2ul);

      // 3-0) Memory safety brought from the postcondition of the recursion
      let hh3 = HST.get () in
      assert (modifies
             (loc_union
               (loc_union
                 (RV.rs_loc_elem (hvreg hsz) (V.as_seq hh0 hs) (U32.v lv))
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
      assert (V.size_of (V.get hh3 hs lv) == s - offset_of i);
      assert (RV.rv_inv hh3 hs);
      mt_safe_elts_constr hh3 lv hs i s;
      assert (mt_safe_elts hh3 lv hs i s);

      // 3-1) Correctness
      mt_safe_elts_spec hh2 (lv + 1ul) hs (i / 2ul) (j / 2ul);
      assert (U32.v lv + 1 < S.length (RV.as_seq hh3 hs) ==>
                    S.equal (RV.as_seq hh3 hs)
                      (MTH.mt_retract_to_ (RV.as_seq hh2 hs) (U32.v lv + 1)
                        (U32.v i / 2) (U32.v s / 2) (U32.v j / 2)));
      assert (RV.rv_inv hh0 hs);
      assert (mt_safe_elts hh0 lv hs i j);
      mt_safe_elts_spec hh0 lv hs i j;
      assert (S.equal (RV.as_seq hh3 hs)
                      (MTH.mt_retract_to_ (RV.as_seq hh0 hs) (U32.v lv)
                        (U32.v i) (U32.v s) (U32.v j)))
    end
    else begin
      let hh3 = HST.get() in
      assert ((modifies (loc_union
                 (RV.rv_loc_elems hh0 hs lv (V.size_of hs))
                 (V.loc_vector_within hs lv (V.size_of hs)))
              hh0 hh3));
      assert (RV.rv_inv hh3 hs /\ mt_safe_elts hh3 lv hs i s);
      mt_safe_elts_spec hh0 lv hs i j;
      assert (S.equal (RV.as_seq hh3 hs)
                      (MTH.mt_retract_to_
                      (RV.as_seq hh0 hs) (U32.v lv)
                      (U32.v i) (U32.v s) (U32.v j)))
    end
  end
#pop-options

private inline_for_extraction
val mt_retract_to_pre_nst: mtv:merkle_tree -> r:offset_t -> Tot bool
let mt_retract_to_pre_nst mtv r =
  offsets_connect (MT?.offset mtv) r &&
  ([@inline_let] let r = split_offset (MT?.offset mtv) r in
   MT?.i mtv <= r && r < MT?.j mtv)

val mt_retract_to_pre: mt:const_mt_p -> r:offset_t -> HST.ST bool
  (requires (fun h0 -> mt_safe h0 (CB.cast mt)))
  (ensures (fun _ _ _ -> True))
let mt_retract_to_pre mt r =
  let mt = CB.cast mt in
  let h0 = HST.get() in
  let mtv = !*mt in
  mt_retract_to_pre_nst mtv r
#push-options "--z3rlimit 100"
val mt_retract_to:
  mt:mt_p ->
  r:offset_t ->
  HST.ST unit
   (requires (fun h0 -> mt_safe h0 mt /\ mt_retract_to_pre_nst (B.get h0 mt 0) r))
   (ensures (fun h0 _ h1 ->
     // memory safety
     modifies (mt_loc mt) h0 h1 /\
     mt_safe h1 mt /\
     // correctness
     (let mtv0 = B.get h0 mt 0 in
      let mtv1 = B.get h1 mt 0 in
      let off = MT?.offset mtv0 in
      let r = split_offset off r in
      MT?.hash_size mtv0 = MT?.hash_size mtv1 /\
      MTH.mt_retract_to (mt_lift h0 mt) (U32.v r) == mt_lift h1 mt)))
let mt_retract_to mt r =
  let hh0 = HST.get () in
  let mtv = !*mt in
  let offset = MT?.offset mtv in
  let r = split_offset offset r in
  let hs = MT?.hs mtv in
  mt_retract_to_ hs 0ul (MT?.i mtv) (r + 1ul) (MT?.j mtv);
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
  Rgl?.r_sep (hreg (MT?.hash_size mtv)) (MT?.mroot mtv)
    (loc_union
      (RV.rv_loc_elems hh0 hs 0ul (V.size_of hs))
      (V.loc_vector_within hs 0ul (V.size_of hs)))
    hh0 hh1;
  mt *= MT (MT?.hash_size mtv) (MT?.offset mtv) (MT?.i mtv) (r+1ul) hs false (MT?.rhs mtv) (MT?.mroot mtv) (MT?.hash_spec mtv) (MT?.hash_fun mtv);
  let hh2 = HST.get () in
  RV.rv_inv_preserved (MT?.hs mtv) (B.loc_buffer mt) hh1 hh2;
  RV.rv_inv_preserved (MT?.rhs mtv) (B.loc_buffer mt) hh1 hh2;
  RV.as_seq_preserved (MT?.hs mtv) (B.loc_buffer mt) hh1 hh2;
  RV.as_seq_preserved (MT?.rhs mtv) (B.loc_buffer mt) hh1 hh2;
  Rgl?.r_sep (hreg (MT?.hash_size mtv)) (MT?.mroot mtv) (B.loc_buffer mt) hh1 hh2;
  mt_safe_elts_preserved 0ul hs (MT?.i mtv) (r+1ul) (B.loc_buffer mt) hh1 hh2
#pop-options


/// Client-side verification

private
val mt_verify_:
  #hsz:hash_size_t ->
  #hash_spec:MTS.hash_fun_t #(U32.v hsz) ->
  k:index_t ->
  j:index_t{k <= j} ->
  mtr:HH.rid ->
  p:const_path_p ->
  ppos:uint32_t ->
  acc:hash #hsz ->
  actd:bool ->
  hash_fun:hash_fun_t #hsz #hash_spec ->
  HST.ST unit
   (requires (fun h0 ->
     let p = CB.cast p in
     path_safe h0 mtr p /\ Rgl?.r_inv (hreg hsz) h0 acc /\
     Path?.hash_size (B.get h0 p 0) = hsz /\
     HH.disjoint (B.frameOf p) (B.frameOf acc) /\
     HH.disjoint mtr (B.frameOf acc) /\
     // Below is a very relaxed condition,
     // but sufficient to ensure (+) for uint32_t is sound.
     ppos <= 64ul - mt_path_length 0ul k j actd /\
     ppos + mt_path_length 0ul k j actd <= V.size_of (phashes h0 p)))
   (ensures (fun h0 _ h1 ->
     let p = CB.cast p in     
     // memory safety
     modifies (B.loc_all_regions_from false (B.frameOf acc)) h0 h1 /\
     Rgl?.r_inv (hreg hsz) h1 acc /\
     // correctness
     Rgl?.r_repr (hreg hsz) h1 acc ==
     MTH.mt_verify_ #(U32.v hsz) #hash_spec (U32.v k) (U32.v j) (lift_path h0 mtr p)
       (U32.v ppos) (Rgl?.r_repr (hreg hsz) h0 acc) actd))
#push-options "--z3rlimit 200 --initial_fuel 1 --max_fuel 1"
let rec mt_verify_ #hsz #hash_spec k j mtr p ppos acc actd hash_fun =
  let ncp:path_p = CB.cast p in
  let hh0 = HST.get () in
  if j = 0ul then ()
  else (let nactd = actd || (j % 2ul = 1ul) in
       if k % 2ul = 0ul then begin
         if j = k || (j = k + 1ul && not actd) then
           mt_verify_ (k / 2ul) (j / 2ul) mtr p ppos acc nactd hash_fun
         else begin
           let ncpd = !*ncp in
           let phash = V.index (Path?.hashes ncpd) ppos in
           hash_fun acc phash acc;
           let hh1 = HST.get () in
           path_preserved mtr ncp
             (B.loc_all_regions_from false (B.frameOf acc)) hh0 hh1;
           lift_path_index hh0 mtr ncp ppos;
           assert (Rgl?.r_repr (hreg hsz) hh1 acc ==
                  hash_spec (Rgl?.r_repr (hreg hsz) hh0 acc)
                            (S.index (lift_path #hsz hh0 mtr ncp) (U32.v ppos)));
           mt_verify_ (k / 2ul) (j / 2ul) mtr p (ppos + 1ul) acc nactd hash_fun
         end
       end
       else begin
         let ncpd = !*ncp in
         let phash = V.index (Path?.hashes ncpd) ppos in
         hash_fun phash acc acc;
         let hh1 = HST.get () in
         path_preserved mtr ncp
           (B.loc_all_regions_from false (B.frameOf acc)) hh0 hh1;
         lift_path_index hh0 mtr ncp ppos;
         assert (Rgl?.r_repr (hreg hsz) hh1 acc ==
                hash_spec (S.index (lift_path #hsz hh0 mtr ncp) (U32.v ppos))
                          (Rgl?.r_repr (hreg hsz) hh0 acc));
         mt_verify_ (k / 2ul) (j / 2ul) mtr p (ppos + 1ul) acc nactd hash_fun
       end)
#pop-options

private inline_for_extraction
val mt_verify_pre_nst: mt:merkle_tree -> k:offset_t -> j:offset_t -> p:path -> rt:(hash #(MT?.hash_size mt)) -> Tot bool
let mt_verify_pre_nst mt k j p rt =
  k < j &&
  offsets_connect (MT?.offset mt) k &&
  offsets_connect (MT?.offset mt) j &&
  MT?.hash_size mt = Path?.hash_size p &&
  ([@inline_let] let k = split_offset (MT?.offset mt) k in
   [@inline_let] let j = split_offset (MT?.offset mt) j in
   // We need to add one since the first element is the hash to verify.
   V.size_of (Path?.hashes p) = 1ul + mt_path_length 0ul k j false)

val mt_verify_pre:
  #hsz:Ghost.erased hash_size_t ->
  mt:const_mt_p ->
  k:uint64_t ->
  j:uint64_t ->
  mtr:HH.rid ->
  p:const_path_p ->
  rt:hash #hsz ->
  HST.ST bool
    (requires (fun h0 ->
      let mt = CB.cast mt in
      let p = CB.cast p in
      let mtv0 = B.get h0 mt 0 in
      MT?.hash_size mtv0 = Ghost.reveal hsz /\
      mt_safe h0 mt /\
      path_safe h0 mtr p /\ Rgl?.r_inv (hreg hsz) h0 rt /\
      HST.is_eternal_region (B.frameOf rt) /\
      HH.disjoint (B.frameOf p) (B.frameOf rt) /\
      HH.disjoint mtr (B.frameOf rt)))
    (ensures (fun _ _ _ -> True))
let mt_verify_pre #hsz mt k j mtr p rt =
  let mt = CB.cast mt in
  let p = CB.cast p in
  let mtv = !*mt in
  mt_verify_pre_nst mtv k j !*p rt

// `mt_verify` verifies a Merkle path `p` with given target index `k` and
// the number of elements `j`. It recursively iterates the path with an
// accumulator `acc` (a compressed hash).
//
// Note that `mt_path_length` is given as a precondition of this operation.
// This is a postcondition of `mt_get_path` so we can call `mt_verify` with
// every path generated by `mt_get_path`.
#push-options "--z3rlimit 20"
val mt_verify:
  #hsz:Ghost.erased hash_size_t ->
  #hash_spec:MTS.hash_fun_t #(U32.v hsz) ->
  mt:const_mt_p ->
  k:uint64_t ->
  j:uint64_t ->
  mtr:HH.rid ->
  p:const_path_p ->
  rt:hash #hsz ->
  HST.ST bool
   (requires (fun h0 ->
     let mt = CB.cast mt in
     let p = CB.cast p in
     let mtv0 = B.get h0 mt 0 in
     MT?.hash_size mtv0 = Ghost.reveal hsz /\
     Path?.hash_size (B.get h0 p 0) = Ghost.reveal hsz /\
     Ghost.reveal (MT?.hash_spec mtv0) == hash_spec /\
     mt_safe h0 mt /\
     path_safe h0 mtr p /\ Rgl?.r_inv (hreg hsz) h0 rt /\
     HST.is_eternal_region (B.frameOf rt) /\
     HH.disjoint (B.frameOf p) (B.frameOf rt) /\
     HH.disjoint mtr (B.frameOf rt) /\
     mt_verify_pre_nst (B.get h0 mt 0) k j (B.get h0 p 0) rt))
   (ensures (fun h0 b h1 ->
     let mt = CB.cast mt in
     let p = CB.cast p in
     let mtv0 = B.get h0 mt 0 in
     let mtv1 = B.get h1 mt 0 in
     MT?.hash_size mtv0 = Ghost.reveal hsz /\
     MT?.hash_size mtv1 = Ghost.reveal hsz /\     
     // memory safety:
     // `rt` is not modified in this function, but we use a trick
     // to allocate an auxiliary buffer in the extended region of `rt`.
     modifies (B.loc_all_regions_from false (B.frameOf rt)) h0 h1 /\
     Rgl?.r_inv (hreg hsz) h1 rt /\
     // correctness
     S.equal (Rgl?.r_repr (hreg hsz) h0 rt) (Rgl?.r_repr (hreg hsz) h1 rt) /\
     (let mtv = B.get h0 mt 0 in
      let k = split_offset (MT?.offset mtv) k in
      let j = split_offset (MT?.offset mtv) j in
      b <==> MTH.mt_verify #(U32.v hsz) #hash_spec (U32.v k) (U32.v j)
             (lift_path h0 mtr p) (Rgl?.r_repr (hreg hsz) h0 rt))))
#pop-options
#push-options "--z3rlimit 200 --initial_fuel 2 --max_fuel 2 --initial_ifuel 1 --max_ifuel 1"
let mt_verify #_ #hash_spec mt k j mtr p rt =
  let ncmt = CB.cast mt in
  let ncp = CB.cast p in
  let mtv = !*ncmt in
  let hash_size = MT?.hash_size mtv in
  let hrg = hreg hash_size in
  let k = split_offset (MT?.offset mtv) k in
  let j = split_offset (MT?.offset mtv) j in
  let hh0 = HST.get () in
  let nrid = HST.new_region (B.frameOf rt) in
  let ih = rg_alloc hrg nrid in
  let pth = !*ncp in
  assert (MT?.hash_size mtv = hash_size);
  assert (Path?.hash_size pth = hash_size);
  let first = V.index (Path?.hashes pth) 0ul in
  Cpy?.copy (hcpy hash_size) hash_size first ih;
  let hh1 = HST.get () in
  path_safe_preserved
    mtr ncp (B.loc_all_regions_from false (B.frameOf rt)) hh0 hh1;
  path_preserved mtr ncp (B.loc_all_regions_from false (B.frameOf rt)) hh0 hh1;
  lift_path_index hh0 mtr ncp 0ul;
  assert (Rgl?.r_repr hrg hh1 ih == S.index (lift_path #hash_size hh0 mtr ncp) 0);
  mt_verify_ #hash_size #hash_spec k j mtr p 1ul ih false (MT?.hash_fun mtv);
  let hh2 = HST.get () in
  assert (Rgl?.r_repr hrg hh2 ih ==
         MTH.mt_verify_ #(U32.v hash_size) #hash_spec (U32.v k) (U32.v j) (lift_path hh1 mtr ncp)
           1 (Rgl?.r_repr hrg hh1 ih) false);
  let r = Lib.ByteBuffer.lbytes_eq #hash_size ih rt in
  rg_free hrg ih;
  r
#pop-options
