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
open Low.RVector

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MHS = FStar.Monotonic.HyperStack
module HH = FStar.Monotonic.HyperHeap

module B = LowStar.Buffer
module V = Low.Vector
module RV = Low.RVector
module S = FStar.Seq

module U32 = FStar.UInt32
module U8 = FStar.UInt8

module EHS = EverCrypt.Hash
module EHL = EverCrypt.Helpers

val hash_size: uint32_t
let hash_size = EHS.tagLen EHS.SHA256

type hash = uint8_p

val hash_cfg: EverCrypt.AutoConfig.impl -> HST.St unit
let hash_cfg i = 
  EverCrypt.AutoConfig.init (EverCrypt.AutoConfig.Prefer i)

// We cannot use `LowStar.RVector.Instances`, where we have some general
// instantiations of `regional`, e.g., if `rg:regional a` then
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

private val hash_cv: unit -> Tot hash
private let hash_cv _ = B.null

private val hash_repr: Type0
private let hash_repr = S.seq uint8_t

val hash_r_repr:
  h:HS.mem -> v:hash -> GTot hash_repr
let hash_r_repr h v = B.as_seq h v

val hash_r_inv: h:HS.mem -> v:hash -> GTot Type0
let hash_r_inv h v =
  B.live h v /\ B.freeable v /\ 
  B.len v = hash_size

val hash_r_inv_reg:
  h:HS.mem -> v:hash ->
  Lemma (requires (hash_r_inv h v))
	(ensures (MHS.live_region h (hash_region_of v)))
let hash_r_inv_reg h v = ()

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

private val hash_r_init:
  r:erid ->
  HST.ST hash
    (requires (fun h0 -> true))
    (ensures (fun h0 v h1 -> 
      Set.subset (Map.domain (MHS.get_hmap h0))
                 (Map.domain (MHS.get_hmap h1)) /\
      modifies loc_none h0 h1 /\
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

// `hash_cv ()` is is also a trick to extract the C code using KreMLin.
// If we just define and use `hash_cv` as a constant, then gcc complains with
// the error "initializer element is not a compile-time constant".
private val hreg: regional hash
private let hreg =
  Rgl hash_region_of
      (hash_cv ())
      hash_repr
      hash_r_repr
      hash_r_inv
      hash_r_inv_reg
      hash_r_sep
      hash_irepr
      hash_r_init
      hash_r_free

private val hcpy: copyable hash hreg
private let hcpy = Cpy hash_copy

type hash_vec = RV.rvector hreg

/// 2. `rvector hash` is regional

val hash_vec_region_of: 
  v:hash_vec -> GTot HH.rid
let hash_vec_region_of v = V.frameOf v

private val hash_vec_cv: hash_vec
private let hash_vec_cv = V.create_empty hash

private val hash_vec_repr: Type0
private let hash_vec_repr = S.seq (S.seq uint8_t)

val hash_vec_r_repr:
  h:HS.mem -> v:hash_vec -> GTot hash_vec_repr
let hash_vec_r_repr h v =
  RV.as_seq h v

val hash_vec_r_inv:
  h:HS.mem -> v:hash_vec -> GTot Type0
let hash_vec_r_inv h v = rv_inv h v

val hash_vec_r_inv_reg:
  h:HS.mem -> v:hash_vec ->
  Lemma (requires (hash_vec_r_inv h v))
	(ensures (MHS.live_region h (hash_vec_region_of v)))
let hash_vec_r_inv_reg h v = ()

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

private val hash_vec_r_init: 
  r:erid ->
  HST.ST (v:hash_vec)
    (requires (fun h0 -> true))
    (ensures (fun h0 v h1 -> 
      Set.subset (Map.domain (MHS.get_hmap h0))
                 (Map.domain (MHS.get_hmap h1)) /\
      modifies loc_none h0 h1 /\
      hash_vec_r_inv h1 v /\
      hash_vec_region_of v = r /\
      hash_vec_r_repr h1 v == Ghost.reveal hash_vec_irepr))
private let hash_vec_r_init r =
  let nrid = RV.new_region_ r in
  let r_init = Rgl?.r_init hreg in
  let ia = r_init nrid in
  V.create_reserve 1ul ia r

val hash_vec_r_free:
  v:hash_vec ->
  HST.ST unit
    (requires (fun h0 -> hash_vec_r_inv h0 v))
    (ensures (fun h0 _ h1 ->
      modifies (loc_all_regions_from false (hash_vec_region_of v)) h0 h1))
let hash_vec_r_free v =
  RV.free v

private val bhreg: regional hash_vec
private let bhreg =
  Rgl hash_vec_region_of
      hash_vec_cv
      hash_vec_repr
      hash_vec_r_repr
      hash_vec_r_inv
      hash_vec_r_inv_reg
      hash_vec_r_sep
      hash_vec_irepr
      hash_vec_r_init
      hash_vec_r_free

type hash_vv = RV.rvector bhreg

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
	   modifies (B.loc_region_only false (B.frameOf dst)) h0 h1 /\
	   Rgl?.r_inv hreg h1 dst))
let hash_2 src1 src2 dst =
  admit ();
  HST.push_frame ();
  // let cb = B.malloc HH.root 0uy (EHS.blockLen EHS.SHA256) in
  // EHS.blockLen EHS.SHA256 = 64ul
  let cb = B.alloca 0uy 64ul in
  B.blit src1 0ul cb 0ul hash_size;
  B.blit src2 0ul cb 32ul hash_size;
  let st = EHS.create EHS.SHA256 in
  EHS.init st;
  EHS.update (Ghost.hide S.empty) st cb;
  EHS.finish st dst;
  EHS.free st;
  HST.pop_frame ()

/// Low-level Merkle tree data structure

// A Merkle tree `MT i j hs rhs_ok rhs` stores all necessary hashes to generate
// a Merkle path for each element from the index `i` to `j-1`.
// - Parameters
// `hs`: a 2-dim store for hashes, where `hs[0]` contains leaf hash values.
// `rhs_ok`: to check the rightmost hashes are up-to-date
// `rhs`: a store for "rightmost" hashes, manipulated only when required to
//        calculate some merkle parhs that need the rightmost hashes
//        as a part of them.
noeq type merkle_tree = 
| MT: i:uint32_t -> j:uint32_t{j >= i} ->
      hs:hash_vv{V.size_of hs = 32ul} ->
      rhs_ok:bool ->
      rhs:hash_vec{V.size_of rhs = 32ul} ->
      merkle_tree

type mt_p = B.pointer merkle_tree

val mt_not_full: HS.mem -> mt_p -> GTot bool
let mt_not_full h mt =
  MT?.j (B.get h mt 0) < U32.uint_to_t (UInt.max_int U32.n)

/// (Memory) Safety

val offset_of: i:uint32_t -> Tot uint32_t
let offset_of i =
  if i % 2ul = 0ul then i else i - 1ul

val mt_safe_elts: 
  h:HS.mem -> lv:uint32_t{lv <= 32ul} ->
  hs:hash_vv{V.size_of hs = 32ul} -> 
  i:uint32_t -> j:uint32_t{j >= i} ->
  GTot Type0 (decreases (32 - U32.v lv))
let rec mt_safe_elts h lv hs i j =
  if lv = 32ul then true
  else (let ofs = offset_of i in
       V.size_of (V.get h hs lv) == j - ofs /\
       mt_safe_elts h (lv + 1ul) hs (i / 2ul) (j / 2ul))

val mt_safe_elts_head:
  h:HS.mem -> lv:uint32_t{lv < 32ul} ->
  hs:hash_vv{V.size_of hs = 32ul} -> 
  i:uint32_t -> j:uint32_t{j >= i} ->
  Lemma (requires (mt_safe_elts h lv hs i j))
	(ensures (V.size_of (V.get h hs lv) == j - offset_of i))
let mt_safe_elts_head h lv hs i j = ()

val mt_safe_elts_rec:
  h:HS.mem -> lv:uint32_t{lv < 32ul} ->
  hs:hash_vv{V.size_of hs = 32ul} -> 
  i:uint32_t -> j:uint32_t{j >= i} ->
  Lemma (requires (mt_safe_elts h lv hs i j))
	(ensures (mt_safe_elts h (lv + 1ul) hs (i / 2ul) (j / 2ul)))
let mt_safe_elts_rec h lv hs i j = ()

val mt_safe_elts_init:
  h:HS.mem -> lv:uint32_t{lv <= 32ul} ->
  hs:hash_vv{V.size_of hs = 32ul} -> 
  Lemma (requires (V.forall_ h hs lv (V.size_of hs)
		    (fun hv -> V.size_of hv = 0ul)))
	(ensures (mt_safe_elts h lv hs 0ul 0ul))
	(decreases (32 - U32.v lv))
let rec mt_safe_elts_init h lv hs =
  if lv = 32ul then ()
  else mt_safe_elts_init h (lv + 1ul) hs

val mt_safe_elts_preserved:
  lv:uint32_t{lv <= 32ul} ->
  hs:hash_vv{V.size_of hs = 32ul} -> 
  i:uint32_t -> j:uint32_t{j >= i} ->
  p:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (V.live h0 hs /\
		  mt_safe_elts h0 lv hs i j /\
		  loc_disjoint p (RV.loc_rvector hs) /\
		  modifies p h0 h1))
	(ensures (mt_safe_elts h1 lv hs i j))
	(decreases (32 - U32.v lv))
	[SMTPat (V.live h0 hs);
	SMTPat (mt_safe_elts h0 lv hs i j);
	SMTPat (loc_disjoint p (RV.loc_rvector hs));
	SMTPat (modifies p h0 h1)]
let rec mt_safe_elts_preserved lv hs i j p h0 h1 =
  if lv = 32ul then ()
  else (assert (loc_includes (RV.loc_rvector hs)
    			     (V.loc_vector_within hs lv (lv + 1ul)));
       V.get_preserved hs lv p h0 h1;
       mt_safe_elts_preserved (lv + 1ul) hs (i / 2ul) (j / 2ul) p h0 h1)

val mt_safe: HS.mem -> mt_p -> GTot Type0
let mt_safe h mt =
  B.live h mt /\ B.freeable mt /\
  (let mtv = B.get h mt 0 in
  // Liveness & Accessibility
  RV.rv_inv h (MT?.hs mtv) /\
  RV.rv_inv h (MT?.rhs mtv) /\
  mt_safe_elts h 0ul (MT?.hs mtv) (MT?.i mtv) (MT?.j mtv) /\
  // Regionality
  HH.extends (V.frameOf (MT?.hs mtv)) (B.frameOf mt) /\
  HH.extends (V.frameOf (MT?.rhs mtv)) (B.frameOf mt) /\
  HH.disjoint (V.frameOf (MT?.hs mtv)) (V.frameOf (MT?.rhs mtv)))

val mt_loc: mt_p -> GTot loc
let mt_loc mt = 
  B.loc_all_regions_from false (B.frameOf mt)

/// Construction

// NOTE: the public function is `create_mt` defined below, which
// builds a tree with an initial hash.
private val create_empty_mt: r:erid ->
  HST.ST mt_p
	 (requires (fun _ -> true))
	 (ensures (fun h0 mt h1 ->
	   modifies (mt_loc mt) h0 h1 /\
	   B.frameOf mt = r /\
	   mt_safe h1 mt /\
	   mt_not_full h1 mt))
#reset-options "--z3rlimit 20"
private let create_empty_mt r =
  let hs_region = RV.new_region_ r in
  let hs = RV.create_rid bhreg 32ul hs_region in
  let h0 = HST.get () in
  assume (V.forall_ h0 hs 0ul (V.size_of hs)
	   (fun hv -> V.size_of hv = 0ul));
  mt_safe_elts_init h0 0ul hs;
  let rhs_region = RV.new_region_ r in
  let rhs = RV.create_rid hreg 32ul rhs_region in
  let h1 = HST.get () in
  mt_safe_elts_preserved
    0ul hs 0ul 0ul (V.loc_vector rhs) h0 h1;
  let mt = B.malloc r (MT 0ul 0ul hs false rhs) 1ul in
  let h2 = HST.get () in
  mt_safe_elts_preserved
    0ul hs 0ul 0ul (B.loc_buffer mt) h1 h2;
  mt

/// Destruction (free)

val free_mt: mt:mt_p ->
  HST.ST unit
	 (requires (fun h0 -> mt_safe h0 mt))
	 (ensures (fun h0 _ h1 -> modifies (mt_loc mt) h0 h1))
let free_mt mt =
  let mtv = B.index mt 0ul in
  RV.free (MT?.hs mtv);
  RV.free (MT?.rhs mtv);
  B.free mt

/// Insertion

private val insert_:
  lv:uint32_t{lv < 32ul} ->
  i:Ghost.erased uint32_t ->
  j:uint32_t{Ghost.reveal i <= j && j < U32.uint_to_t (UInt.max_int U32.n)} ->
  hs:hash_vv{V.size_of hs = 32ul} ->
  acc:hash ->
  HST.ST unit
	 (requires (fun h0 ->
	   RV.rv_inv h0 hs /\ 
	   Rgl?.r_inv hreg h0 acc /\
	   HH.disjoint (V.frameOf hs) (B.frameOf acc) /\
	   mt_safe_elts h0 lv hs (Ghost.reveal i) j))
	 (ensures (fun h0 _ h1 ->
	   // Need more fine-grained one for below.
	   modifies (RV.loc_rvector hs) h0 h1 /\
	   RV.rv_inv h1 hs /\
	   mt_safe_elts h1 lv hs (Ghost.reveal i) (j + 1ul)))
private let rec insert_ lv i j hs acc =
  admit ();
  let ihv = RV.insert_copy hcpy (V.index hs lv) acc in
  RV.assign hs lv ihv;
  if j % 2ul = 1ul
  then (let lvhs = V.index hs lv in
       hash_2 (V.index lvhs (V.size_of lvhs - 2ul)) acc acc;
       insert_ (lv + 1ul)
	       (Ghost.hide (Ghost.reveal i / 2ul)) (j / 2ul) 
	       hs acc)

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
	   modifies (mt_loc mt) h0 h1 /\
	   mt_safe h1 mt))
#reset-options "--z3rlimit 40 --max_fuel 0"
let mt_insert mt v =
  // let hh0 = HST.get () in
  let mtv = B.index mt 0ul in
  insert_ 0ul (Ghost.hide (MT?.i mtv)) (MT?.j mtv) (MT?.hs mtv) v;
  // let hh1 = HST.get () in
  // RV.rv_inv_preserved
  //   (MT?.rhs mtv) (RV.loc_rvector (MT?.hs mtv)) hh0 hh1;
  B.upd mt 0ul 
    (MT (MT?.i mtv)
	(MT?.j mtv + 1ul)
	(MT?.hs mtv)
	false // `rhs` is always deprecated right after an insertion.
	(MT?.rhs mtv))
  // let hh2 = HST.get () in
  // RV.rv_inv_preserved
  //   (MT?.hs mtv) (B.loc_buffer mt) hh1 hh2;
  // RV.rv_inv_preserved
  //   (MT?.rhs mtv) (B.loc_buffer mt) hh1 hh2;
  // mt_safe_elts_preserved
  //   0ul (MT?.hs mtv) (MT?.i mtv) (MT?.j mtv + 1ul) (B.loc_buffer mt)
  //   hh1 hh2

val create_mt: r:erid -> init:hash ->
  HST.ST mt_p
	 (requires (fun h0 -> 
	   Rgl?.r_inv hreg h0 init /\
	   HH.disjoint r (B.frameOf init)))
	 (ensures (fun h0 mt h1 ->
	   modifies (mt_loc mt) h0 h1 /\
	   mt_safe h1 mt))
let create_mt r init =
  let mt = create_empty_mt r in
  mt_insert mt init;
  mt

/// Construction and Destruction of paths

type path = B.pointer (RV.rvector hreg)

val path_safe: HS.mem -> path -> GTot Type0
let path_safe h p =
  B.live h p /\ B.freeable p /\
  RV.rv_inv h (B.get h p 0) /\
  HH.extends (V.frameOf (B.get h p 0)) (B.frameOf p)

val path_loc: path -> GTot loc
let path_loc p = B.loc_all_regions_from false (B.frameOf p)

val path_safe_preserved:
  p:path -> dl:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (path_safe h0 p /\
		  loc_disjoint dl (path_loc p) /\
		  modifies dl h0 h1))
	(ensures (path_safe h1 p))
	[SMTPat (path_safe h0 p);
	SMTPat (loc_disjoint dl (path_loc p));
	SMTPat (modifies dl h0 h1)]
let path_safe_preserved p dl h0 h1 =
  assert (loc_includes (path_loc p) (loc_rvector (B.get h0 p 0)));
  assert (loc_includes (path_loc p) (loc_buffer p));
  rv_inv_preserved (B.get h0 p 0) dl h0 h1

val init_path: 
  r:erid ->
  HST.ST path
    (requires (fun h0 -> true))
    (ensures (fun h0 p h1 -> path_safe h1 p))
let init_path r =
  let nrid = RV.new_region_ r in
  B.malloc r (hash_vec_r_init nrid) 1ul

val clear_path:
  p:path ->
  HST.ST unit
    (requires (fun h0 -> path_safe h0 p))
    (ensures (fun h0 _ h1 -> 
      path_safe h1 p /\ V.size_of (B.get h1 p 0) = 0ul))
let clear_path p =
  B.upd p 0ul (V.clear (B.index p 0ul))

val free_path:
  p:path ->
  HST.ST unit
    (requires (fun h0 -> 
      B.live h0 p /\ B.freeable p /\
      V.live h0 (B.get h0 p 0) /\ V.freeable (B.get h0 p 0) /\
      HH.extends (V.frameOf (B.get h0 p 0)) (B.frameOf p)))
    (ensures (fun h0 _ h1 -> modifies (path_loc p) h0 h1))
let free_path p =
  V.free (B.index p 0ul);
  B.free p

/// Getting the Merkle root and path

// Construct the rightmost hashes for a given (incomplete) Merkle tree.
// This function calculates the Merkle root as well, which is the final
// accumulator value.
private val construct_rhs:
  lv:uint32_t{lv <= 32ul} ->
  hs:hash_vv{V.size_of hs = 32ul} ->
  rhs:hash_vec{V.size_of rhs = 32ul} ->
  i:uint32_t ->
  j:uint32_t{i <= j && U32.v j < pow2 (32 - U32.v lv)} ->
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
	   modifies (loc_union
		      (RV.loc_rvector rhs)
		      (B.loc_all_regions_from false (B.frameOf acc))) h0 h1 /\
	   RV.rv_inv h1 rhs /\
	   Rgl?.r_inv hreg h1 acc))
	 (decreases (U32.v j))
#reset-options "--z3rlimit 200 --max_fuel 1"
private let rec construct_rhs lv hs rhs i j acc actd =
  let ofs = offset_of i in
  let copy = Cpy?.copy hcpy in
  if j = 0ul then ()
  else
    (if j % 2ul = 0ul
    then (Math.Lemmas.pow2_double_mult (32 - U32.v lv - 1);
	 let hh = HST.get () in
	 mt_safe_elts_rec hh lv hs i j;
	 construct_rhs (lv + 1ul) hs rhs (i / 2ul) (j / 2ul) acc actd)
    else (if actd
    	 then (let hh0 = HST.get () in
	      RV.assign_copy hcpy rhs lv acc;
	      let hh1 = HST.get () in
	      Rgl?.r_sep hreg acc
		(B.loc_all_regions_from false (V.frameOf rhs)) hh0 hh1;
	      RV.rv_inv_preserved
	      	hs (B.loc_all_regions_from false (V.frameOf rhs))
	      	hh0 hh1;
	      RV.rv_inv_preserved
	      	(V.index hs lv) (B.loc_all_regions_from false (V.frameOf rhs))
	      	hh0 hh1;
	      mt_safe_elts_preserved lv hs i j
	      	(B.loc_all_regions_from false (V.frameOf rhs))
	      	hh0 hh1;
	      mt_safe_elts_head hh1 lv hs i j;
	      hash_2 (V.index (V.index hs lv) (j - 1ul - ofs)) acc acc;
	      let hh2 = HST.get () in
	      mt_safe_elts_preserved lv hs i j
		(B.loc_all_regions_from false (B.frameOf acc))
		hh1 hh2;
	      RV.rv_inv_preserved
		hs (B.loc_region_only false (B.frameOf acc))
		hh1 hh2;
	      RV.rv_inv_preserved
		rhs (B.loc_region_only false (B.frameOf acc))
		hh1 hh2)
	 else (let hh1 = HST.get () in
	      mt_safe_elts_head hh1 lv hs i j;
	      assert (RV.rv_inv hh1 (V.get hh1 hs lv));
	      assert (RV.elems_reg hh1 (V.get hh1 hs lv));
	      assert (HH.extends
		       (B.frameOf (V.get hh1 (V.get hh1 hs lv) (j - 1ul - ofs)))
		       (V.frameOf (V.get hh1 hs lv)));
	      assert (HH.extends (V.frameOf (V.get hh1 hs lv))
				 (V.frameOf hs));
	      copy (V.index (V.index hs lv) (j - 1ul - ofs)) acc;
	      let hh2 = HST.get () in
	      mt_safe_elts_preserved lv hs i j
		(B.loc_all_regions_from false (B.frameOf acc))
		hh1 hh2;
	      RV.rv_inv_preserved
		hs (B.loc_all_regions_from false (B.frameOf acc))
		hh1 hh2;
	      RV.rv_inv_preserved
		rhs (B.loc_all_regions_from false (B.frameOf acc))
		hh1 hh2);
	 let hh3 = HST.get () in
	 mt_safe_elts_rec hh3 lv hs i j;
	 construct_rhs (lv + 1ul) hs rhs (i / 2ul) (j / 2ul) acc true))

val mt_get_root:
  mt:mt_p -> 
  rt:hash ->
  HST.ST unit
	 (requires (fun h0 -> 
	   mt_safe h0 mt /\ Rgl?.r_inv hreg h0 rt /\
	   HH.disjoint (B.frameOf mt) (B.frameOf rt)))
	 (ensures (fun h0 _ h1 ->
	   modifies (loc_union
		      (mt_loc mt)
		      (B.loc_all_regions_from false (B.frameOf rt))) h0 h1 /\
	   mt_safe h1 mt /\ Rgl?.r_inv hreg h1 rt))
let mt_get_root mt rt =
  let hh0 = HST.get () in
  let mtv = B.index mt 0ul in
  let i = MT?.i mtv in
  let j = MT?.j mtv in
  let hs = MT?.hs mtv in
  let rhs = MT?.rhs mtv in
  construct_rhs 0ul hs rhs i j rt false;
  let hh1 = HST.get () in
  assert (RV.rv_inv hh1 rhs);
  assert (Rgl?.r_inv hreg hh1 rt);
  assert (B.live hh1 mt);
  RV.rv_inv_preserved
    hs (loc_union
         (RV.loc_rvector rhs)
	 (B.loc_all_regions_from false (B.frameOf rt)))
    hh0 hh1;
  mt_safe_elts_preserved 0ul hs i j
    (loc_union
      (RV.loc_rvector rhs)
      (B.loc_all_regions_from false (B.frameOf rt)))
  hh0 hh1;
  B.upd mt 0ul (MT i j hs true rhs);
  let hh2 = HST.get () in
  Rgl?.r_sep hreg rt (B.loc_buffer mt) hh1 hh2;
  RV.rv_inv_preserved hs (B.loc_buffer mt) hh1 hh2;
  RV.rv_inv_preserved rhs (B.loc_buffer mt) hh1 hh2;
  mt_safe_elts_preserved 0ul hs i j
    (B.loc_buffer mt) hh1 hh2

// Construct a Merkle path for a given index `k`, hashes `hs`, 
// and rightmost hashes `rhs`.
// Caution: current impl. copies "pointers" in the Merkle tree 
//          to the output path.
private val mt_get_path_:
  lv:uint32_t{lv < 32ul} ->
  hs:hash_vv{V.size_of hs = 32ul} ->
  rhs:hash_vec{V.size_of rhs = 32ul} ->
  i:uint32_t -> j:uint32_t{i <= j} -> 
  k:uint32_t{i <= k && k <= j} ->
  p:path ->
  actd:bool ->
  HST.ST unit
	 (requires (fun h0 ->
	   RV.rv_inv h0 hs /\ RV.rv_inv h0 rhs /\
	   HH.disjoint (V.frameOf hs) (V.frameOf rhs) /\
	   mt_safe_elts h0 lv hs i j /\
	   path_safe h0 p))
	 (ensures (fun h0 _ h1 ->
	   modifies (path_loc p) h0 h1 /\
	   path_safe h1 p))
private let rec mt_get_path_ lv hs rhs i j k p actd =
  admit ();
  let ofs = offset_of i in
  if j = 0ul then ()
  else
    (let pv = B.index p 0ul in
    if k % 2ul = 1ul
    then B.upd p 0ul (V.insert pv (V.index (V.index hs lv) (k - 1ul - ofs)))
    else
      (if k = j then ()
      else if k + 1ul = j
      then (if actd then B.upd p 0ul (V.insert pv (V.index rhs lv)))
      else B.upd p 0ul (V.insert pv (V.index (V.index hs lv) (k + 1ul - ofs))));
    mt_get_path_ (lv + 1ul) hs rhs (i / 2ul) (j / 2ul) (k / 2ul) p
		 (if j % 2 = 0ul then actd else true))

val mt_get_path:
  mt:mt_p -> 
  idx:uint32_t ->
  p:path ->
  root:hash ->
  HST.ST uint32_t
	 (requires (fun h0 ->
	   MT?.i (B.get h0 mt 0) <= idx /\ idx < MT?.j (B.get h0 mt 0) /\
	   mt_safe h0 mt /\ path_safe h0 p /\
	   Rgl?.r_inv hreg h0 root))
	 (ensures (fun h0 _ h1 ->
	   modifies (loc_union (mt_loc mt) (path_loc p)) h0 h1 /\
	   mt_safe h1 mt /\
	   path_safe h1 p))
let mt_get_path mt idx p root =
  admit ();
  let copy = Cpy?.copy hcpy in
  let mtv = B.index mt 0ul in
  let i = MT?.i mtv in
  let ofs = offset_of (MT?.i mtv) in
  let j = MT?.j mtv in
  let hs = MT?.hs mtv in
  let rhs = MT?.rhs mtv in
  if not (MT?.rhs_ok mtv) then
    (copy (V.index (V.index hs 0ul) (j - 1ul - ofs)) root;
    construct_rhs 0ul hs rhs i j root false;
    B.upd mt 0ul (MT i j hs true rhs))
  else ();
  let ih = V.index (V.index hs 0ul) (idx - ofs) in
  B.upd p 0ul (RV.insert_copy hcpy (B.index p 0ul) ih);
  mt_get_path_ 0ul hs rhs i j idx p false;
  j

/// Flushing

private val mt_flush_to_:
  lv:uint32_t{lv < 32ul} ->
  hs:hash_vv{V.size_of hs = 32ul} ->
  i:uint32_t ->
  HST.ST unit
	 (requires (fun h0 -> true))
	 (ensures (fun h0 _ h1 -> true))
private let rec mt_flush_to_ lv hs i =
  admit ();
  if i = 0ul then ()
  else (let ofs = offset_of i in
       let hvec = V.index hs lv in
       RV.assign hs lv (RV.flush hvec ofs);
       mt_flush_to_ (lv + 1ul) hs (i / 2ul))

val mt_flush_to:
  mt:mt_p ->
  idx:uint32_t ->
  HST.ST unit
	 (requires (fun h0 -> true))
	 (ensures (fun h0 _ h1 -> true))
let rec mt_flush_to mt idx =
  admit ();
  let mtv = B.index mt 0ul in
  mt_flush_to_ 0ul (MT?.hs mtv) (idx - MT?.i mtv);
  B.upd mt 0ul (MT idx (MT?.j mtv)
		   (MT?.hs mtv)
		   (MT?.rhs_ok mtv)
		   (MT?.rhs mtv))

val mt_flush:
  mt:mt_p ->
  HST.ST unit
	 (requires (fun h0 -> true))
	 (ensures (fun h0 _ h1 -> true))
let mt_flush mt =
  admit ();
  let mtv = B.index mt 0ul in
  mt_flush_to mt (MT?.j mtv)

/// Client-side verification

private val mt_verify_:
  k:uint32_t ->
  j:uint32_t{k <= j} ->
  p:path ->
  ppos:uint32_t ->
  acc:hash ->
  actd:bool ->
  HST.ST unit
	 (requires (fun h0 ->
	   path_safe h0 p /\ Rgl?.r_inv hreg h0 acc /\
	   HH.disjoint (B.frameOf p) (B.frameOf acc) /\
	   (let psz = V.size_of (B.get h0 p 0) in
	   ppos <= psz /\ U32.v j < pow2 (U32.v (psz - ppos)))))
	 (ensures (fun h0 _ h1 ->
	   modifies (B.loc_all_regions_from false (B.frameOf acc)) h0 h1 /\
	   Rgl?.r_inv hreg h1 acc))
private let rec mt_verify_ k j p ppos acc actd =
  if j = 0ul then ()
  else (let nactd = actd || (j % 2ul = 1ul) in
       let phash = V.index (B.index p 0ul) ppos in
       if k % 2ul = 0ul
       then (if j = k || (j = k + 1ul && not actd)
	    then mt_verify_ (k / 2ul) (j / 2ul) p ppos acc nactd
	    else (hash_2 acc phash acc;
		 mt_verify_ (k / 2ul) (j / 2ul) p (ppos + 1ul) acc nactd))
       else (hash_2 phash acc acc;
	    mt_verify_ (k / 2ul) (j / 2ul) p (ppos + 1ul) acc nactd))

private val buf_eq:
  #a:eqtype -> b1:B.buffer a -> b2:B.buffer a ->
  len:uint32_t ->
  HST.ST bool
	 (requires (fun h0 -> 
	   B.live h0 b1 /\ B.live h0 b2 /\
	   len <= B.len b1 /\ len <= B.len b2))
	 (ensures (fun h0 _ h1 -> h0 == h1))
private let rec buf_eq #a b1 b2 len =
  if len = 0ul then true
  else (let a1 = B.index b1 (len - 1ul) in
       let a2 = B.index b2 (len - 1ul) in
       let teq = buf_eq b1 b2 (len - 1ul) in
       a1 = a2 && teq)

val mt_verify:
  k:uint32_t ->
  j:uint32_t{k < j} ->
  p:path ->
  rt:hash ->
  HST.ST bool
	 (requires (fun h0 ->
	   path_safe h0 p /\ Rgl?.r_inv hreg h0 rt /\
	   HST.is_eternal_region (B.frameOf rt) /\
	   HH.disjoint (B.frameOf p) (B.frameOf rt) /\
	   (let psz = V.size_of (B.get h0 p 0) in
	   1ul <= psz /\ U32.v j <= pow2 (U32.v psz - 1))))
	 (ensures (fun h0 _ h1 ->
	   // `rt` is not modified in this function, but we use a trick 
	   // to allocate an auxiliary buffer in the extended region of `rt`.
	   modifies (B.loc_all_regions_from false (B.frameOf rt)) h0 h1 /\
	   Rgl?.r_inv hreg h1 rt /\
	   S.equal (Rgl?.r_repr hreg h0 rt)
		   (Rgl?.r_repr hreg h1 rt)))
let mt_verify k j p rt =
  let hh0 = HST.get () in
  let nrid = RV.new_region_ (B.frameOf rt) in
  let ih = hash_r_init nrid in
  let copy = Cpy?.copy hcpy in
  copy (V.index (B.index p 0ul) 0ul) ih;
  let hh1 = HST.get () in
  path_safe_preserved p (B.loc_all_regions_from false (B.frameOf rt)) hh0 hh1;
  mt_verify_ k j p 1ul ih false;
  buf_eq ih rt hash_size

