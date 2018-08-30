module MerkleTree.New.Low

open EverCrypt.Hash
open EverCrypt.Helpers

open FStar.All
open FStar.Integers
open FStar.Mul
open LowStar.Modifies
open LowStar.BufferOps
open LowStar.Vector
// open LowStar.BufVector
open LowStar.RVector
open LowStar.RVector.Instances

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MHS = FStar.Monotonic.HyperStack
module HH = FStar.Monotonic.HyperHeap

module B = LowStar.Buffer
module V = LowStar.Vector
// module BV = LowStar.BufVector
module RV = LowStar.RVector
module RVI = LowStar.RVector.Instances
module S = FStar.Seq

module U32 = FStar.UInt32
module U8 = FStar.UInt8

module EHS = EverCrypt.Hash
module EHL = EverCrypt.Helpers

val hash_size: uint32_t
let hash_size = 32ul // EHS.tagLen EHS.SHA256

type hash = uint8_p

val hreg: RV.regional hash
let hreg = RVI.buffer_regional 0uy hash_size

val hcpy: RV.copyable hash hreg
let hcpy = RVI.buffer_copyable 0uy hash_size

val bhreg: RV.regional (RV.rvector #hash hreg)
let bhreg = RVI.buffer_vector_regional 0uy hash_size

/// Compression of two hashes

val hash_2: 
  src1:hash -> src2:hash -> dst:hash ->
  HST.ST unit
	 (requires (fun h0 ->
	   Rgl?.r_inv hreg h0 src1 /\ 
	   Rgl?.r_inv hreg h0 src2 /\
	   Rgl?.r_inv hreg h0 dst))
	 (ensures (fun h0 _ h1 -> true))
#reset-options "--z3rlimit 40"
let hash_2 src1 src2 dst =
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
  HST.pop_frame ()

/// Low-level Merkle tree data structure

type hash_vec = RV.rvector hreg
type hash_vv = RV.rvector bhreg

// A Merkle tree `MT i j hs rhs_ok rhs` stores all necessary hashes to generate
// a Merkle path for each element from the index `i` to `j-1`.
// - Parameters
// `hs`: a 2-dim store for hashes, where `hs[0]` contains leaf hash values.
// `rhs_ok`: to check the rightmost hashes are up-to-date
// `rhs`: a store for "rightmost" hashes, manipulated only when required to
//        calculate some merkle parhs that need the rightmost hashes
//        as a part of them.
noeq type merkle_tree = 
| MT: i:uint32_t -> j:uint32_t{j > i} ->
      hs:hash_vv{V.size_of hs = 32ul} ->
      rhs_ok:bool ->
      rhs:hash_vec{V.size_of hs = 32ul} ->
      merkle_tree

type mt_p = B.pointer merkle_tree

/// Construction

val create_mt_: 
  hs:hash_vv{V.size_of hs = 32ul} ->
  depth:uint32_t{depth <= 32ul} ->
  HST.ST unit
	 (requires (fun h0 -> 
	   V.live h0 hs /\
	   HST.is_eternal_region (V.frameOf hs)))
	 (ensures (fun h0 mt h1 -> true))
	 (decreases (U32.v depth))
let rec create_mt_ hs depth =
  if depth = 0ul then ()
  else (let dr = RV.new_region_ (V.frameOf hs) in
       let hv = RV.create_reserve hreg 1ul dr in
       V.assign hs (depth - 1ul) hv;
       create_mt_ hs (depth - 1ul))

val create_mt: init:hash ->
  HST.ST mt_p
	 (requires (fun _ -> true))
	 (ensures (fun h0 mt h1 -> true))
let create_mt init =
  admit ();
  let mt_region = RV.new_region_ HH.root in
  let hs = RV.create_rid bhreg 32ul mt_region in
  create_mt_ hs 32ul;
  V.assign hs 0ul (RV.insert_copy hcpy (V.index hs 0ul) init);
  let rhs = RV.create hreg 32ul in
  B.malloc HH.root (MT 0ul 1ul hs true rhs) 1ul

/// Destruction (free)

val free_mt: mt:mt_p ->
  HST.ST unit
	 (requires (fun h0 -> B.live h0 mt))
	 (ensures (fun h0 _ h1 -> true))
let free_mt mt =
  admit ();
  let mtv = B.index mt 0ul in
  RV.free (MT?.hs mtv);
  RV.free (MT?.rhs mtv);
  B.free mt

/// Insertion

val insert_:
  lv:uint32_t{lv < 32ul} ->
  j:uint32_t ->
  hs:hash_vv{V.size_of hs = 32ul} ->
  acc:hash ->
  HST.ST unit
	 (requires (fun h0 -> true))
	 (ensures (fun h0 _ h1 -> true))
let rec insert_ lv j hs acc =
  admit ();
  RV.assign hs lv (RV.insert_copy hcpy (V.index hs lv) acc);
  if j % 2ul = 1ul
  then (hash_2 (V.back (V.index hs lv)) acc acc;
       insert_ (lv + 1ul) (j / 2ul) hs acc)

// Caution: current impl. manipulates the content in `v`.
val insert:
  mt:mt_p -> v:hash ->
  HST.ST unit
	 (requires (fun h0 -> true))
	 (ensures (fun h0 _ h1 -> true))
let rec insert mt v =
  admit ();
  let mtv = B.index mt 0ul in
  insert_ 0ul (MT?.j mtv) (MT?.hs mtv) v;
  B.upd mt 0ul 
    (MT (MT?.i mtv)
	(MT?.j mtv + 1ul)
	(MT?.hs mtv)
	false // `rhs` is always deprecated right after an insertion.
	(MT?.rhs mtv))

/// Getting the Merkle root and path

// Construct the rightmost hashes for a given (incomplete) Merkle tree.
// This function calculates the Merkle root as well, which is the final
// accumulator value.
val construct_rhs:
  lv:uint32_t{lv < 32ul} ->
  hs:hash_vv{V.size_of hs = 32ul} ->
  rhs:hash_vec{V.size_of rhs = 32ul} ->
  j:uint32_t ->
  acc:hash -> actd:bool ->
  HST.ST unit
	 (requires (fun h0 -> true))
	 (ensures (fun h0 _ h1 -> true))
let rec construct_rhs lv hs rhs j acc actd =
  admit ();
  if j = 0ul then ()
  else if j % 2ul = 0ul
  then
    // If `j` is even, it already has a rightmost hash of (lv + 1ul)
    construct_rhs (lv + 1ul) hs rhs (j / 2ul) acc actd
  else (
    (if actd
    then (hash_2 (V.index (V.index hs lv) (j - 1ul)) acc acc;
	 RV.assign_copy hcpy rhs (lv + 1ul) acc)
    else Cpy?.copy hcpy (V.index (V.index hs lv) (j - 1ul)) acc);
    construct_rhs (lv + 1ul) hs rhs (j / 2ul) acc true)

// Construct a Merkle path for a given index `k`, hashes `hs`, 
// and rightmost hashes `rhs`.
// Caution: current impl. copies "pointers" in the Merkle tree 
//          to the output path.
val mt_get_path_:
  lv:uint32_t{lv < 32ul} ->
  hs:hash_vv{V.size_of hs = 32ul} ->
  rhs:hash_vec{V.size_of rhs = 32ul} ->
  j:uint32_t -> k:uint32_t{j = 0ul || k <= j} ->
  path:B.pointer (V.vector hash) ->
  HST.ST unit
	 (requires (fun h0 -> true))
	 (ensures (fun h0 _ h1 -> true))
let rec mt_get_path_ lv hs rhs j k path =
  admit ();
  if j <= 1ul then ()
  else 
    (if k % 2ul = 0ul
    then (if k = j then ()
	 else if k + 1ul < j
	 then B.upd path 0ul (V.insert (B.index path 0ul)
				       (V.index (V.index hs lv) (k + 1ul)))
	 else B.upd path 0ul (V.insert (B.index path 0ul) (V.index rhs lv)))
    else B.upd path 0ul (V.insert (B.index path 0ul) 
				  (V.index (V.index hs lv) (k - 1ul)));
    mt_get_path_ (lv + 1ul) hs rhs (j / 2ul) (k / 2ul) path)

val mt_get_path:
  mt:mt_p -> 
  idx:uint32_t -> // {MT?.i mt <= idx && idx < MT?.j mt}
  root:hash ->
  path:B.pointer (V.vector hash) ->
  HST.ST uint32_t
	 (requires (fun h0 -> true))
	 (ensures (fun h0 _ h1 -> true))
let mt_get_path mt idx root path =
  admit ();
  let mtv = B.index mt 0ul in
  if not (MT?.rhs_ok mtv) then
    (construct_rhs 0ul (MT?.hs mtv) (MT?.rhs mtv) (MT?.j mtv) root false;
    B.upd mt 0ul (MT (MT?.i mtv) (MT?.j mtv) (MT?.hs mtv) true (MT?.rhs mtv)))
  else ();
  mt_get_path_ 0ul (MT?.hs mtv) (MT?.rhs mtv) (MT?.j mtv) idx path;
  MT?.j mtv

/// Flushing

// TODO: need to think about flushing after deciding a proper 
//       data structure for `MT?.hs`.
// NOTE: flush "until" `idx`
val mt_flush_to:
  mt:mt_p ->
  idx:uint32_t ->
  HST.ST unit
	 (requires (fun h0 -> true))
	 (ensures (fun h0 _ h1 -> true))
let mt_flush_to mt idx = ()

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

val mt_verify_:
  k:uint32_t ->
  j:uint32_t{j = 0ul || k <= j} ->
  path:V.vector hash ->
  ppos:uint32_t{ppos < V.size_of path} ->
  acc:hash ->
  HST.ST unit
	 (requires (fun h0 -> true))
	 (ensures (fun h0 _ h1 -> true))
let rec mt_verify_ k j path ppos acc =
  admit ();
  if j <= 1ul then ()
  else (if k % 2ul = 0ul
       then (if k = j then mt_verify_ (k / 2ul) (j / 2ul) path ppos acc
	    else (hash_2 acc (V.index path ppos) acc;
		 mt_verify_ (k / 2ul) (j / 2ul) path (ppos + 1ul) acc))
       else (hash_2 (V.index path ppos) acc acc;
	    mt_verify_ (k / 2ul) (j / 2ul) path (ppos + 1ul) acc))

val buf_eq:
  #a:eqtype -> b1:B.buffer a -> b2:B.buffer a ->
  len:uint32_t ->
  HST.ST bool
	 (requires (fun h0 -> 
	   B.live h0 b1 /\ B.live h0 b2 /\
	   len <= B.len b1 /\ len <= B.len b2))
	 (ensures (fun h0 _ h1 -> true))
let rec buf_eq #a b1 b2 len =
  if len = 0ul then true
  else (let a1 = B.index b1 (len - 1ul) in
       let a2 = B.index b2 (len - 1ul) in
       let teq = buf_eq b1 b2 (len - 1ul) in
       a1 = a2 && teq)

val mt_verify:
  k:uint32_t ->
  j:uint32_t{k < j} ->
  path:V.vector hash{V.size_of path > 0ul} ->
  root:hash ->
  HST.ST bool
	 (requires (fun h0 -> true))
	 (ensures (fun h0 _ h1 -> true))
let mt_verify k j path root =
  admit ();
  let acc = B.malloc HH.root 0uy hash_size in
  mt_verify_ k j path 0ul acc;
  buf_eq acc root hash_size

