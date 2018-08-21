module MerkleTree.New.Low

open EverCrypt.Hash
open EverCrypt.Helpers

open FStar.All
open FStar.Integers
open FStar.Mul
open LowStar.Modifies
open LowStar.BufferOps
open LowStar.Vector
open LowStar.BufVector

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MHS = FStar.Monotonic.HyperStack
module HH = FStar.Monotonic.HyperHeap

module B = LowStar.Buffer
module V = LowStar.Vector
module BV = LowStar.BufVector
module S = FStar.Seq

module U32 = FStar.UInt32
module U8 = FStar.UInt8

module EHS = EverCrypt.Hash
module EHL = EverCrypt.Helpers

type hash = uint8_p
type hash_vec = BV.buf_vector uint8_t

val hash_size: uint32_t
let hash_size = EHS.tagLen EHS.SHA256

/// Compression of two hashes

assume val hash_2: 
  src1:hash -> src2:hash -> dst:hash ->
  HST.ST unit
	 (requires (fun h0 ->
	   BV.buffer_inv_live hash_size h0 src1 /\
	   BV.buffer_inv_live hash_size h0 src2 /\
	   BV.buffer_inv_live hash_size h0 dst))
	 (ensures (fun h0 _ h1 ->
	   // memory safety
	   modifies (B.loc_buffer dst) h0 h1))

/// Low-level Merkle tree data structure

// A Merkle tree `MT i j hs` stores all necessary hashes to generate
// a Merkle path for each element from the index `i` to `j-1`. 
// `hs` is a 2-dim store for hashes, where `hs[0]` contains leaf hash values.
noeq type merkle_tree = 
| MT: i:uint32_t -> j:uint32_t{j > i} ->
      hs:B.buffer hash_vec{B.length hs = U32.n} ->
      merkle_tree

/// Construction

val create_mt_: 
  hs:B.buffer hash_vec{B.length hs = U32.n} ->
  depth:uint32_t{depth <= 32ul} ->
  HST.ST unit
	 (requires (fun h0 -> 
	   B.live h0 hs /\
	   HST.is_eternal_region (B.frameOf hs)))
	 (ensures (fun h0 mt h1 -> true))
	 (decreases (U32.v depth))
let rec create_mt_ hs depth =
  if depth = 0ul then ()
  else (let dr = BV.new_region_ (B.frameOf hs) in
       let hv = BV.create_reserve hash_size 1ul dr in
       B.upd hs (depth - 1ul) hv;
       create_mt_ hs (depth - 1ul))

val create_mt: unit ->
  HST.ST merkle_tree
	 (requires (fun _ -> true))
	 (ensures (fun h0 mt h1 -> true))
let create_mt _ =
  let mt_region = BV.new_region_ HH.root in
  let hs = B.malloc mt_region (BV.create_empty uint8_t) 32ul in
  create_mt_ hs 32ul;
  MT 0ul 1ul hs

/// Destruction (free)

val free_mt_:
  lv:uint32_t{lv <= 32ul} ->
  hs:B.buffer hash_vec{B.length hs = U32.n} ->
  HST.ST unit
	 (requires (fun h0 -> true))
	 (ensures (fun h0 _ h1 -> true))
let rec free_mt_ lv hs =
  admit ();
  if lv = 0ul then ()
  else (V.free (B.index hs (lv - 1ul));
       free_mt_ (lv - 1ul) hs)

val free_mt: merkle_tree ->
  HST.ST unit
	 (requires (fun _ -> true))
	 (ensures (fun h0 _ h1 -> true))
let free_mt mt =
  admit ();
  free_mt_ 32ul (MT?.hs mt);
  B.free (MT?.hs mt)

/// Insertion

val insert_:
  lv:uint32_t{lv < 32ul} ->
  j:uint32_t ->
  hs:B.buffer hash_vec{B.length hs = U32.n} ->
  acc:hash ->
  HST.ST unit
	 (requires (fun h0 -> true))
	 (ensures (fun h0 _ h1 -> true))
let rec insert_ lv j hs acc =
  admit ();
  if j % 2ul = 0ul then 
    B.upd hs lv (V.insert (B.index hs lv) acc)
  else
    (B.upd hs lv (V.insert (B.index hs lv) acc);
    hash_2 (V.back (B.index hs lv)) acc acc;
    insert_ (lv + 1ul) (j / 2ul) hs acc)

// Caution: current impl. manipulates the content in `v`
//          as an accumulator.
val insert:
  mt:merkle_tree -> v:hash ->
  HST.ST merkle_tree
	 (requires (fun h0 -> true))
	 (ensures (fun h0 _ h1 -> true))
let rec insert mt v =
  admit ();
  insert_ 0ul (MT?.j mt) (MT?.hs mt) v;
  MT (MT?.i mt)
     (MT?.j mt + 1ul)
     (MT?.hs mt)

/// Getting the Merkle root and path

val mt_get_path_:
  hs:B.buffer hash_vec{B.length hs = U32.n} ->
  lv:uint32_t{lv < 32ul} ->
  i:uint32_t -> j:uint32_t ->
  k:uint32_t{i <= k && k < j} ->
  path:B.buffer hash{B.length path = U32.n} ->
  acc:hash ->
  HST.ST unit
	 (requires (fun h0 -> true))
	 (ensures (fun h0 _ h1 -> true))
let rec mt_get_path_ hs lv i j k path acc =
  admit ()

val mt_get_path:
  mt:merkle_tree -> 
  idx:uint32_t{MT?.i mt <= idx && idx < MT?.j mt} ->
  root:hash ->
  path:B.buffer hash{B.length path = U32.n} ->
  HST.ST uint32_t
	 (requires (fun h0 -> true))
	 (ensures (fun h0 _ h1 -> true))
let mt_get_path mt idx root path =
  mt_get_path_ (MT?.hs mt) 0ul (MT?.i mt) (MT?.j mt) idx path root;
  MT?.j mt

/// Flushing

// TODO: need to think about flushing after deciding a proper data structure
//       for `MT?.hs`.
// NOTE: flush "until" `idx`
val mt_flush_to:
  mt:merkle_tree ->
  idx:uint32_t{idx <= MT?.j mt} ->
  HST.ST unit
	 (requires (fun h0 -> true))
	 (ensures (fun h0 _ h1 -> true))
let mt_flush_to mt idx = ()

val mt_flush:
  mt:merkle_tree ->
  HST.ST unit
	 (requires (fun h0 -> true))
	 (ensures (fun h0 _ h1 -> true))
let mt_flush mt =
  mt_flush_to mt (MT?.j mt)

/// Client-side verification

val mt_verify_:
  lv:uint32_t{lv < 32ul} ->
  k:uint32_t ->
  j:uint32_t{j = 0ul || k < j} ->
  path:B.buffer hash{B.length path = U32.n} ->
  acc:hash ->
  HST.ST unit
	 (requires (fun h0 -> true))
	 (ensures (fun h0 _ h1 -> true))
let rec mt_verify_ lv k j path acc =
  admit ();
  if j = 0ul then ()
  else
    (if k % 2ul = 1ul
    then (if k + 1ul < j
	 then hash_2 acc (B.index path lv) acc
	 else ())
    else hash_2 (B.index path lv) acc acc;
    mt_verify_ (lv + 1ul) (k / 2ul) (j / 2ul) path acc)

