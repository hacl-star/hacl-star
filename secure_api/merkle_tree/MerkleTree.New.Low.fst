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

noeq type merkle_tree = 
| MT: hs:B.buffer hash_vec{B.length hs = U32.n} ->
      merkle_tree

/// Initialization

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
  MT hs

/// Insertion

// Think: is it better to have a library for 2-dim values (hashes)
//        to control memory safety / disjointness (by region)?


