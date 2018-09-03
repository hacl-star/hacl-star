module MerkleTree.New.High

open EverCrypt
// open EverCrypt.Hash
open EverCrypt.Helpers

open FStar.All
open FStar.Ghost
open FStar.Integers
open FStar.Mul
open FStar.Seq

module List = FStar.List.Tot
module S = FStar.Seq

module U32 = FStar.UInt32
module U8 = FStar.UInt8
type uint32_t = U32.t
type uint8_t = U8.t

module EHS = EverCrypt.Hash
module EHL = EverCrypt.Helpers

val hash_size: uint32_t
let hash_size = 32ul

let hash = b:EHS.bytes{S.length b = U32.v hash_size}
let hash_seq = S.seq hash

val hash_2: src1:hash -> src2:hash -> GTot hash
let hash_2 src1 src2 =
  EHS.extract (EHS.hash0 #(Ghost.hide EHS.SHA256) (S.append src1 src2))

/// High-level Merkle tree data structure

noeq type merkle_tree =
| MT: i:nat -> j:nat{j > i} ->
      hs:S.seq hash_seq{S.length hs = 32} ->
      rhs_ok:bool -> rhs:hash_seq{S.length rhs = 32} ->
      merkle_tree

