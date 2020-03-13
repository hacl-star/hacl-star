module MerkleTree.Low.Hashfunctions

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
module MTH = MerkleTree.New.High
module MTS = MerkleTree.Spec

open Lib.IntTypes

open MerkleTree.Low.Datastructures

#set-options "--z3rlimit 10 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

let init_hash (hsz:hash_size_t) (r:HST.erid): HST.St (hash #hsz) 
= rg_alloc (hreg hsz) r

#set-options "--z3rlimit 200 --initial_fuel 2 --max_fuel 2 --initial_ifuel 2 --max_ifuel 2"

let free_hash (#hsz:Ghost.erased hash_size_t) (h:hash #hsz): HST.ST unit
  (requires (fun h0 -> (Rgl?.r_inv (hreg hsz)) h0 h))
  (ensures (fun _ _ _ -> True))
= hash_r_free #hsz h

inline_for_extraction
type hash_fun_t (#hsz:hash_size_t) (#hash_spec:Ghost.erased (MTS.hash_fun_t #(U32.v hsz))) = src1:hash #hsz -> src2:hash #hsz -> dst:hash #hsz -> HST.ST unit
   (requires (fun h0 ->
     Rgl?.r_inv (hreg hsz) h0 src1 /\
     Rgl?.r_inv (hreg hsz) h0 src2 /\
     Rgl?.r_inv (hreg hsz) h0 dst))
   (ensures (fun h0 _ h1 ->
     // memory safety
     modifies (B.loc_region_only false (B.frameOf dst)) h0 h1 /\
     Rgl?.r_inv (hreg hsz) h1 dst /\
     // correctness
     S.equal (Rgl?.r_repr (hreg hsz) h1 dst)
             ((Ghost.reveal hash_spec) (Rgl?.r_repr (hreg hsz) h0 src1) (Rgl?.r_repr (hreg hsz) h0 src2))
     ))
