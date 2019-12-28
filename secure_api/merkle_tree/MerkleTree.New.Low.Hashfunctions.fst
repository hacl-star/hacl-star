module MerkleTree.New.Low.Hashfunctions

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
module EHS = EverCrypt.Hash
module MTH = MerkleTree.New.High
module MTS = MerkleTree.Spec

open Lib.IntTypes

open MerkleTree.New.Low.Hashes
open MerkleTree.New.Low.Datastructures

#set-options "--z3rlimit 10 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

let init_hash (hsz:hash_size_t) = hash_r_alloc #hsz
let free_hash (hsz:hash_size_t) = hash_r_free #hsz

noextract inline_for_extraction unfold
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

val sha256_compress: hash_fun_t #32ul #(Ghost.hide MTH.sha256_compress)
#push-options "--z3rlimit 40 --max_fuel 0"
let sha256_compress src1 src2 dst =
  let hash_size = 32ul in
  let hash_alg = Spec.Hash.Definitions.SHA2_256 in
  let hh0 = HST.get () in
  HST.push_frame ();
  // KreMLin can't extract `EHS.blockLen EHS.SHA256` (= 64ul)
  let cb = B.alloca (u8 0) 64ul in
  B.blit src1 0ul cb 0ul hash_size;
  B.blit src2 0ul cb 32ul hash_size;

  // ONLY WORKS BECAUSE hash_alg is inline_for_extraction and is known to be SHA2_256
  let st = EHS.alloca hash_alg in
  EHS.init #(Ghost.hide hash_alg) st;
  let hh1 = HST.get () in
  assert (S.equal (S.append
                    (Rgl?.r_repr(hreg hash_size) hh0 src1)
                    (Rgl?.r_repr(hreg hash_size) hh0 src2))
                  (B.as_seq hh1 cb));

  EHS.update #(Ghost.hide hash_alg) st cb;
  let hh2 = HST.get () in
  assert (EHS.repr st hh2 == Spec.Agile.Hash.update hash_alg (Spec.Agile.Hash.init hash_alg) (B.as_seq hh1 cb));
  assert (S.equal (S.append S.empty (B.as_seq hh1 cb))
                  (B.as_seq hh1 cb));

  EHS.finish #(Ghost.hide hash_alg) st dst;
  let hh3 = HST.get () in
  assert (S.equal (B.as_seq hh3 dst)
                  (Spec.Hash.PadFinish.finish hash_alg (EHS.repr st hh2)));
  assert (S.equal (B.as_seq hh3 dst)
                  (Spec.Hash.PadFinish.finish hash_alg (Spec.Agile.Hash.update hash_alg (Spec.Agile.Hash.init hash_alg) (B.as_seq hh1 cb))));
  assert (S.equal (B.as_seq hh3 dst)
                  (MTH.sha256_compress
                    (Rgl?.r_repr(hreg hash_size) hh0 src1)
                    (Rgl?.r_repr(hreg hash_size) hh0 src2)));
  HST.pop_frame ();

  let hh4 = HST.get () in
  assert (S.equal (B.as_seq hh4 dst)
                  (MTH.sha256_compress
                    (Rgl?.r_repr(hreg hash_size) hh0 src1)
                    (Rgl?.r_repr(hreg hash_size) hh0 src2)))
#pop-options
