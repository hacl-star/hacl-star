module MerkleTree.EverCrypt

open MerkleTree.Low

module HH = FStar.Monotonic.HyperHeap
module B = LowStar.Buffer

module HST = FStar.HyperStack.ST
module MTH = MerkleTree.New.High
module MTLD = MerkleTree.Low.Datastructures
module MLH = MerkleTree.Low.Hashfunctions

open LowStar.Regional

// ---

module S = FStar.Seq

module EHS = EverCrypt.Hash

open MerkleTree.Low.Datastructures

open Lib.IntTypes

#push-options "--z3rlimit 40 --max_fuel 0"
let mt_sha256_compress src1 src2 dst =
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


let mt_create r init =
  mt_create_custom 32ul (MerkleTree.New.High.sha256_compress) r init mt_sha256_compress


