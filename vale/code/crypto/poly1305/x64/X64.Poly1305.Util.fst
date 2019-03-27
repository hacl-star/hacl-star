module X64.Poly1305.Util

open FStar.Tactics
open FStar.Tactics.Canon
open FStar.Math.Lemmas
open FStar.Math.Lib
open FStar.Mul
open X64.Vale.State   // needed for mem
open X64.Poly1305.Bitvectors
open X64.Memory

// private unfold let op_Star = op_Multiply

//#reset-options "--z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3 --z3cliopt smt.arith.nl=false --max_fuel 0 --max_ifuel 0 --smtencoding.elim_box true --eager_inference --smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native"

(* Getting a weird error otherwise, will file an issue
   when this gets merged in fstar branch *)
let poly1305_heap_blocks h pad r s k =
  if 0 <= k && k <= Seq.length s && k % 2 = 0 then
    poly1305_heap_blocks' h pad r s k
  else
    0

let reveal_poly1305_heap_blocks (h:int) (pad:int) (r:int) (s) (k) =
  ()

let rec lemma_poly1305_heap_hash_blocks_alt h pad r m b n =
  let s = buffer64_as_seq m b in
  let inp = seqTo128 (buffer64_as_seq m b) in
  assert ((2 * n) % 2 == 0); // REVIEW
  reveal_poly1305_heap_blocks h pad r s (n + n);
  if n = 0 then () else (
    lemma_poly1305_heap_hash_blocks_alt h pad r m b (n-1);
    reveal_poly1305_heap_blocks h pad r s (n+n-2);
    ()
  )

// let rec lemma_poly1305_heap_hash_blocks' (h:int) (pad:int) (r:int) (m:mem) (i:int) (len:nat)
//   (k:int{i <= k /\ (k - i) % 16 == 0 /\ k <= i + len /\
//     (forall j . {:pattern (m `Map.contains` j)} i <= j /\ j < i + (len + 15) / 16 * 16 && (j - i) % 8 = 0 ==> m `Map.contains` j)}) :
//   Lemma (requires True)
//         (ensures (poly1305_heap_blocks h pad r m i k == poly1305_hash_blocks h pad r (heapletTo128 m i len) i k))
//   (decreases (k-i)) =
//     let heapb = poly1305_heap_blocks h pad r m i k in
//     let hashb = poly1305_hash_blocks h pad r (heapletTo128 m i len) i k in
//     if i = k then
//       assert(heapb == hashb)
//     else
//       let kk = k - 16 in
//       assert (i >= 0 ==> precedes (kk - i) (k-i));
//       assert (i < 0 ==> precedes (kk - i) (k-i));
//       lemma_poly1305_heap_hash_blocks' h pad r m i len kk

let reveal_modp () =
  FStar.Pervasives.reveal_opaque (`%modp) modp

let reveal_mod2_128 () =
  FStar.Pervasives.reveal_opaque (`%mod2_128) mod2_128
