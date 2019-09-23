module Vale.Poly1305.Util

open FStar.Tactics
open FStar.Tactics.Canon
open FStar.Math.Lemmas
open FStar.Math.Lib
open FStar.Mul
open Vale.X64.State   // needed for mem
open Vale.Poly1305.Bitvectors
open Vale.X64.Memory

//#reset-options "--z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3 --z3cliopt smt.arith.nl=false --max_fuel 0 --max_ifuel 0 --smtencoding.elim_box true --eager_inference --smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native"

(* Getting a weird error otherwise, will file an issue
   when this gets merged in fstar branch *)
let poly1305_heap_blocks h pad r s k =
  if 0 <= k && k <= Seq.length s && k % 2 = 0 then
    poly1305_heap_blocks' h pad r s k
  else
    0

let reveal_poly1305_heap_blocks h pad r s k =
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

let rec lemma_equal_blocks h pad r inp1 inp2 k =
  if k > 0 then lemma_equal_blocks h pad r inp1 inp2 (k - 1)

let rec lemma_append_blocks h pad r inp1 inp2 inp k1 k2 =
  if k2 > 0 then lemma_append_blocks h pad r inp1 inp2 inp k1 (k2 - 1) else
  if k1 > 0 then lemma_append_blocks h pad r inp1 inp2 inp (k1 - 1) k2
