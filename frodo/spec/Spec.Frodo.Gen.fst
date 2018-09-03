module Spec.Frodo.Gen

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open Spec.Matrix
open Spec.Frodo.Keccak

module Matrix = Spec.Matrix
module Seq = Lib.Sequence

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val frodo_gen_matrix_cshake_fc:
    n:size_nat{2 * n <= max_size_t /\ 256 + n < maxint U16 /\ n * n <= max_size_t}
  -> seedLen:size_nat
  -> seed:lbytes seedLen
  -> i:size_nat{i < n}
  -> j:size_nat{j < n}
  -> GTot uint16
let frodo_gen_matrix_cshake_fc n seedLen seed i j =
  let res_i = cshake128_frodo seedLen seed (u16 (256 + i)) (2 * n) in
  uint_from_bytes_le (Seq.sub res_i (j * 2) 2)

val frodo_gen_matrix_cshake:
    n:size_nat{2 * n <= max_size_t /\ 256 + n < maxint U16 /\ n * n <= max_size_t}
  -> seedLen:size_nat
  -> seed:lbytes seedLen
  -> res:matrix n n
    {forall (i:size_nat{i < n}) (j:size_nat{j < n}).
     res.(i, j) == frodo_gen_matrix_cshake_fc n seedLen seed i j}
let frodo_gen_matrix_cshake n seedLen seed =
  let res = Matrix.create n n in
  let res = repeati_inductive n
  (fun i res ->
    forall (i0:size_nat{i0 < i}) (j:size_nat{j < n}).
    res.(i0, j) == frodo_gen_matrix_cshake_fc n seedLen seed i0 j)
  (fun i res ->
    let res_i = cshake128_frodo seedLen seed (u16 (256 + i)) (2 * n) in
    repeati_inductive n
    (fun j res0 ->
      (forall (i0:size_nat{i0 < i}) (j:size_nat{j < n}). res0.(i0, j) == res.(i0, j)) /\
      (forall (j0:size_nat{j0 < j}). res0.(i, j0) == frodo_gen_matrix_cshake_fc n seedLen seed i j0))
    (fun j res0 ->
      res0.(i, j) <- uint_from_bytes_le (Seq.sub res_i (j * 2) 2)
    ) res
  ) res in
  res

val lemma_gen_matrix_4x:
     n:size_nat{0 < n /\ 2 * n <= max_size_t /\ 256 + n < maxint U16 /\ n * n <= max_size_t /\ n % 4 = 0}
  -> seedLen:size_nat{seedLen > 0}
  -> seed:lbytes seedLen
  -> res:matrix n n
  -> Lemma
     (requires (forall (i0:size_nat{i0 < n / 4}) (j:size_nat{j < n}) (k:size_nat{k < 4}).
       res.(4 * i0 + k, j) == frodo_gen_matrix_cshake_fc n seedLen seed (4 * i0 + k) j))
     (ensures  (forall (i:size_nat{i < n}) (j:size_nat{j < n}).
       res.(i, j) == frodo_gen_matrix_cshake_fc n seedLen seed i j))
let lemma_gen_matrix_4x n seedLen seed res =
  assert (forall (i0:size_nat{i0 < n / 4}) (j:size_nat{j < n}) (k:size_nat{k < 4}).
    frodo_gen_matrix_cshake_fc n seedLen seed (4 * i0 + k) j == frodo_gen_matrix_cshake_fc n seedLen seed (i0 * 4 + k) j);
  assert (forall (i:size_nat{i < n}) (j:size_nat{j < n}). i == i / 4 * 4 + i % 4 /\ i / 4 < n / 4 /\ i % 4 < 4);
  assert (forall (i:size_nat{i < n}) (j:size_nat{j < n}). res.(i, j) == frodo_gen_matrix_cshake_fc n seedLen seed (i / 4 * 4 + i % 4) j)

val frodo_gen_matrix_cshake_4x:
    n:size_nat{0 < n /\ 2 * n <= max_size_t /\ 256 + n < maxint U16 /\ n * n <= max_size_t /\ n % 4 = 0}
  -> seedLen:size_nat{seedLen > 0}
  -> seed:lbytes seedLen
  -> res:matrix n n{res == frodo_gen_matrix_cshake n seedLen seed}
let frodo_gen_matrix_cshake_4x n seedLen seed =
  let res = Matrix.create n n in
  let n4 = n / 4 in
  let res = repeati_inductive n4
  (fun i res ->
    forall (i0:size_nat{i0 < i}) (j:size_nat{j < n}) (k:size_nat{k < 4}).
    res.(4 * i0 + k, j) == frodo_gen_matrix_cshake_fc n seedLen seed (4 * i0 + k) j)
  (fun i res ->
    let ctr0 = 256 + 4 * i + 0 in
    let ctr1 = 256 + 4 * i + 1 in
    let ctr2 = 256 + 4 * i + 2 in
    let ctr3 = 256 + 4 * i + 3 in
    let r0 = cshake128_frodo seedLen seed (u16 ctr0) (2 * n) in
    let r1 = cshake128_frodo seedLen seed (u16 ctr1) (2 * n) in
    let r2 = cshake128_frodo seedLen seed (u16 ctr2) (2 * n) in
    let r3 = cshake128_frodo seedLen seed (u16 ctr3) (2 * n) in
    let res1 = repeati_inductive n
    (fun j res0 ->
      (forall (i0:size_nat{i0 < i}) (j:size_nat{j < n}) (k:size_nat{k < 4}). res0.(4 * i0 + k, j) == res.(4 * i0 + k, j)) /\
      (forall (j0:size_nat{j0 < j}) (k:size_nat{k < 4}). res0.(4 * i + k, j0) == frodo_gen_matrix_cshake_fc n seedLen seed (4 * i + k) j0))
    (fun j res0 ->
      let res0 = res0.(4 * i + 0, j) <- uint_from_bytes_le (Seq.sub r0 (j * 2) 2) in
      let res0 = res0.(4 * i + 1, j) <- uint_from_bytes_le (Seq.sub r1 (j * 2) 2) in
      let res0 = res0.(4 * i + 2, j) <- uint_from_bytes_le (Seq.sub r2 (j * 2) 2) in
      let res0 = res0.(4 * i + 3, j) <- uint_from_bytes_le (Seq.sub r3 (j * 2) 2) in
      res0
    ) res in
    res1
  ) res in
  assert (forall (i0:size_nat{i0 < n / 4}) (j:size_nat{j < n}) (k:size_nat{k < 4}).
    res.(4 * i0 + k, j) == frodo_gen_matrix_cshake_fc n seedLen seed (4 * i0 + k) j);
  lemma_gen_matrix_4x n seedLen seed res;
  Spec.Matrix.extensionality res (frodo_gen_matrix_cshake n seedLen seed);
  res
