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
