module Spec.Frodo.Gen

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open Spec.Matrix
open Spec.Frodo.Keccak

module Matrix = Spec.Matrix
module Seq = Lib.Sequence

val frodo_gen_matrix_cshake:
    n:size_nat{2 * n < max_size_t /\ 256 + n < maxint U16 /\ n * n < max_size_t}
  -> seedLen:size_nat
  -> seed:lbytes seedLen
  -> matrix n n
let frodo_gen_matrix_cshake n seedLen seed =
  let res = Matrix.create n n in
  repeati n
  (fun i res ->
    let res_i = cshake128_frodo seedLen seed (u16 (256 + i)) (2 * n) in
    repeati n
    (fun j res ->
      res.(i, j) <- uint_from_bytes_le (Seq.sub res_i (j * 2) 2)
    ) res
  ) res
