module Spec.Frodo.Sample

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open Spec.Matrix
open Spec.Frodo.Lemmas
open Spec.Frodo.Params

module Seq = Lib.Sequence
module Matrix = Spec.Matrix

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.* +FStar.Pervasives'"

val frodo_sample: r:uint16 -> uint16
let frodo_sample r =
  let open Lib.RawIntTypes in
  let t = r >>. u32 1 in
  let r0 = r &. u16 1 in
  mod_mask_lemma r (u32 1);
  uintv_extensionality (mod_mask (u32 1)) (u16 1);
  assert (uint_v r0 == 0 \/ uint_v r0 == 1);
  let e = 0 in
  let e =
    repeati_inductive
      (cdf_table_len - 1)
      (fun z e -> 0 <= e /\ e <= z /\ z < cdf_table_len)
      (fun z e -> let e = if (uint_to_nat t > uint_to_nat cdf_table.[z]) then e + 1 else e in e)
      e
  in
  let open FStar.Math.Lib in
  let e = (powx (-1) (uint_to_nat r0)) * e in
  assert_norm (powx (-1) 1 == -1);
  assert_norm (powx (-1) 0 == 1);
  assert (-cdf_table_len < e /\ e < cdf_table_len);
  u16 (e % modulus U16)

val frodo_sample_matrix_fc:
    n1:size_nat
  -> n2:size_nat{2 * n1 * n2 < max_size_t}
  -> r:lbytes (2 * n1 * n2)
  -> i:size_nat{i < n1}
  -> j:size_nat{j < n2}
  -> GTot uint16
let frodo_sample_matrix_fc n1 n2 r i j =
  lemma_matrix_index_repeati1 n1 n2 i j;
  frodo_sample (uint_from_bytes_le (Seq.sub r (2 * (n2 * i + j)) 2))

val frodo_sample_matrix:
    n1:size_nat
  -> n2:size_nat{2 * n1 * n2 < max_size_t}
  -> seedLen:size_nat
  -> seed:lbytes seedLen
  -> ctr:uint16
  -> res:matrix n1 n2
    {let r = cshake_frodo seedLen seed ctr (2 * n1 * n2) in
     (forall (i:size_nat{i < n1}) (j:size_nat{j < n2}).
     res.(i, j) == frodo_sample_matrix_fc n1 n2 r i j)}
let frodo_sample_matrix n1 n2 seedLen seed ctr =
  let res = Matrix.create n1 n2 in
  let r = cshake_frodo seedLen seed ctr (2 * n1 * n2) in
  repeati_inductive n1
  (fun i res ->
    forall (i0:size_nat{i0 < i}) (j:size_nat{j < n2}).
    res.(i0, j) == frodo_sample_matrix_fc n1 n2 r i0 j)
  (fun i res ->
    repeati_inductive n2
    (fun j res0 ->
      (forall (i0:size_nat{i0 < i}) (j:size_nat{j < n2}). res0.(i0, j) == res.(i0, j)) /\
      (forall (j0:size_nat{j0 < j}). res0.(i, j0) == frodo_sample_matrix_fc n1 n2 r i j0))
    (fun j res ->
      lemma_matrix_index_repeati1 n1 n2 i j;
      res.(i, j) <- frodo_sample (uint_from_bytes_le (Seq.sub r (2 * (n2 * i + j)) 2))
    ) res
  ) res
