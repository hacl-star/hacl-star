module Spec.Frodo.Sample

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open Spec.Matrix
open Spec.Frodo.Lemmas
open Frodo.Params

module Seq = Lib.Sequence
module Matrix = Spec.Matrix
module Loops = Lib.LoopCombinators

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let cdf_table_len = size_v cdf_table_len

let cdf_table: lseq uint16 cdf_table_len =
  assert_norm (List.Tot.length cdf_list == cdf_table_len);
  Seq.createL cdf_list

val lemma_frodo_sample0: i:size_nat{i < cdf_table_len}
  -> Lemma (uint_v (cdf_table.[i]) < pow2 15)
let lemma_frodo_sample0 i =
  assert_norm (List.Tot.length cdf_list == cdf_table_len);
  lemma_cdf_list i

val lemma_frodo_sample1:
   a:uint16{uint_v a < pow2 15}
 -> b:uint16{uint_v b < pow2 15}
 -> Lemma
     (let c0 = if Lib.RawIntTypes.(uint_to_nat a > uint_to_nat b) then 1 else 0 in
      let c1 = to_u16 (to_u32 (b -. a)) >>. 15ul in
      uint_v c1 == c0)
let lemma_frodo_sample1 a b =
  let c = to_u16 (to_u32 (b -. a)) in
  assert (uint_v c < modulus U16);
  FStar.Math.Lemmas.lemma_div_lt (uint_v c) 16 15;
  let c1 = c >>. 15ul in
  assert (uint_v c1 = uint_v c / pow2 15);
  FStar.Math.Lemmas.pow2_minus 16 15;
  assert (uint_v c1 = 0 \/ uint_v c1 = 1)

val frodo_sample_f:
    t:uint16
  -> i:size_nat{i < cdf_table_len}
  -> res:nat{res = 0 \/ res = 1}
let frodo_sample_f t i =
  let open Lib.RawIntTypes in
  if (uint_to_nat t > uint_to_nat cdf_table.[i])
  then 1 else 0

val frodo_sample_fc:
    t:uint16
  -> i:size_nat{i <= cdf_table_len}
  -> GTot (res:nat{0 <= res /\ res <= i})
    (decreases i)
let rec frodo_sample_fc t i =
  if i = 0 then 0
  else frodo_sample_f t (i - 1) + frodo_sample_fc t (i - 1)

val frodo_sample_res:
    sign:uint16{uint_v sign == 0 \/ uint_v sign == 1}
  -> e:nat{e < cdf_table_len}
  -> uint16
let frodo_sample_res r0 e =
  let open Lib.RawIntTypes in
  let open FStar.Math.Lib in
  let e = (powx (-1) (uint_to_nat r0)) * e in
  assert_norm (powx (-1) 1 == -1);
  assert_norm (powx (-1) 0 == 1);
  assert (-cdf_table_len < e /\ e < cdf_table_len);
  u16 (e % modulus U16)

#set-options "--max_fuel 1"

val frodo_sample: r:uint16 -> uint16
let frodo_sample r =
  let t = r >>. 1ul in
  let r0 = r &. u16 1 in
  mod_mask_lemma r 1ul;
  assert (v #U16 #SEC (mod_mask 1ul) == 1);
  assert (uint_v r0 == 0 \/ uint_v r0 == 1);
  let e =
    Loops.repeati_inductive
      (cdf_table_len - 1)
      (fun z e -> 0 <= e /\ e <= z /\ z < cdf_table_len /\ e == frodo_sample_fc t z)
      (fun z e -> frodo_sample_f t z + e) 0 in
  frodo_sample_res r0 e

#set-options "--max_fuel 0"

val frodo_sample_matrix0:
    n1:size_nat
  -> n2:size_nat{2 * n1 * n2 <= max_size_t}
  -> r:lbytes (2 * n1 * n2)
  -> i:size_nat{i < n1}
  -> j:size_nat{j < n2}
  -> res:matrix n1 n2
  -> matrix n1 n2
let frodo_sample_matrix0 n1 n2 r i j res =
  lemma_matrix_index_repeati1 n1 n2 i j;
  res.(i, j) <- frodo_sample (uint_from_bytes_le (Seq.sub r (2 * (n2 * i + j)) 2))

val frodo_sample_matrix1:
    n1:size_nat
  -> n2:size_nat{2 * n1 * n2 <= max_size_t}
  -> r:lbytes (2 * n1 * n2)
  -> i:size_nat{i < n1}
  -> res:matrix n1 n2
  -> matrix n1 n2
let frodo_sample_matrix1 n1 n2 r i res =
  Loops.repeati n2 (frodo_sample_matrix0 n1 n2 r i) res

val frodo_sample_matrix:
    n1:size_nat
  -> n2:size_nat{2 * n1 * n2 <= max_size_t}
  -> seedLen:size_nat
  -> seed:lbytes seedLen
  -> ctr:uint16
  -> res:matrix n1 n2
let frodo_sample_matrix n1 n2 seedLen seed ctr =
  let res = Matrix.create n1 n2 in
  let r = frodo_prf_spec seedLen seed ctr (2 * n1 * n2) in
  Loops.repeati n1 (frodo_sample_matrix1 n1 n2 r) res
