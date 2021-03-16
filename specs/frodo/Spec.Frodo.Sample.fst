module Spec.Frodo.Sample

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open Spec.Matrix
open Spec.Frodo.Lemmas
open Spec.Frodo.Params

module LSeq = Lib.Sequence
module Matrix = Spec.Matrix
module Loops = Lib.LoopCombinators

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val frodo_sample_f:
    a:frodo_alg
  -> t:uint16
  -> i:size_nat{i < cdf_table_len a}
  -> res:nat{res = 0 \/ res = 1}

let frodo_sample_f a t i =
  if v t > v (cdf_table a).[i] then 1 else 0


val frodo_sample_fc:
    a:frodo_alg
  -> t:uint16
  -> i:size_nat{i <= cdf_table_len a}
  -> GTot (res:nat{0 <= res /\ res <= i})
  (decreases i)

let rec frodo_sample_fc a t i =
  if i = 0 then 0
  else frodo_sample_f a t (i - 1) + frodo_sample_fc a t (i - 1)


val frodo_sample_res:
    a:frodo_alg
  -> sign:uint16{v sign <= 1}
  -> e:nat{e < cdf_table_len a}
  -> uint16

let frodo_sample_res a r0 e =
  let open FStar.Math.Lib in
  let e = (powx (-1) (v r0)) * e in
  assert_norm (powx (-1) 1 == -1);
  assert_norm (powx (-1) 0 == 1);
  assert (-cdf_table_len a < e /\ e < cdf_table_len a);
  u16 (e % modulus U16)


#push-options "--fuel 1"
val frodo_sample: a:frodo_alg -> r:uint16 -> uint16
let frodo_sample a r =
  let t = r >>. 1ul in
  let r0 = r &. u16 1 in
  mod_mask_lemma r 1ul;
  assert (v #U16 #SEC (mod_mask 1ul) == 1);
  assert (v r0 == 0 \/ v r0 == 1);

  let e =
    Loops.repeati_inductive
      (cdf_table_len a - 1)
      (fun z e -> 0 <= e /\ e <= z /\ e == frodo_sample_fc a t z)
      (fun z e -> frodo_sample_f a t z + e) 0 in
  frodo_sample_res a r0 e
#pop-options


// frodo_sample_matrix can be replaced with `creati`
val frodo_sample_matrix0:
    a:frodo_alg
  -> n1:size_nat
  -> n2:size_nat{2 * n1 * n2 <= max_size_t}
  -> r:lbytes (2 * n1 * n2)
  -> i:size_nat{i < n1}
  -> j:size_nat{j < n2}
  -> res:matrix n1 n2
  -> matrix n1 n2

let frodo_sample_matrix0 a n1 n2 r i j res =
  lemma_matrix_index_repeati1 n1 n2 i j;
  res.(i, j) <- frodo_sample a (uint_from_bytes_le (LSeq.sub r (2 * (i * n2 + j)) 2))


val frodo_sample_matrix1:
    a:frodo_alg
  -> n1:size_nat
  -> n2:size_nat{2 * n1 * n2 <= max_size_t}
  -> r:lbytes (2 * n1 * n2)
  -> i:size_nat{i < n1}
  -> res:matrix n1 n2
  -> matrix n1 n2

let frodo_sample_matrix1 a n1 n2 r i res =
  Loops.repeati n2 (frodo_sample_matrix0 a n1 n2 r i) res


val frodo_sample_matrix:
    a:frodo_alg
  -> n1:size_nat
  -> n2:size_nat{2 * n1 * n2 <= max_size_t}
  -> r:lbytes (2 * n1 * n2)
  -> matrix n1 n2

let frodo_sample_matrix a n1 n2 r =
  let res = Matrix.create n1 n2 in
  Loops.repeati n1 (frodo_sample_matrix1 a n1 n2 r) res
