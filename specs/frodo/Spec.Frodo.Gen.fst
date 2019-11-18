module Spec.Frodo.Gen

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open Spec.Matrix
open Spec.SHA3
open Spec.AES

module Matrix = Spec.Matrix
module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators

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

val frodo_gen_matrix_cshake0:
    n:size_nat{2 * n <= max_size_t /\ 256 + n < maxint U16 /\ n * n <= max_size_t}
  -> i:size_nat{i < n}
  -> res_i:lbytes (2 * n)
  -> j:size_nat{j < n}
  -> res0:matrix n n
  -> res1:matrix n n
let frodo_gen_matrix_cshake0 n i res_i j res0 =
    res0.(i, j) <- uint_from_bytes_le (Seq.sub res_i (j * 2) 2)

val frodo_gen_matrix_cshake1:
    n:size_nat{2 * n <= max_size_t /\ 256 + n < maxint U16 /\ n * n <= max_size_t}
  -> seedLen:size_nat
  -> seed:lbytes seedLen
  -> i:size_nat{i < n}
  -> res:matrix n n
  -> res1:matrix n n
let frodo_gen_matrix_cshake1 n seedLen seed i res =
  let res_i = cshake128_frodo seedLen seed (u16 (256 + i)) (2 * n) in
  Loops.repeati_inductive' #(matrix n n) n
  (fun j res0 ->
    (forall (i0:size_nat{i0 < i}) (j:size_nat{j < n}). res0.(i0, j) == res.(i0, j)) /\
    (forall (j0:size_nat{j0 < j}). res0.(i, j0) == frodo_gen_matrix_cshake_fc n seedLen seed i j0))
  (frodo_gen_matrix_cshake0 n i res_i) res

let frodo_gen_matrix_cshake_s (n:size_nat{n * n <= max_size_t}) (i:size_nat{i <= n}) = matrix n n

val frodo_gen_matrix_cshake:
    n:size_nat{2 * n <= max_size_t /\ 256 + n < maxint U16 /\ n * n <= max_size_t}
  -> seedLen:size_nat
  -> seed:lbytes seedLen
  -> res:matrix n n
    {forall (i:size_nat{i < n}) (j:size_nat{j < n}).
     res.(i, j) == frodo_gen_matrix_cshake_fc n seedLen seed i j}
let frodo_gen_matrix_cshake n seedLen seed =
  let res = Matrix.create n n in
  Loops.repeat_gen_inductive n (frodo_gen_matrix_cshake_s n)
  (fun i res ->
    forall (i0:size_nat{i0 < i}) (j:size_nat{j < n}).
    mget #n #n res i0 j == frodo_gen_matrix_cshake_fc n seedLen seed i0 j)
  (frodo_gen_matrix_cshake1 n seedLen seed) res

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

val frodo_gen_matrix_cshake_4x0:
    n:size_nat{2 * n <= max_size_t /\ 256 + n < maxint U16 /\ n * n <= max_size_t}
  -> i:size_nat{i < n / 4}
  -> r0:lbytes (2 * n)
  -> r1:lbytes (2 * n)
  -> r2:lbytes (2 * n)
  -> r3:lbytes (2 * n)
  -> j:size_nat{j < n}
  -> res0:matrix n n
  -> res1:matrix n n
let frodo_gen_matrix_cshake_4x0 n i r0 r1 r2 r3 j res0 =
  let res0 = res0.(4 * i + 0, j) <- uint_from_bytes_le (Seq.sub r0 (j * 2) 2) in
  let res0 = res0.(4 * i + 1, j) <- uint_from_bytes_le (Seq.sub r1 (j * 2) 2) in
  let res0 = res0.(4 * i + 2, j) <- uint_from_bytes_le (Seq.sub r2 (j * 2) 2) in
  let res0 = res0.(4 * i + 3, j) <- uint_from_bytes_le (Seq.sub r3 (j * 2) 2) in
  res0

val frodo_gen_matrix_cshake_4x1:
    n:size_nat{2 * n <= max_size_t /\ 256 + n < maxint U16 /\ n * n <= max_size_t}
  -> seedLen:size_nat
  -> seed:lbytes seedLen
  -> i:size_nat{i < n / 4}
  -> res:matrix n n
  -> res1:matrix n n
let frodo_gen_matrix_cshake_4x1 n seedLen seed i res =
  let ctr0 = 256 + 4 * i + 0 in
  let ctr1 = 256 + 4 * i + 1 in
  let ctr2 = 256 + 4 * i + 2 in
  let ctr3 = 256 + 4 * i + 3 in
  let r0 = cshake128_frodo seedLen seed (u16 ctr0) (2 * n) in
  let r1 = cshake128_frodo seedLen seed (u16 ctr1) (2 * n) in
  let r2 = cshake128_frodo seedLen seed (u16 ctr2) (2 * n) in
  let r3 = cshake128_frodo seedLen seed (u16 ctr3) (2 * n) in
  Loops.repeati_inductive' #(matrix n n) n
  (fun j res0 ->
    (forall (i0:size_nat{i0 < i}) (j:size_nat{j < n}) (k:size_nat{k < 4}).
      res0.(4 * i0 + k, j) == res.(4 * i0 + k, j)) /\
    (forall (j0:size_nat{j0 < j}) (k:size_nat{k < 4}).
      res0.(4 * i + k, j0) == frodo_gen_matrix_cshake_fc n seedLen seed (4 * i + k) j0))
  (frodo_gen_matrix_cshake_4x0 n i r0 r1 r2 r3) res

let frodo_gen_matrix_cshake_4x_s (n:size_nat{n * n <= max_size_t}) (i:size_nat{i <= n / 4}) = matrix n n

val frodo_gen_matrix_cshake_4x:
    n:size_nat{0 < n /\ 2 * n <= max_size_t /\ 256 + n < maxint U16 /\ n * n <= max_size_t /\ n % 4 = 0}
  -> seedLen:size_nat{seedLen > 0}
  -> seed:lbytes seedLen
  -> res:matrix n n{res == frodo_gen_matrix_cshake n seedLen seed}
let frodo_gen_matrix_cshake_4x n seedLen seed =
  let res = Matrix.create n n in
  let n4 = n / 4 in
  let res = Loops.repeat_gen_inductive n4 (frodo_gen_matrix_cshake_4x_s n)
  (fun i res ->
    forall (i0:size_nat{i0 < i}) (j:size_nat{j < n}) (k:size_nat{k < 4}).
    res.(4 * i0 + k, j) == frodo_gen_matrix_cshake_fc n seedLen seed (4 * i0 + k) j)
  (frodo_gen_matrix_cshake_4x1 n seedLen seed) res in
  assert (forall (i0:size_nat{i0 < n / 4}) (j:size_nat{j < n}) (k:size_nat{k < 4}).
    res.(4 * i0 + k, j) == frodo_gen_matrix_cshake_fc n seedLen seed (4 * i0 + k) j);
  lemma_gen_matrix_4x n seedLen seed res;
  Spec.Matrix.extensionality res (frodo_gen_matrix_cshake n seedLen seed);
  res

#set-options "--z3rlimit 150"

val frodo_gen_matrix_cshake_4x_lemma:
    n:size_nat{0 < n /\ 2 * n <= max_size_t /\ 256 + n < maxint U16 /\ n * n <= max_size_t /\ n % 4 = 0}
  -> seedLen:size_nat{seedLen > 0}
  -> seed:lbytes seedLen ->
  Lemma (
    frodo_gen_matrix_cshake_4x n seedLen seed ==
    Loops.repeat_gen (n / 4) (frodo_gen_matrix_cshake_4x_s n)
      (frodo_gen_matrix_cshake_4x1 n seedLen seed) (Matrix.create n n))
let frodo_gen_matrix_cshake_4x_lemma n seedLen seed = ()

val frodo_gen_matrix_aes:
    n:size_nat{n * n <= max_size_t /\ n < maxint U16}
  -> seedLen:size_nat{seedLen == 16}
  -> seed:lbytes seedLen
  -> res:matrix n n
let frodo_gen_matrix_aes n seedLen seed =
  let res = Matrix.create n n in
  let key = aes128_key_expansion seed in
  let tmp = Seq.create 8 (u16 0) in
  let n1 = n / 8 in
  Loops.repeati n
  (fun i res ->
    Loops.repeati n1
    (fun j res ->
      let j = j * 8 in
      let tmp = tmp.[0] <- u16 i in
      let tmp = tmp.[1] <- u16 j in
      let res_i = aes_encrypt_block AES128 key (uints_to_bytes_le tmp) in
      Loops.repeati 8
      (fun k res ->
        res.(i, j + k) <- uint_from_bytes_le (Seq.sub res_i (k * 2) 2)
      ) res
    ) res
  ) res
