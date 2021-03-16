module Spec.Frodo.Gen

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open Spec.Matrix
open Spec.SHA3
open Spec.AES

module Matrix = Spec.Matrix
module LSeq = Lib.Sequence
module Loops = Lib.LoopCombinators

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val frodo_gen_matrix_shake_get_r:
    n:size_nat{n * n <= max_size_t /\ n <= maxint U16}
  -> seed:lbytes 16
  -> i:size_nat{i < n}
  -> lbytes (2 * n)

let frodo_gen_matrix_shake_get_r n seed i =
  let tmp = uint_to_bytes_le (u16 i) in
  let b = concat tmp seed in
  shake128 18 b (2 * n)


val frodo_gen_matrix_shake0:
    n:size_nat{n * n <= max_size_t}
  -> i:size_nat{i < n}
  -> res_i:lbytes (2 * n)
  -> j:size_nat{j < n}
  -> res0:matrix n n
  -> matrix n n

let frodo_gen_matrix_shake0 n i res_i j res0 =
  res0.(i, j) <- uint_from_bytes_le (LSeq.sub res_i (j * 2) 2)


val frodo_gen_matrix_shake1:
    n:size_nat{n * n <= max_size_t /\ n <= maxint U16}
  -> seed:lbytes 16
  -> i:size_nat{i < n}
  -> res:matrix n n
  -> matrix n n

let frodo_gen_matrix_shake1 n seed i res =
  let res_i = frodo_gen_matrix_shake_get_r n seed i in
  Loops.repeati n (frodo_gen_matrix_shake0 n i res_i) res


val frodo_gen_matrix_shake:
    n:size_nat{n * n <= max_size_t /\ n <= maxint U16}
  -> seed:lbytes 16
  -> matrix n n

let frodo_gen_matrix_shake n seed =
  let res = Matrix.create n n in
  Loops.repeati n (frodo_gen_matrix_shake1 n seed) res


val frodo_gen_matrix_shake_4x0:
    n:size_nat{n * n <= max_size_t /\ n <= maxint U16}
  -> i:size_nat{i < n / 4}
  -> r0:lbytes (2 * n)
  -> r1:lbytes (2 * n)
  -> r2:lbytes (2 * n)
  -> r3:lbytes (2 * n)
  -> j:size_nat{j < n}
  -> res0:matrix n n
  -> matrix n n

let frodo_gen_matrix_shake_4x0 n i r0 r1 r2 r3 j res0 =
  let res0 = res0.(4 * i + 0, j) <- uint_from_bytes_le (LSeq.sub r0 (j * 2) 2) in
  let res0 = res0.(4 * i + 1, j) <- uint_from_bytes_le (LSeq.sub r1 (j * 2) 2) in
  let res0 = res0.(4 * i + 2, j) <- uint_from_bytes_le (LSeq.sub r2 (j * 2) 2) in
  let res0 = res0.(4 * i + 3, j) <- uint_from_bytes_le (LSeq.sub r3 (j * 2) 2) in
  res0


val frodo_gen_matrix_shake_4x1_get_r:
    n:size_nat{n * n <= max_size_t /\ n <= maxint U16}
  -> seed:lbytes 16
  -> i:size_nat{i < n / 4}
  -> lbytes (2 * n) & lbytes (2 * n) & lbytes (2 * n) & lbytes (2 * n)

let frodo_gen_matrix_shake_4x1_get_r n seed i =
  let t0 = uint_to_bytes_le (u16 (4 * i + 0)) in
  let t1 = uint_to_bytes_le (u16 (4 * i + 1)) in
  let t2 = uint_to_bytes_le (u16 (4 * i + 2)) in
  let t3 = uint_to_bytes_le (u16 (4 * i + 3)) in

  let b0 = concat t0 seed in
  let b1 = concat t1 seed in
  let b2 = concat t2 seed in
  let b3 = concat t3 seed in

  let r0 = shake128 18 b0 (2 * n) in
  let r1 = shake128 18 b1 (2 * n) in
  let r2 = shake128 18 b2 (2 * n) in
  let r3 = shake128 18 b3 (2 * n) in
  r0, r1, r2, r3


val frodo_gen_matrix_shake_4x1:
    n:size_nat{n * n <= max_size_t /\ n <= maxint U16}
  -> seed:lbytes 16
  -> i:size_nat{i < n / 4}
  -> res:matrix n n
  -> matrix n n

let frodo_gen_matrix_shake_4x1 n seed i res =
  let r0, r1, r2, r3 = frodo_gen_matrix_shake_4x1_get_r n seed i in
  Loops.repeati n (frodo_gen_matrix_shake_4x0 n i r0 r1 r2 r3) res


val frodo_gen_matrix_shake_4x:
    n:size_nat{n * n <= max_size_t /\ n <= maxint U16 /\ n % 4 = 0}
  -> seed:lbytes 16
  -> matrix n n

let frodo_gen_matrix_shake_4x n seed =
  let res = Matrix.create n n in
  let n4 = n / 4 in
  Loops.repeati n4 (frodo_gen_matrix_shake_4x1 n seed) res


val frodo_gen_matrix_aes:
    n:size_nat{n * n <= max_size_t /\ n <= maxint U16}
  -> seed:lbytes 16
  -> matrix n n

let frodo_gen_matrix_aes n seed =
  let res = Matrix.create n n in
  let key = aes128_key_expansion seed in
  let tmp = LSeq.create 8 (u16 0) in
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
        res.(i, j + k) <- uint_from_bytes_le (LSeq.sub res_i (k * 2) 2)
      ) res
    ) res
  ) res


(** Lemma (frodo_gen_matrix_shake == frodo_gen_matrix_shake_4x) *)

val frodo_gen_matrix_shake_fc:
    n:size_nat{n * n <= max_size_t /\ n <= maxint U16}
  -> seed:lbytes 16
  -> i:size_nat{i < n}
  -> j:size_nat{j < n}
  -> GTot uint16

let frodo_gen_matrix_shake_fc n seed i j =
  let res_i = frodo_gen_matrix_shake_get_r n seed i in
  uint_from_bytes_le (LSeq.sub res_i (j * 2) 2)


val frodo_gen_matrix_shake1_ind:
    n:size_nat{n * n <= max_size_t /\ n <= maxint U16}
  -> seed:lbytes 16
  -> i:size_nat{i < n}
  -> res:matrix n n
  -> Pure (matrix n n)
    (requires True)
    (ensures  fun res1 ->
      let res_i = frodo_gen_matrix_shake_get_r n seed i in
      res1 == Loops.repeati n (frodo_gen_matrix_shake0 n i res_i) res)

let frodo_gen_matrix_shake1_ind n seed i res =
  let res_i = frodo_gen_matrix_shake_get_r n seed i in
  //Loops.repeati n (frodo_gen_matrix_shake0 n i res_i) res

  Loops.repeati_inductive' #(matrix n n) n
  (fun j res0 ->
    (forall (i0:size_nat{i0 < i}) (j:size_nat{j < n}). res0.(i0, j) == res.(i0, j)) /\
    (forall (j0:size_nat{j0 < j}). res0.(i, j0) == frodo_gen_matrix_shake_fc n seed i j0))
  (frodo_gen_matrix_shake0 n i res_i) res


val frodo_gen_matrix_shake_ind:
    n:size_nat{n * n <= max_size_t /\ n <= maxint U16}
  -> seed:lbytes 16
  -> Pure (matrix n n)
    (requires True)
    (ensures  fun res ->
      res == Loops.repeati n (frodo_gen_matrix_shake1_ind n seed) (Matrix.create n n) /\
      (forall (i:size_nat{i < n}) (j:size_nat{j < n}).
      res.(i, j) == frodo_gen_matrix_shake_fc n seed i j))

let frodo_gen_matrix_shake_ind n seed =
  let res = Matrix.create n n in
  //Loops.repeati n (frodo_gen_matrix_shake1 n seed) res

  Loops.repeati_inductive' #(matrix n n) n
  (fun i res ->
    forall (i0:size_nat{i0 < i}) (j:size_nat{j < n}).
      res.(i0, j) == frodo_gen_matrix_shake_fc n seed i0 j)
  (frodo_gen_matrix_shake1_ind n seed) res


val frodo_gen_matrix_shake_4x1_ind:
    n:size_nat{n * n <= max_size_t /\ n <= maxint U16}
  -> seed:lbytes 16
  -> i:size_nat{i < n / 4}
  -> res:matrix n n
  -> Pure (matrix n n)
    (requires True)
    (ensures  fun res1 ->
      let r0, r1, r2, r3 = frodo_gen_matrix_shake_4x1_get_r n seed i in
      res1 == Loops.repeati n (frodo_gen_matrix_shake_4x0 n i r0 r1 r2 r3) res)

let frodo_gen_matrix_shake_4x1_ind n seed i res =
  let r0, r1, r2, r3 = frodo_gen_matrix_shake_4x1_get_r n seed i in
  //Loops.repeati n (frodo_gen_matrix_shake_4x0 n i r0 r1 r2 r3) res
  Loops.repeati_inductive' #(matrix n n) n
  (fun j res0 ->
    (forall (i0:size_nat{i0 < i}) (j:size_nat{j < n}) (k:size_nat{k < 4}).
      res0.(4 * i0 + k, j) == res.(4 * i0 + k, j)) /\
    (forall (j0:size_nat{j0 < j}) (k:size_nat{k < 4}).
      res0.(4 * i + k, j0) == frodo_gen_matrix_shake_fc n seed (4 * i + k) j0))
  (frodo_gen_matrix_shake_4x0 n i r0 r1 r2 r3) res


val lemma_gen_matrix_4x:
    n:size_nat{n * n <= max_size_t /\ n <= maxint U16 /\ n % 4 = 0}
  -> seed:lbytes 16
  -> res:matrix n n
  -> Lemma
    (requires (forall (i0:size_nat{i0 < n / 4}) (j:size_nat{j < n}) (k:size_nat{k < 4}).
      res.(4 * i0 + k, j) == frodo_gen_matrix_shake_fc n seed (4 * i0 + k) j))
    (ensures  (forall (i:size_nat{i < n}) (j:size_nat{j < n}).
      res.(i, j) == frodo_gen_matrix_shake_fc n seed i j))

let lemma_gen_matrix_4x n seed res =
  assert (forall (i0:size_nat{i0 < n / 4}) (j:size_nat{j < n}) (k:size_nat{k < 4}).
    frodo_gen_matrix_shake_fc n seed (4 * i0 + k) j == frodo_gen_matrix_shake_fc n seed (i0 * 4 + k) j);
  assert (forall (i:size_nat{i < n}) (j:size_nat{j < n}). i == i / 4 * 4 + i % 4 /\ i / 4 < n / 4 /\ i % 4 < 4);
  assert (forall (i:size_nat{i < n}) (j:size_nat{j < n}). res.(i, j) == frodo_gen_matrix_shake_fc n seed (i / 4 * 4 + i % 4) j)


val frodo_gen_matrix_shake_4x_ind:
    n:size_nat{n * n <= max_size_t /\ n <= maxint U16 /\ n % 4 = 0}
  -> seed:lbytes 16
  -> Pure (matrix n n)
    (requires True)
    (ensures  fun res ->
      res == Loops.repeati (n / 4) (frodo_gen_matrix_shake_4x1_ind n seed) (Matrix.create n n) /\
      res == frodo_gen_matrix_shake_ind n seed)

let frodo_gen_matrix_shake_4x_ind n seed =
  let res = Matrix.create n n in
  let n4 = n / 4 in
  //Loops.repeati n4 (frodo_gen_matrix_shake_4x1 n seed) res

  let res =
  Loops.repeati_inductive' n4
  (fun i res ->
    forall (i0:size_nat{i0 < i}) (j:size_nat{j < n}) (k:size_nat{k < 4}).
      res.(4 * i0 + k, j) == frodo_gen_matrix_shake_fc n seed (4 * i0 + k) j)
  (frodo_gen_matrix_shake_4x1_ind n seed) res in
  //assert (forall (i0:size_nat{i0 < n / 4}) (j:size_nat{j < n}) (k:size_nat{k < 4}).
    //res.(4 * i0 + k, j) == frodo_gen_matrix_shake_fc n seed (4 * i0 + k) j);
  lemma_gen_matrix_4x n seed res;
  Spec.Matrix.extensionality res (frodo_gen_matrix_shake_ind n seed);
  res


val frodo_gen_matrix_shake_4x_lemma:
    n:size_nat{n * n <= max_size_t /\ n <= maxint U16 /\ n % 4 = 0}
  -> seed:lbytes 16 -> Lemma
    (frodo_gen_matrix_shake_4x n seed == frodo_gen_matrix_shake n seed)

let frodo_gen_matrix_shake_4x_lemma n seed =
  let res = Matrix.create n n in
  let r_4x = frodo_gen_matrix_shake_4x n seed in
  let r = frodo_gen_matrix_shake n seed in
  let r_ind_4x = frodo_gen_matrix_shake_4x_ind n seed in
  let r_ind = frodo_gen_matrix_shake_ind n seed in

  assert (r_ind_4x == r_ind);
  assert (r_ind == Loops.repeati n (frodo_gen_matrix_shake1_ind n seed) res);
  assert (r_ind_4x == Loops.repeati (n / 4) (frodo_gen_matrix_shake_4x1_ind n seed) res);

  let aux_r (i:nat{i < n}) (acc:matrix n n) :
    Lemma (frodo_gen_matrix_shake1_ind n seed i acc == frodo_gen_matrix_shake1 n seed i acc) = () in

  Classical.forall_intro_2 aux_r;
  Lib.Sequence.Lemmas.repeati_extensionality n
    (frodo_gen_matrix_shake1_ind n seed) (frodo_gen_matrix_shake1 n seed) res;
  assert (r_ind == frodo_gen_matrix_shake n seed);

  let aux_r_4x (i:nat{i < n / 4}) (acc:matrix n n) :
    Lemma (frodo_gen_matrix_shake_4x1_ind n seed i acc == frodo_gen_matrix_shake_4x1 n seed i acc) = () in

  Classical.forall_intro_2 aux_r_4x;
  Lib.Sequence.Lemmas.repeati_extensionality (n / 4)
    (frodo_gen_matrix_shake_4x1_ind n seed) (frodo_gen_matrix_shake_4x1 n seed) res;
  assert (r_ind_4x == frodo_gen_matrix_shake_4x n seed);
  assert (r_4x == r)
