module Hacl.Spec.FFDHE.Lemmas

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Spec.FFDHE

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"


val ffdhe_p_lemma_len: a:ffdhe_alg -> Lemma
 (let ffdhe_p = get_ffdhe_params a in
  let p = Mk_ffdhe_params?.ffdhe_p ffdhe_p in
  Seq.index p 0 == 0xffuy)

let ffdhe_p_lemma_len a =
  let ffdhe_p = get_ffdhe_params a in
  let p = Mk_ffdhe_params?.ffdhe_p ffdhe_p in

  allow_inversion ffdhe_alg;
  match a with
  | FFDHE2048 ->
    assert (p == of_list list_ffdhe_p2048);
    assert_norm (List.Tot.index list_ffdhe_p2048 0 == 0xffuy);
    assert (Seq.index (Seq.seq_of_list list_ffdhe_p2048) 0 == 0xffuy)
  | FFDHE3072 ->
    assert (p == of_list list_ffdhe_p3072);
    assert_norm (List.Tot.index list_ffdhe_p3072 0 == 0xffuy);
    assert (Seq.index (Seq.seq_of_list list_ffdhe_p3072) 0 == 0xffuy)
  | FFDHE4096 ->
    assert (p == of_list list_ffdhe_p4096);
    assert_norm (List.Tot.index list_ffdhe_p4096 0 == 0xffuy);
    assert (Seq.index (Seq.seq_of_list list_ffdhe_p4096) 0 == 0xffuy)
  | FFDHE6144 ->
    assert (p == of_list list_ffdhe_p6144);
    assert_norm (List.Tot.index list_ffdhe_p6144 0 == 0xffuy);
    assert (Seq.index (Seq.seq_of_list list_ffdhe_p6144) 0 == 0xffuy)
  | FFDHE8192 ->
    assert (p == of_list list_ffdhe_p8192);
    assert_norm (List.Tot.index list_ffdhe_p8192 0 == 0xffuy);
    assert (Seq.index (Seq.seq_of_list list_ffdhe_p8192) 0 == 0xffuy)


// the proof should be somehow simpler
val pow2_lt_len: len:size_pos -> Lemma (pow2 (8 * len - 1) < pow2 (8 * (len - 1)) * (pow2 8 - 1))
let pow2_lt_len len =
  let a = pow2 (8 * len - 1) in
  let b = pow2 (8 * (len - 1)) * (pow2 8 - 1) in
  calc (==) {
    b / a;
    (==) { Math.Lemmas.pow2_plus (8 * len - 8) 7 }
    b / (pow2 (8 * len - 8) * pow2 7);
    (==) { Math.Lemmas.division_multiplication_lemma b (pow2 (8 * len - 8)) (pow2 7) }
    b / pow2 (8 * len - 8) / pow2 7;
    (==) { Math.Lemmas.cancel_mul_div (pow2 8 - 1) (pow2 (8 * len - 8)) }
    (pow2 8 - 1) / pow2 7;
    (==) { Math.Lemmas.pow2_plus 7 1 }
    (pow2 7 * 2 - 1) / pow2 7;
    (==) { }
    1;
    };
  //  assert (b / a * a <= b);
  //  assert (a <= b)

  calc (>) {
    pow2 (8 * len - 8) * (pow2 8 - 1) % pow2 (8 * len - 1);
    (==) { Math.Lemmas.pow2_plus (8 * len - 8) 8 }
    (pow2 (8 * len) - pow2 (8 * len - 8)) % pow2 (8 * len - 1);
    (==) { Math.Lemmas.lemma_mod_plus_distr_l (pow2 (8 * len)) (- pow2 (8 * len - 8)) (pow2 (8 * len - 1)) }
    (pow2 (8 * len) % pow2 (8 * len - 1) - pow2 (8 * len - 8)) % pow2 (8 * len - 1);
    (==) { Math.Lemmas.pow2_multiplication_modulo_lemma_1 1 (8 * len - 1) (8 * len) }
    (0 - pow2 (8 * len - 8)) % pow2 (8 * len - 1);
    //(==) { Math.Lemmas.pow2_lt_compat (8 * len - 1) (8 * len - 8) }
    //pow2 (8 * len - 1) - pow2 (8 * len - 8);
    (>) { Math.Lemmas.pow2_lt_compat (8 * len - 1) (8 * len - 8) }
    0;
    };

  assert (a < b)


val ffdhe_p_bits_lemma: a:ffdhe_alg -> Lemma
 (let ffdhe_p = get_ffdhe_params a in
  let len = ffdhe_len a in
  let p = Mk_ffdhe_params?.ffdhe_p ffdhe_p in
  let p_n = nat_from_bytes_be p in
  pow2 (8 * len - 1) < p_n)

let ffdhe_p_bits_lemma a =
  let ffdhe_p = get_ffdhe_params a in
  let len = ffdhe_len a in
  let p = Mk_ffdhe_params?.ffdhe_p ffdhe_p in
  let p_n = nat_from_bytes_be p in

  nat_from_intseq_be_slice_lemma p 1;
  assert (p_n == nat_from_bytes_be (slice p 1 len) + pow2 (8 * (len - 1)) * nat_from_bytes_be (slice p 0 1));
  nat_from_intseq_be_lemma0 (slice p 0 1);
  assert (p_n == nat_from_bytes_be (slice p 1 len) + pow2 (8 * (len - 1)) * v p.[0]);
  assert (pow2 (8 * (len - 1)) * v p.[0] <= p_n);
  ffdhe_p_lemma_len a;
  assert (pow2 (8 * (len - 1)) * (pow2 8 - 1) <= p_n);
  pow2_lt_len len
