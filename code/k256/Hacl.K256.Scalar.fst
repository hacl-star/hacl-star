module Hacl.K256.Scalar

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

module S = Spec.K256
module F = Hacl.K256.Field

module BD = Hacl.Bignum.Definitions
module BN = Hacl.Bignum
module BR = Hacl.Bignum.ModReduction
module AM = Hacl.Bignum.AlmostMontgomery
module BB = Hacl.Bignum.Base

module SN = Hacl.Spec.Bignum
module SD = Hacl.Spec.Bignum.Definitions


#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(**
  This is a naive implementation of field arithmetic for testing purposes
*)


let make_u64_4 out (f0, f1, f2, f3) =
  out.(0ul) <- f0;
  out.(1ul) <- f1;
  out.(2ul) <- f2;
  out.(3ul) <- f3;
  let h = ST.get () in
  SD.bn_eval_unfold_i (as_seq h out) 4;
  SD.bn_eval_unfold_i (as_seq h out) 3;
  SD.bn_eval_unfold_i (as_seq h out) 2;
  SD.bn_eval_unfold_i (as_seq h out) 1;
  SD.bn_eval0 (as_seq h out)


let make_order_k256 () =
  [@inline_let]
  let r =
   (u64 0xbfd25e8cd0364141,
    u64 0xbaaedce6af48a03b,
    u64 0xfffffffffffffffe,
    u64 0xffffffffffffffff) in

  assert_norm (qas_nat4 r = S.q);
  r


inline_for_extraction noextract
val make_pow2_256_minus_order_k256: unit -> Pure qelem4
  (requires True)
  (ensures  fun r -> qas_nat4 r = pow2 256 - S.q)

let make_pow2_256_minus_order_k256 () =
  [@inline_let]
  let r =
   (u64 0x402da1732fc9bebf,
    u64 0x4551231950b75fc4,
    u64 0x1,
    u64 0x0) in

  assert_norm (qas_nat4 r = pow2 256 - S.q);
  r


val lemma_check_overflow: b:nat{b < pow2 256} ->
  Lemma (let overflow = (b + (pow2 256 - S.q)) / pow2 256 in
    overflow = (if b < S.q then 0 else 1))

let lemma_check_overflow b =
  let overflow = (b + (pow2 256 - S.q)) / pow2 256 in
  if b < S.q then begin
    assert (pow2 256 + b - S.q < pow2 256);
    assert (pow2 256 - S.q <= pow2 256 + b - S.q);
    assert_norm (0 < pow2 256 - S.q);
    Math.Lemmas.small_div (pow2 256 + b - S.q) (pow2 256);
    assert (overflow = 0) end
  else begin
    assert (pow2 256 <= pow2 256 + b - S.q);
    Math.Lemmas.lemma_div_le (pow2 256) (pow2 256 + b - S.q) (pow2 256);
    Math.Lemmas.cancel_mul_div 1 (pow2 256);
    assert (1 <= overflow);

    assert (pow2 256 + b - S.q < pow2 256 + pow2 256 - S.q);
    assert (pow2 256 + b - S.q <= pow2 256 + pow2 256 - S.q - 1);
    Math.Lemmas.lemma_div_le (pow2 256 + b - S.q) (pow2 256 + pow2 256 - S.q - 1) (pow2 256);
    assert_norm ((pow2 256 + pow2 256 - S.q - 1) / pow2 256 = 1);
    assert (overflow <= 1) end


val lemma_get_carry_from_bn_add: r:nat{r < pow2 256} -> c:nat ->
  Lemma ((r + c * pow2 256) / pow2 256 = c)

let lemma_get_carry_from_bn_add r c =
  Math.Lemmas.lemma_div_plus r c (pow2 256);
  Math.Lemmas.small_div r (pow2 256)


val modq_short: out:qelem -> a:lbuffer uint64 qnlimb -> Stack unit
  (requires fun h ->
    live h a /\ live h out /\ disjoint a out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    qas_nat h1 out == qas_nat h0 a % S.q)

[@CInline]
let modq_short out a =
  push_frame ();
  let tmp = create qnlimb (u64 0) in
  make_u64_4 tmp (make_pow2_256_minus_order_k256 ());
  let h0 = ST.get () in
  let c = BN.bn_add_eq_len qnlimb a tmp out in
  let h1 = ST.get () in
  SN.bn_add_lemma (as_seq h0 a) (as_seq h0 tmp);
  assert (v c * pow2 256 + qas_nat h1 out = qas_nat h0 a + qas_nat h0 tmp);
  assert (qas_nat h0 tmp == pow2 256 - S.q);

  [@inline_let]
  let mask = u64 0 -. c in
  buf_mask_select out a mask out;
  let h2 = ST.get () in
  assert (v mask = (if v c = 0 then 0 else ones_v U64));
  assert (as_seq h2 out == (if v c = 0 then as_seq h0 a else as_seq h1 out));

  SD.bn_eval_bound (as_seq h0 a) (v qnlimb);
  SD.bn_eval_bound (as_seq h1 out) (v qnlimb);
  lemma_check_overflow (qas_nat h0 a);
  lemma_get_carry_from_bn_add (qas_nat h1 out) (v c);
  assert (v c = (if qas_nat h0 a < S.q then 0 else 1));

  if qas_nat h0 a < S.q then begin
    assert (qas_nat h2 out == qas_nat h0 a);
    Math.Lemmas.small_mod (qas_nat h0 a) S.q end
  else begin
    assert (qas_nat h2 out == qas_nat h0 a + (pow2 256 - S.q) - pow2 256);
    Math.Lemmas.lemma_mod_sub (qas_nat h0 a) S.q 1;
    assert (qas_nat h2 out % S.q == qas_nat h0 a % S.q);
    Math.Lemmas.small_mod (qas_nat h2 out) S.q end;
  pop_frame ()


let create_qelem () =
  SD.bn_eval_zeroes #U64 (v qnlimb) (v qnlimb);
  create qnlimb (u64 0)


(* TODO: make bn_is_zero vartime *)
[@CInline]
let is_qelem_zero_vartime f =
  let h0 = ST.get () in
  let m = BN.bn_is_zero_mask qnlimb f in
  SN.bn_is_zero_mask_lemma (as_seq h0 f);
  BB.unsafe_bool_of_limb m


(* TODO: make is_qelem_eq vartime *)
[@CInline]
let is_qelem_eq_vartime f1 f2 =
  let h0 = ST.get () in
  let m = BN.bn_eq_mask qnlimb f1 f2 in
  SN.bn_eq_mask_lemma (as_seq h0 f1) (as_seq h0 f2);
  BB.unsafe_bool_of_limb m


[@CInline]
let load_qelem f b =
  let h0 = ST.get () in
  SN.bn_from_bytes_be_lemma #U64 32 (as_seq h0 b);
  BN.bn_from_bytes_be 32ul b f


(* TODO: make bn_lt_mask vartime *)
[@CInline]
let load_qelem_vartime f b =
  push_frame ();
  let n = create qnlimb (u64 0) in
  make_u64_4 n (make_order_k256 ());

  let h0 = ST.get () in
  SN.bn_from_bytes_be_lemma #U64 32 (as_seq h0 b);
  BN.bn_from_bytes_be 32ul b f;
  let h1 = ST.get () in

  let is_zero = is_qelem_zero_vartime f in
  let is_lt_q = BN.bn_lt_mask qnlimb f n in
  SN.bn_lt_mask_lemma (as_seq h1 f) (as_seq h1 n);
  let is_lt_q_b = BB.unsafe_bool_of_limb is_lt_q in
  pop_frame ();
  not is_zero && is_lt_q_b


[@CInline]
let load_qelem_modq f b =
  push_frame ();
  let tmp = create qnlimb (u64 0) in
  let h0 = ST.get () in
  SN.bn_from_bytes_be_lemma #U64 32 (as_seq h0 b);
  BN.bn_from_bytes_be 32ul b f;
  copy tmp f;
  modq_short f tmp;
  pop_frame ()


[@CInline]
let store_qelem b f =
  let h0 = ST.get () in
  SN.bn_to_bytes_be_lemma #U64 32 (as_seq h0 f);
  BN.bn_to_bytes_be 32ul f b


[@CInline]
let qadd out f1 f2 =
  push_frame ();
  let n = create qnlimb (u64 0) in
  make_u64_4 n (make_order_k256 ());

  let h0 = ST.get () in
  BN.bn_add_mod_n qnlimb n f1 f2 out;
  SN.bn_add_mod_n_lemma (as_seq h0 n) (as_seq h0 f1) (as_seq h0 f2);
  pop_frame ()


(* TODO: check whether barrett reduction is more efficient than montgomery one *)

let make_r2_modq () =
  [@inline_let]
  let r =
   (u64 0x896cf21467d7d140,
    u64 0x741496c20e7cf878,
    u64 0xe697f5e45bcd07c6,
    u64 0x9d671cd581c69bc5) in

  assert_norm (qas_nat4 r = pow2 512 % S.q);
  r


let make_mu0 () =
  assert_norm ((1 + S.q * 5408259542528602431) % pow2 64 = 0);
  u64 5408259542528602431


val modq: out:qelem -> a:lbuffer uint64 (2ul *! qnlimb) -> Stack unit
  (requires fun h ->
    live h a /\ live h out /\ disjoint a out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    qas_nat h1 out == BD.bn_v h0 a % S.q)

[@CInline]
let modq out a =
  push_frame ();
  let n = create qnlimb (u64 0) in
  make_u64_4 n (make_order_k256 ());

  let r2 = create 4ul (u64 0) in
  make_u64_4 r2 (make_r2_modq ());

  let mu = make_mu0 () in

  BR.bn_mod_slow_precomp (AM.mk_runtime_almost_mont qnlimb) n mu r2 a out;
  pop_frame ()


[@CInline]
let qmul out f1 f2 =
  push_frame ();
  let h0 = ST.get () in
  let tmp = create (2ul *! qnlimb) (u64 0) in
  BN.bn_mul qnlimb qnlimb f1 f2 tmp;
  SN.bn_mul_lemma (as_seq h0 f1) (as_seq h0 f2);

  modq out tmp;
  pop_frame ()
