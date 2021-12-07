module Hacl.K256.Scalar

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

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


inline_for_extraction noextract
val make_u64_4 (out:qelem) (f:qelem4) : Stack unit
  (requires fun h -> live h out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    qas_nat h1 out == qas_nat4 f)

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


inline_for_extraction noextract
val make_order_k256: unit -> Pure qelem4
  (requires True)
  (ensures  fun r -> qas_nat4 r = S.q)

let make_order_k256 () =
  [@inline_let]
  let r =
   (u64 0xbfd25e8cd0364141,
    u64 0xbaaedce6af48a03b,
    u64 0xfffffffffffffffe,
    u64 0xffffffffffffffff) in

  assert_norm (qas_nat4 r = S.q);
  r


// needed for Montgomery arithmetic
inline_for_extraction noextract
val make_r2_modq: unit -> Pure qelem4
  (requires True)
  (ensures  fun r -> qas_nat4 r = pow2 512 % S.q)

let make_r2_modq () =
  assert_norm (pow2 512 % S.q = 0x9d671cd581c69bc5e697f5e45bcd07c6741496c20e7cf878896cf21467d7d140);
  [@inline_let]
  let r =
   (u64 0x896cf21467d7d140,
    u64 0x741496c20e7cf878,
    u64 0xe697f5e45bcd07c6,
    u64 0x9d671cd581c69bc5) in

  assert_norm (qas_nat4 r = pow2 512 % S.q);
  r


// needed for Montgomery arithmetic
inline_for_extraction noextract
val make_mu0 : unit -> Pure uint64
  (requires True)
  (ensures  fun mu -> (1 + S.q * v mu) % pow2 64 = 0)

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


val modq_short: out:qelem -> a:lbuffer uint64 qnlimb -> Stack unit
  (requires fun h ->
    live h a /\ live h out /\ eq_or_disjoint a out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    qas_nat h1 out == BD.bn_v h0 a % S.q)

[@CInline]
let modq_short out a =
  push_frame ();
  let tmp = create (2ul *! qnlimb) (u64 0) in
  SD.bn_eval_zeroes #U64 (2 * v qnlimb) (2 * v qnlimb);
  let h0 = ST.get () in
  assert (BD.bn_v h0 tmp = 0);
  update_sub tmp 0ul qnlimb a;
  SD.bn_update_sub_eval (as_seq h0 tmp) (as_seq h0 a) 0;
  let h1 = ST.get () in
  assert (BD.bn_v h1 tmp ==
    BD.bn_v h0 tmp - SD.bn_v (LSeq.sub (as_seq h0 tmp) 0 (v qnlimb)) * pow2 (64 * 0) + BD.bn_v h0 a * pow2 (64 * 0));
  assert_norm (pow2 0 = 1);

  LSeq.eq_intro (LSeq.sub (as_seq h0 tmp) 0 (v qnlimb)) (LSeq.create (v qnlimb) (u64 0));
  SD.bn_eval_zeroes #U64 (v qnlimb) (v qnlimb);
  assert (SD.bn_v (LSeq.sub (as_seq h0 tmp) 0 (v qnlimb)) = 0);
  assert (BD.bn_v h1 tmp == BD.bn_v h0 a);

  modq out tmp;
  pop_frame ()


let create_qelem () =
  SD.bn_eval_zeroes #U64 (v qnlimb) (v qnlimb);
  create qnlimb (u64 0)


[@CInline]
let is_qelem_zero_vartime f =
  let h0 = ST.get () in
  let m = BN.bn_is_zero_mask qnlimb f in
  SN.bn_is_zero_mask_lemma (as_seq h0 f);
  BB.unsafe_bool_of_limb m


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
  let h0 = ST.get () in
  SN.bn_from_bytes_be_lemma #U64 32 (as_seq h0 b);
  BN.bn_from_bytes_be 32ul b f;
  modq_short f f


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


[@CInline]
let qmul out f1 f2 =
  push_frame ();
  let h0 = ST.get () in
  let tmp = create (2ul *! qnlimb) (u64 0) in
  BN.bn_mul qnlimb qnlimb f1 f2 tmp;
  SN.bn_mul_lemma (as_seq h0 f1) (as_seq h0 f2);

  modq out tmp;
  pop_frame ()
