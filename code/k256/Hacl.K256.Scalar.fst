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
module KL = Hacl.Spec.K256.Scalar.Lemmas

module BD = Hacl.Bignum.Definitions
module BN = Hacl.Bignum
module BB = Hacl.Bignum.Base

module SN = Hacl.Spec.Bignum
module SD = Hacl.Spec.Bignum.Definitions

include Hacl.Spec.K256.Scalar

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

[@CInline]
let bn_add : BN.bn_add_st U64 = BN.bn_add

//inline_for_extraction noextract
//let kn = BN.mk_runtime_bn U64 qnlimb

let add4: BN.bn_add_eq_len_st U64 qnlimb =
  BN.bn_add_eq_len qnlimb

let sub4: BN.bn_sub_eq_len_st U64 qnlimb =
  BN.bn_sub_eq_len qnlimb

let add_mod4: BN.bn_add_mod_n_st U64 qnlimb =
  BN.bn_add_mod_n qnlimb

let sub_mod4: BN.bn_sub_mod_n_st U64 qnlimb =
  BN.bn_sub_mod_n qnlimb

let mul4 (a:BD.lbignum U64 qnlimb) : BN.bn_karatsuba_mul_st U64 qnlimb a =
  BN.bn_mul qnlimb qnlimb a

let sqr4 (a:BD.lbignum U64 qnlimb) : BN.bn_karatsuba_sqr_st U64 qnlimb a =
  BN.bn_sqr qnlimb a

inline_for_extraction noextract
instance kn: BN.bn U64 = {
  BN.len = qnlimb;
  BN.add = add4;
  BN.sub = sub4;
  BN.add_mod_n = add_mod4;
  BN.sub_mod_n = sub_mod4;
  BN.mul = mul4;
  BN.sqr = sqr4
}


let make_u64_4 out (f0, f1, f2, f3) =
  out.(0ul) <- f0;
  out.(1ul) <- f1;
  out.(2ul) <- f2;
  out.(3ul) <- f3;
  let h = ST.get () in
  KL.qas_nat4_is_qas_nat (as_seq h out);
  assert (Seq.equal (as_seq h out) (LSeq.create4 f0 f1 f2 f3))


let make_order_k256 () =
  [@inline_let]
  let r =
   (u64 0xbfd25e8cd0364141,
    u64 0xbaaedce6af48a03b,
    u64 0xfffffffffffffffe,
    u64 0xffffffffffffffff) in

  assert_norm (qas_nat4 r = S.q);
  r


let create_qelem () =
  SD.bn_eval_zeroes #U64 (v qnlimb) (v qnlimb);
  create qnlimb (u64 0)


[@CInline]
let is_qelem_zero f =
  let h0 = ST.get () in
  SN.bn_is_zero_mask_lemma (as_seq h0 f);
  BN.bn_is_zero_mask qnlimb f


[@CInline]
let is_qelem_zero_vartime f =
  let h = ST.get () in
  KL.qas_nat4_is_qas_nat (as_seq h f);

  let (f0,f1,f2,f3) = (f.(0ul), f.(1ul), f.(2ul), f.(3ul)) in
  KL.is_qelem_zero_vartime4_lemma (f0,f1,f2,f3);
  is_qelem_zero_vartime4 (f0,f1,f2,f3)


[@CInline]
let is_qelem_eq_vartime f1 f2 =
  let h = ST.get () in
  KL.qas_nat4_is_qas_nat (as_seq h f1);
  KL.qas_nat4_is_qas_nat (as_seq h f2);

  let (a0,a1,a2,a3) = (f1.(0ul), f1.(1ul), f1.(2ul), f1.(3ul)) in
  let (b0,b1,b2,b3) = (f2.(0ul), f2.(1ul), f2.(2ul), f2.(3ul)) in
  KL.is_qelem_eq_vartime4_lemma (a0,a1,a2,a3) (b0,b1,b2,b3);
  is_qelem_eq_vartime4 (a0,a1,a2,a3) (b0,b1,b2,b3)


[@CInline]
let load_qelem f b =
  let h0 = ST.get () in
  SN.bn_from_bytes_be_lemma #U64 32 (as_seq h0 b);
  BN.bn_from_bytes_be 32ul b f


[@CInline]
let load_qelem_check f b =
  push_frame ();
  let n = create qnlimb (u64 0) in
  make_u64_4 n (make_order_k256 ());
  load_qelem f b;

  let h0 = ST.get () in
  let is_zero = is_qelem_zero f in
  assert (v is_zero == (if qas_nat h0 f = 0 then ones_v U64 else 0));
  let is_lt_q = BN.bn_lt_mask qnlimb f n in
  SN.bn_lt_mask_lemma (as_seq h0 f) (as_seq h0 n);
  assert (v is_lt_q == (if qas_nat h0 f < S.q then ones_v U64 else 0));
  let m = logand (lognot is_zero) is_lt_q in
  lognot_lemma is_zero;
  logand_lemma (lognot is_zero) is_lt_q;
  pop_frame ();
  m


[@CInline]
let load_qelem_vartime f b =
  load_qelem f b;

  let h = ST.get () in
  KL.qas_nat4_is_qas_nat (as_seq h f);
  let is_zero = is_qelem_zero_vartime f in
  let (a0,a1,a2,a3) = (f.(0ul), f.(1ul), f.(2ul), f.(3ul)) in
  let is_lt_q_b = is_qelem_lt_q_vartime4 (a0,a1,a2,a3) in
  KL.is_qelem_lt_q_vartime4_lemma (a0,a1,a2,a3);
  not is_zero && is_lt_q_b


val modq_short: out:qelem -> a:lbuffer uint64 qnlimb -> Stack unit
  (requires fun h ->
    live h a /\ live h out /\ disjoint a out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    qas_nat h1 out == qas_nat h0 a % S.q)

[@CInline]
let modq_short out a =
  push_frame ();
  let tmp = create qnlimb (u64 0) in
  [@inline_let]
  let (t0,t1,t2,t3) = make_pow2_256_minus_order_k256 () in
  make_u64_4 tmp (t0,t1,t2,t3);

  let h0 = ST.get () in
  let c = kn.BN.add a tmp out in
  let mask = u64 0 -. c in
  map2T qnlimb out (BB.mask_select mask) out a;
  KL.mod_short_lseq_lemma (as_seq h0 a);
  pop_frame ()


[@CInline]
let load_qelem_modq f b =
  push_frame ();
  let tmp = create qnlimb (u64 0) in
  load_qelem f b;
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
  kn.BN.add_mod_n n f1 f2 out;
  SN.bn_add_mod_n_lemma (as_seq h0 n) (as_seq h0 f1) (as_seq h0 f2);
  pop_frame ()


val mul_pow2_256_minus_q_add:
    len:size_t
  -> resLen:size_t{2 + v len <= v resLen /\ 4 <= v resLen}
  -> t01:lbuffer uint64 2ul
  -> a:lbuffer uint64 len
  -> e:lbuffer uint64 4ul
  -> res:lbuffer uint64 resLen ->
  Stack (BB.carry U64)
  (requires fun h ->
    live h a /\ live h res /\ live h t01 /\ live h e /\
    disjoint a res /\ disjoint a t01 /\ disjoint a e /\
    disjoint res t01 /\ disjoint res e /\ disjoint t01 e /\
    as_seq h t01 == LSeq.create2 (u64 0x402da1732fc9bebf) (u64 0x4551231950b75fc4) /\
    as_seq h res == LSeq.create (v resLen) (u64 0))
  (ensures  fun h0 c h1 -> modifies (loc res) h0 h1 /\
    (c, as_seq h1 res) ==
      mul_pow2_256_minus_q_lseq_add (v len) (v resLen) (as_seq h0 a) (as_seq h0 e))

[@CInline]
let mul_pow2_256_minus_q_add len resLen t01 a e res =
  push_frame ();
  let tmp = create (len +! 2ul) (u64 0) in
  BN.bn_mul len 2ul a t01 tmp;
  update_sub res 2ul len a;
  let _ = bn_add resLen res (len +! 2ul) tmp res in
  let c = bn_add resLen res 4ul e res in
  pop_frame ();
  c


inline_for_extraction noextract
val modq_before_final:
    t01:lbuffer uint64 2ul
  -> a:lbuffer uint64 (2ul *! qnlimb)
  -> out:qelem ->
  Stack (BB.carry U64)
  (requires fun h ->
    live h a /\ live h out /\ live h t01 /\
    disjoint a out /\ disjoint a t01 /\ disjoint out t01 /\
    as_seq h t01 == LSeq.create2 (u64 0x402da1732fc9bebf) (u64 0x4551231950b75fc4) /\
    as_seq h out == LSeq.create 4 (u64 0))
  (ensures  fun h0 c h1 -> modifies (loc out) h0 h1 /\
    (c, as_seq h1 out) == mod_lseq_before_final (as_seq h0 a))

let modq_before_final t01 a out =
  push_frame ();
  let m = create 7ul (u64 0) in
  let p = create 5ul (u64 0) in
  let c0 = mul_pow2_256_minus_q_add 4ul 7ul t01 (sub a 4ul 4ul) (sub a 0ul 4ul) m in
  let c1 = mul_pow2_256_minus_q_add 3ul 5ul t01 (sub m 4ul 3ul) (sub m 0ul 4ul) p in
  let c2 = mul_pow2_256_minus_q_add 1ul 4ul t01 (sub p 4ul 1ul) (sub p 0ul 4ul) out in
  pop_frame ();
  c2


val modq: out:qelem -> a:lbuffer uint64 (2ul *! qnlimb) -> Stack unit
  (requires fun h ->
    live h a /\ live h out /\ disjoint a out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    qas_nat h1 out == BD.bn_v h0 a % S.q)

[@CInline]
let modq out a =
  push_frame ();
  let r = create qnlimb (u64 0) in
  let tmp = create qnlimb (u64 0) in
  [@inline_let]
  let (t0,t1,t2,t3) = make_pow2_256_minus_order_k256 () in
  make_u64_4 tmp (t0,t1,t2,t3);

  let t01 = sub tmp 0ul 2ul in
  let h0 = ST.get () in
  assert (Seq.equal (as_seq h0 t01) (LSeq.create2 t0 t1));
  let c0 = modq_before_final t01 a r in

  let c1 = kn.BN.add r tmp out in
  let mask = u64 0 -. (c0 +. c1) in
  map2T qnlimb out (BB.mask_select mask) out r;

  let h1 = ST.get () in
  KL.mod_lseq_lemma (as_seq h0 a);
  pop_frame ()


[@CInline]
let qmul out f1 f2 =
  push_frame ();
  let h0 = ST.get () in
  let tmp = create (2ul *! qnlimb) (u64 0) in
  kn.BN.mul f1 f2 tmp;
  SN.bn_mul_lemma (as_seq h0 f1) (as_seq h0 f2);

  modq out tmp;
  pop_frame ()


[@CInline]
let qsqr out f =
  push_frame ();
  let h0 = ST.get () in
  let tmp = create (2ul *! qnlimb) (u64 0) in
  kn.BN.sqr f tmp;
  SN.bn_sqr_lemma (as_seq h0 f);

  modq out tmp;
  pop_frame ()
