module Hacl.Impl.K256.Field64

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.Sequence
open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence

module S = Spec.K256
module F64 = Hacl.Spec.K256.Field64
module LF64 = Hacl.Spec.K256.Field64.Lemmas

module BN = Hacl.Bignum
module BD = Hacl.Bignum.Definitions
module SB = Hacl.Spec.Bignum
module SD = Hacl.Spec.Bignum.Definitions

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

noextract
let feval (h:mem) (e:lbuffer uint64 4ul) : GTot S.felem =
  BD.bn_v h e % S.prime


inline_for_extraction noextract
val carry_pass_small_inplace: f:lbuffer uint64 4ul -> cin:uint64 -> Stack unit
  (requires fun h -> live h f)
  (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    as_seq h1 f == F64.carry_pass_small (as_seq h0 f) cin)

let carry_pass_small_inplace f cin =
  let c = BN.bn_add1 4ul f (cin *. u64 0x1000003D1) f in
  f.(0ul) <- f.(0ul) +. c *. u64 0x1000003D1


inline_for_extraction noextract
val carry_pass:
    out:lbuffer uint64 4ul
  -> x_bn:lbuffer uint64 2ul
  -> f:lbuffer uint64 4ul
  -> cin:uint64 ->
  Stack unit
  (requires fun h ->
    live h f /\ live h x_bn /\ live h out /\
    disjoint f x_bn /\ disjoint f out /\ disjoint x_bn out)
  (ensures  fun h0 _ h1 -> modifies (loc x_bn |+| loc out) h0 h1 /\
    as_seq h1 out == F64.carry_pass (as_seq h0 f) cin)

let carry_pass out x_bn f cin =
  let x = mul64_wide cin (u64 0x1000003D1) in
  let x_lo = to_u64 x in
  let x_hi = to_u64 (x >>. 64ul) in
  x_bn.(0ul) <- x_lo;
  x_bn.(1ul) <- x_hi;
  let h1 = ST.get () in
  LSeq.eq_intro (as_seq h1 x_bn) (LSeq.create2 x_lo x_hi);
  assert (as_seq h1 x_bn == LSeq.create2 x_lo x_hi);

  let c = BN.bn_add 4ul f 2ul x_bn out in
  carry_pass_small_inplace out c


val carry_wide: out:lbuffer uint64 4ul -> f:lbuffer uint64 8ul -> Stack unit
  (requires fun h ->
    live h f /\ live h out /\ disjoint f out)
  (ensures  fun h0 _ h1 -> modifies (loc out |+| loc f) h0 h1 /\
    as_seq h1 out == F64.carry_wide (as_seq h0 f))

[@CInline]
let carry_wide out f =
  let c0 = BN.bn_mul1_lshift_add_in_place
    4ul (sub f 4ul 4ul) (u64 0x1000003D1) 4ul 0ul (sub f 0ul 4ul) in
  carry_pass out (sub f 4ul 2ul) (sub f 0ul 4ul) c0


val fmul (out f1 f2: lbuffer uint64 4ul) : Stack unit
  (requires fun h ->
    live h out /\ live h f1 /\ live h f2 /\
    eq_or_disjoint out f1 /\ eq_or_disjoint out f2 /\
    eq_or_disjoint f1 f2)
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    feval h1 out == S.fmul (feval h0 f1) (feval h0 f2))

[@CInline]
let fmul out f1 f2 =
  push_frame ();
  let tmp = create 8ul (u64 0) in
  let h0 = ST.get () in
  BN.bn_mul 4ul 4ul f1 f2 tmp;
  carry_wide out tmp;
  let h1 = ST.get () in
  assert (as_seq h1 out == F64.fmul4 (as_seq h0 f1) (as_seq h0 f2));
  LF64.fmul4_lemma (as_seq h0 f1) (as_seq h0 f2);
  pop_frame ()


val fsqr (out f: lbuffer uint64 4ul) : Stack unit
  (requires fun h ->
    live h out /\ live h f /\ eq_or_disjoint out f)
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    feval h1 out == S.fmul (feval h0 f) (feval h0 f))

[@CInline]
let fsqr out f =
  push_frame ();
  let tmp = create 8ul (u64 0) in
  let h0 = ST.get () in
  BN.bn_sqr 4ul f tmp;
  SB.bn_mul_lemma (as_seq h0 f) (as_seq h0 f);
  SB.bn_sqr_lemma (as_seq h0 f);
  let h1 = ST.get () in
  SD.bn_eval_extensionality_j (as_seq h1 tmp) (SB.bn_sqr (as_seq h0 f)) 8;
  assert (as_seq h1 tmp == SB.bn_sqr (as_seq h0 f));

  carry_wide out tmp;
  let h2 = ST.get () in
  assert (as_seq h2 out == F64.fsqr4 (as_seq h0 f));
  LF64.fsqr4_lemma (as_seq h0 f);
  pop_frame ()
