module Hacl.K256.Field

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

module S = Spec.K256

module BD = Hacl.Bignum.Definitions
module BN = Hacl.Bignum
module BR = Hacl.Bignum.ModReduction
module AM = Hacl.Bignum.AlmostMontgomery
module BI = Hacl.Bignum.ModInv
module BE = Hacl.Bignum.Exponentiation
module BM = Hacl.Bignum.Montgomery

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


let make_prime_k256 () =
  [@inline_let]
  let r =
   (u64 0xfffffffefffffc2f,
    u64 0xffffffffffffffff,
    u64 0xffffffffffffffff,
    u64 0xffffffffffffffff) in

  assert_norm (as_nat4 r = S.prime);
  r


// needed for Montgomery arithmetic
inline_for_extraction noextract
val make_r2_modp: unit -> Pure felem4
  (requires True)
  (ensures  fun r -> as_nat4 r = pow2 512 % S.prime)

let make_r2_modp () =
  assert_norm (pow2 512 % S.prime = 0x1000007a2000e90a1);
  (u64 0x7a2000e90a1, u64 0x1, u64 0x0, u64 0x0)


// needed for Montgomery arithmetic
inline_for_extraction noextract
val make_mu0 : unit -> Pure uint64
  (requires True)
  (ensures  fun mu -> (1 + S.prime * v mu) % pow2 64 = 0)

let make_mu0 () =
  assert_norm ((1 + S.prime * 15580212934572586289) % pow2 64 = 0);
  u64 15580212934572586289


val modp: out:felem -> a:lbuffer uint64 (2ul *! nlimb) -> Stack unit
  (requires fun h ->
    live h a /\ live h out /\ disjoint a out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat h1 out == BD.bn_v h0 a % S.prime)

[@CInline]
let modp out a =
  push_frame ();
  let n = create nlimb (u64 0) in
  make_u64_4 n (make_prime_k256 ());

  let r2 = create 4ul (u64 0) in
  make_u64_4 r2 (make_r2_modp ());

  let mu = make_mu0 () in

  BR.bn_mod_slow_precomp (AM.mk_runtime_almost_mont nlimb) n mu r2 a out;
  pop_frame ()


let create_felem () =
  SD.bn_eval_zeroes #U64 (v nlimb) (v nlimb);
  create nlimb (u64 0)

// not used
let load_felem f b = admit()

// not used
let store_felem b f = admit()


let set_zero f =
  memset f (u64 0) nlimb;
  let h = ST.get () in
  assert (as_seq h f == LSeq.create (v nlimb) (u64 0));
  SD.bn_eval_zeroes #U64 (v nlimb) (v nlimb)


let set_one f =
  BN.bn_from_uint nlimb (u64 1) f;
  SN.bn_from_uint_lemma (v nlimb) (u64 1)

// not used
let copy_felem f1 f2 = admit()


let fmul_small_num out f1 num =
  push_frame ();
  let f2 = create nlimb (u64 0) in
  BN.bn_from_uint nlimb num f2;
  SN.bn_from_uint_lemma (v nlimb) num;

  let h0 = ST.get () in
  let tmp = create (2ul *! nlimb) (u64 0) in
  BN.bn_mul nlimb nlimb f2 f1 tmp;
  SN.bn_mul_lemma (as_seq h0 f2) (as_seq h0 f1);

  modp out tmp;
  pop_frame ()


let fmul_3b out f =
  [@inline_let]
  let b3 = u64 (S.b * 3) in
  fmul_small_num out f b3


let fmul_24b out f =
  [@inline_let]
  let b24 = u64 (S.b * 24) in
  fmul_small_num out f b24


let fadd out f1 f2 =
  push_frame ();
  let n = create nlimb (u64 0) in
  make_u64_4 n (make_prime_k256 ());

  let h0 = ST.get () in
  BN.bn_add_mod_n nlimb n f1 f2 out;
  SN.bn_add_mod_n_lemma (as_seq h0 n) (as_seq h0 f1) (as_seq h0 f2);
  pop_frame ()


let fsub out f1 f2 =
  push_frame ();
  let n = create nlimb (u64 0) in
  make_u64_4 n (make_prime_k256 ());

  let h0 = ST.get () in
  BN.bn_sub_mod_n nlimb n f1 f2 out;
  SN.bn_sub_mod_n_lemma (as_seq h0 n) (as_seq h0 f1) (as_seq h0 f2);
  pop_frame ()


let fmul out f1 f2 =
  push_frame ();
  let h0 = ST.get () in
  let tmp = create (2ul *! nlimb) (u64 0) in
  BN.bn_mul nlimb nlimb f1 f2 tmp;
  SN.bn_mul_lemma (as_seq h0 f1) (as_seq h0 f2);

  modp out tmp;
  pop_frame ()


let fsqr out f =
  push_frame ();
  let h0 = ST.get () in
  let tmp = create (2ul *! nlimb) (u64 0) in
  BN.bn_sqr nlimb f tmp;
  SN.bn_sqr_lemma (as_seq h0 f);

  modp out tmp;
  pop_frame ()


let finv out f =
  push_frame ();
  let n = create nlimb (u64 0) in
  make_u64_4 n (make_prime_k256 ());
  let r2 = create 4ul (u64 0) in
  make_u64_4 r2 (make_r2_modp ());
  let mu = make_mu0 () in
  let n2 = create nlimb (u64 0) in
  BI.bn_mod_inv_prime_n2 nlimb n n2;

  BE.bn_mod_exp_fw_vartime_precomp
    (BM.mk_runtime_mont nlimb) 4ul n mu r2 f 256ul n2 out;
  pop_frame ()
