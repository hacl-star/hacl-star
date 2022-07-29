module Hacl.Impl.K256.GLV.Constants

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST

module SG = Hacl.Spec.K256.GLV
open Hacl.K256.Field
open Hacl.K256.Scalar

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val make_minus_lambda: f:qelem -> Stack unit
  (requires fun h -> live h f)
  (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    qas_nat h1 f == SG.minus_lambda)

let make_minus_lambda f =
  [@inline_let]
  let x =
   (u64 0xe0cfc810b51283cf,
    u64 0xa880b9fc8ec739c2,
    u64 0x5ad9e3fd77ed9ba4,
    u64 0xac9c52b33fa3cf1f) in

  assert_norm (SG.minus_lambda == qas_nat4 x);
  make_u64_4 f x


inline_for_extraction noextract
val make_beta: f:felem -> Stack unit
  (requires fun h -> live h f)
  (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    as_nat h1 f == SG.beta /\ inv_fully_reduced h1 f)

let make_beta f =
  [@inline_let]
  let x =
   (u64 0x96c28719501ee,
    u64 0x7512f58995c13,
    u64 0xc3434e99cf049,
    u64 0x7106e64479ea,
    u64 0x7ae96a2b657c) in

  assert_norm (0x96c28719501ee <= max52);
  assert_norm (0x7ae96a2b657c <= max48);
  assert_norm (SG.beta == as_nat5 x);
  make_u52_5 f x


inline_for_extraction noextract
val make_minus_b1: f:qelem -> Stack unit
  (requires fun h -> live h f)
  (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    qas_nat h1 f == SG.minus_b1)

let make_minus_b1 f =
  [@inline_let]
  let x =
   (u64 0x6f547fa90abfe4c3,
    u64 0xe4437ed6010e8828,
    u64 0x0,
    u64 0x0) in

  assert_norm (SG.minus_b1 == qas_nat4 x);
  make_u64_4 f x


inline_for_extraction noextract
val make_minus_b2: f:qelem -> Stack unit
  (requires fun h -> live h f)
  (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    qas_nat h1 f == SG.minus_b2)

let make_minus_b2 f =
  [@inline_let]
  let x =
   (u64 0xd765cda83db1562c,
    u64 0x8a280ac50774346d,
    u64 0xfffffffffffffffe,
    u64 0xffffffffffffffff) in

  assert_norm (SG.minus_b2 == qas_nat4 x);
  make_u64_4 f x


inline_for_extraction noextract
val make_g1: f:qelem -> Stack unit
  (requires fun h -> live h f)
  (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    qas_nat h1 f == SG.g1)

let make_g1 f =
  [@inline_let]
  let x =
   (u64 0xe893209a45dbb031,
    u64 0x3daa8a1471e8ca7f,
    u64 0xe86c90e49284eb15,
    u64 0x3086d221a7d46bcd) in

  assert_norm (SG.g1 == qas_nat4 x);
  make_u64_4 f x


inline_for_extraction noextract
val make_g2: f:qelem -> Stack unit
  (requires fun h -> live h f)
  (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    qas_nat h1 f == SG.g2)

let make_g2 f =
  [@inline_let]
  let x =
   (u64 0x1571b4ae8ac47f71,
    u64 0x221208ac9df506c6,
    u64 0x6f547fa90abfe4c4,
    u64 0xe4437ed6010e8828) in

  assert_norm (SG.g2 == qas_nat4 x);
  make_u64_4 f x
