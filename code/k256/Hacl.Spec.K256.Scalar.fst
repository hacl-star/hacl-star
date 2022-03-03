module Hacl.Spec.K256.Scalar

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

module SD = Hacl.Spec.Bignum.Definitions
module SB = Hacl.Spec.Bignum
module BB = Hacl.Spec.Bignum.Base

module S = Spec.K256

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let qelem4 = uint64 & uint64 & uint64 & uint64
inline_for_extraction noextract
let qelem_lseq = lseq uint64 4

noextract
let qas_nat4 (f:qelem4) =
  let (f0, f1, f2, f3) = f in
  v f0 + v f1 * pow2 64 + v f2 * pow2 128 + v f3 * pow2 192


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


inline_for_extraction noextract
let is_qelem_zero_vartime4 ((f0,f1,f2,f3): qelem4) : bool =
  let open Lib.RawIntTypes in
  u64_to_UInt64 f0 =. 0uL &&
  u64_to_UInt64 f1 =. 0uL &&
  u64_to_UInt64 f2 =. 0uL &&
  u64_to_UInt64 f3 =. 0uL


inline_for_extraction noextract
let is_qelem_lt_q_vartime4 ((a0,a1,a2,a3): qelem4) : bool =
  let open Lib.RawIntTypes in
  if u64_to_UInt64 a3 <. 0xffffffffffffffffuL then true
  else begin
    if u64_to_UInt64 a2 <. 0xfffffffffffffffeuL then true
    else begin
      if u64_to_UInt64 a2 >. 0xfffffffffffffffeuL then false
      else begin
        if u64_to_UInt64 a1 <. 0xbaaedce6af48a03buL then true
        else begin
          if u64_to_UInt64 a1 >. 0xbaaedce6af48a03buL then false
          else u64_to_UInt64 a0 <. 0xbfd25e8cd0364141uL
        end
      end
    end
  end


inline_for_extraction noextract
let is_qelem_eq_vartime4 ((a0,a1,a2,a3): qelem4) ((b0,b1,b2,b3): qelem4) : bool =
  let open Lib.RawIntTypes in
  u64_to_UInt64 a0 =. u64_to_UInt64 b0 &&
  u64_to_UInt64 a1 =. u64_to_UInt64 b1 &&
  u64_to_UInt64 a2 =. u64_to_UInt64 b2 &&
  u64_to_UInt64 a3 =. u64_to_UInt64 b3


noextract
val mod_short_lseq: a:qelem_lseq -> qelem_lseq
let mod_short_lseq a =
  let (t0,t1,t2,t3) = make_pow2_256_minus_order_k256 () in
  let tmp = create4 t0 t1 t2 t3 in
  let c, out = SB.bn_add a tmp in

  let mask = u64 0 -. c in
  map2 (BB.mask_select mask) out a


noextract
val mul_pow2_256_minus_q_lseq:
  len:size_nat -> resLen:size_nat{2 + len <= resLen}
  -> a:lseq uint64 len -> BB.carry U64 & lseq uint64 resLen

let mul_pow2_256_minus_q_lseq len resLen a =
  let t0 = u64 0x402da1732fc9bebf in
  let t1 = u64 0x4551231950b75fc4 in
  let t01 = create2 t0 t1 in

  // TODO:replace bn_mul with bn_mul1 + bn_mul1_lshift_add?
  let m0 = SB.bn_mul a t01 in // a * t01
  let m1 = create resLen (u64 0) in
  let m1 = update_sub m1 2 len a in // a * t2 * pow2 128
  SB.bn_add m1 m0 // a * SECP256K1_N_C


noextract
val mul_pow2_256_minus_q_lseq_add:
  len:size_nat -> resLen:size_nat{2 + len <= resLen /\ 4 <= resLen}
  -> a:lseq uint64 len -> e:lseq uint64 4 -> BB.carry U64 & lseq uint64 resLen

let mul_pow2_256_minus_q_lseq_add len resLen a e =
  let _, m = mul_pow2_256_minus_q_lseq len resLen a in // a * SECP256K1_N_C
  SB.bn_add m e // e + a * SECP256K1_N_C


noextract
val mod_lseq_before_final: a:lseq uint64 8 -> BB.carry U64 & qelem_lseq
let mod_lseq_before_final a =
  // Reduce 512 bits into 385.
  // m[0..6] = a[0..3] + a[4..7] * SECP256K1_N_C.

  // Reduce 385 bits into 258.
  // p[0..4] = m[0..3] + m[4..6] * SECP256K1_N_C.

  // Reduce 258 bits into 256.
  // c, r[0..3] = p[0..3] + p[4] * SECP256K1_N_C.

  // Final reduction of r.
  // secp256k1_scalar_reduce(r, c + secp256k1_scalar_check_overflow(r));

  // 385 // 64 = 7
  let _, m = mul_pow2_256_minus_q_lseq_add 4 7 (sub a 4 4) (sub a 0 4) in // a[0..3] + a[4..7] * SECP256K1_N_C
  // 258 // 64 = 5
  let _, p = mul_pow2_256_minus_q_lseq_add 3 5 (sub m 4 3) (sub m 0 4) in // m[0..3] + m[4..6] * SECP256K1_N_C
  mul_pow2_256_minus_q_lseq_add 1 4 (sub p 4 1) (sub p 0 4) // p[0..3] + p[4] * SECP256K1_N_C


noextract
val mod_lseq: a:lseq uint64 8 -> qelem_lseq
let mod_lseq a =
  let c0, r = mod_lseq_before_final a in

  [@inline_let]
  let (t0,t1,t2,t3) = make_pow2_256_minus_order_k256 () in
  let tmp = create4 t0 t1 t2 t3 in
  let c1, out = SB.bn_add r tmp in

  let mask = u64 0 -. (c0 +. c1) in
  map2 (BB.mask_select mask) out r
