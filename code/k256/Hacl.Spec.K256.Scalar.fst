module Hacl.Spec.K256.Scalar

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

module BSeq = Lib.ByteSequence

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
let is_qelem_le_q_halved_vartime4 ((a0,a1,a2,a3): qelem4) : bool =
  let open Lib.RawIntTypes in
  if u64_to_UInt64 a3 <. 0x7fffffffffffffffuL then true
  else begin
    if u64_to_UInt64 a3 >. 0x7fffffffffffffffuL then false
    else begin
      if u64_to_UInt64 a2 <. 0xffffffffffffffffuL then true
      else begin
        if u64_to_UInt64 a2 >. 0xffffffffffffffffuL then false
        else begin
          if u64_to_UInt64 a1 <. 0x5d576e7357a4501duL then true
          else begin
            if u64_to_UInt64 a1 >. 0x5d576e7357a4501duL then false
            else u64_to_UInt64 a0 <=. 0xdfe92f46681b20a0uL
          end
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

  let (t0,t1,t2,t3) = make_pow2_256_minus_order_k256 () in
  let tmp = create4 t0 t1 t2 t3 in
  let c1, out = SB.bn_add r tmp in

  let mask = u64 0 -. (c0 +. c1) in
  map2 (BB.mask_select mask) out r


noextract
let qmul_shift_384 (a b:qelem_lseq) : qelem_lseq =
  let l = SB.bn_mul a b in
  let res_b = SB.bn_rshift l 6 in
  let res_b_padded = create 4 (u64 0) in
  let res_b_padded = update_sub res_b_padded 0 2 res_b in
  let _, res1_b = SB.bn_add1 res_b_padded (u64 1) in

  let flag = l.[5] >>. 63ul in
  let mask = u64 0 -. flag in // mask = if flag is set then ones_v U64 else 0
  map2 (BB.mask_select mask) res1_b res_b_padded // res = if flag is set then res1_b else res_b


// val shiftlow_lemma: shift:size_t -> Lemma (v (shift &. 0x3ful) = v shift % pow2 6)
// let shiftlow_lemma shift =
//   let shiftlow = shift &. 0x3ful in
//   assert_norm (0x3f = pow2 6 - 1);
//   mod_mask_lemma shift 6ul;
//   assert (v (mod_mask #U32 #PUB 6ul) == v (0x3ful));
//   assert (v shiftlow = v shift % pow2 6)


// (* https://github.com/bitcoin-core/secp256k1/blob/master/src/scalar_4x64_impl.h *)
// noextract
// let qmul_shift (a b:qelem_lseq) (shift:size_t{256 <= v shift /\ v shift <= 512}) : qelem_lseq =
//   let l = SB.bn_mul a b in
//   let shiftlimbs = shift >>. 6ul in
//   assert (v shiftlimbs = v shift / pow2 6);

//   let shiftlow = shift &. 0x3ful in
//   shiftlow_lemma shift;
//   assert (v shiftlow = v shift % pow2 6);
//   assert_norm (pow2 6 = 64);
//   assert (v shiftlow < 64);

//   let shifthigh = 64ul -. shiftlow in
//   assert (if 0 < v shiftlow then v shifthigh < 64 else v shifthigh <= 64);

//   let r0 =
//     if shift <. 512ul then begin
//       let tmp =
//         if shift <. 448ul && shiftlow >. 0ul then begin
//           assume (1 + v shiftlimbs < 8);
//           l.[1 + v shiftlimbs] <<. shifthigh end
//         else u64 0 in
//       assume (v shiftlimbs < 8);
//       (l.[v shiftlimbs] >>. shiftlow |. tmp) end
//     else u64 0 in

//   let r1 =
//     if shift <. 448ul then begin
//       let tmp =
//         if shift <. 384ul && shiftlow >. 0ul then begin
//           assume (2 + v shiftlimbs < 8);
//           l.[2 + v shiftlimbs] <<. shifthigh end
//         else u64 0 in
//       assume (1 + v shiftlimbs < 8);
//       (l.[1 + v shiftlimbs] >>. shiftlow |. tmp) end
//     else u64 0 in

//   let r2 =
//     if shift <. 384ul then begin
//       let tmp =
//         if shift <. 320ul && shiftlow >. 0ul then begin
//           assume (3 + v shiftlimbs < 8);
//           l.[3 + v shiftlimbs] <<. shifthigh end
//         else u64 0 in
//       assume (2 + v shiftlimbs < 8);
//       (l.[2 + v shiftlimbs] >>. shiftlow |. tmp) end
//     else u64 0 in

//   let r3 =
//     if shift <. 320ul then begin
//       assume (3 + v shiftlimbs < 8);
//       l.[3 + v shiftlimbs] >>. shiftlow end
//     else u64 0 in

//   let res = (r0, r1, r2, r3) in
//   let shiftlimbs1 = (shift -. 1ul) >>. 6ul in
//   assume (v shiftlimbs1 < 8);
//   let shiftlow1 = (shift -. 1ul) &. 0x3ful in
//   assume (v shiftlow1 < 64);
//   let flag = (l.[v shiftlimbs1] >>. shiftlow1) &. u64 1 in

//   (* or: res = cadd_bit res 0ul flag *)
//   let mask = u64 0 -. flag in // mask = if flag is set then ones_v U64 else 0
//   let res_b = create4 r0 r1 r2 r3 in
//   let _, res1_b = SB.bn_add1 res_b (u64 1) in
//   map2 (BB.mask_select mask) res1_b res_b // res = if flag is set then res1_b else res_b


// let cadd_bit (r:qelem4) (bit:size_t{v bit < 256}) (flag:size_t{v flag <= 1}) : qelem4 =
//   let (r0, r1, r2, r3) = r in
//   let bit = bit +. ((flag -. 1ul) &. 0x100ul) in
//   let bit_m = bit &. 0x3ful in
//   assume (v bit_m < 64);

//   let tmp0 = if bit >>. 6ul =. 0ul then u64 1 <<. bit_m else u64 0 in
//   let t = to_u128 r0 +. to_u128 tmp0 in
//   let r0 = to_u64 t in let c0 = t >>. 64ul in

//   let tmp1 = if bit >>. 6ul =. 1ul then u64 1 <<. bit_m else u64 0 in
//   let t = c0 +. to_u128 r1 +. to_u128 tmp1 in
//   let r1 = to_u64 t in let c1 = t >>. 64ul in

//   let tmp2 = if bit >>. 6ul =. 2ul then u64 1 <<. bit_m else u64 0 in
//   let t = c1 +. to_u128 r2 +. to_u128 tmp2 in
//   let r2 = to_u64 t in let c2 = t >>. 64ul in

//   let tmp3 = if bit >>. 6ul =. 3ul then u64 1 <<. bit_m else u64 0 in
//   let t = c2 +. to_u128 r3 +. to_u128 tmp3 in
//   let r3 = to_u64 t in

//   (r0, r1, r2, r3)
