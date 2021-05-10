module Hacl.Bignum25519

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

module S51 = Hacl.Spec.Curve25519.Field51.Definition
module SL51 = Hacl.Spec.Curve25519.Field51.Lemmas
module BN = Hacl.Impl.Curve25519.Field51
module SC = Spec.Curve25519

friend Hacl.Curve25519_51

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
let mask_51 = u64 0x7ffffffffffff

let make_u64_5 b s0 s1 s2 s3 s4 =
  b.(0ul) <- s0;
  b.(1ul) <- s1;
  b.(2ul) <- s2;
  b.(3ul) <- s3;
  b.(4ul) <- s4

let make_u64_10 b s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 =
  b.(0ul) <- s0;
  b.(1ul) <- s1;
  b.(2ul) <- s2;
  b.(3ul) <- s3;
  b.(4ul) <- s4;
  b.(5ul) <- s5;
  b.(6ul) <- s6;
  b.(7ul) <- s7;
  b.(8ul) <- s8;
  b.(9ul) <- s9

let make_zero b =
  b.(0ul) <- u64 0;
  b.(1ul) <- u64 0;
  b.(2ul) <- u64 0;
  b.(3ul) <- u64 0;
  b.(4ul) <- u64 0;
  assert_norm (S51.as_nat5 (u64 0, u64 0, u64 0, u64 0, u64 0) % Spec.Curve25519.prime == 0)

let make_one b =
  b.(0ul) <- u64 1;
  b.(1ul) <- u64 0;
  b.(2ul) <- u64 0;
  b.(3ul) <- u64 0;
  b.(4ul) <- u64 0;
  assert_norm (S51.as_nat5 (u64 1, u64 0, u64 0, u64 0, u64 0) % Spec.Curve25519.prime == 1)


[@CInline]
let fsum a b =
  BN.fadd a a b


[@CInline]
let fdifference a b =
  BN.fsub a b a


inline_for_extraction noextract
val carry51:
    #m:S51.scale64{m < 8192}
  -> l:uint64
  -> cin:uint64 ->
  Pure (uint64 & uint64)
  (requires
    S51.felem_fits1 l m /\
    S51.felem_fits1 cin 1)
  (ensures fun (l0, l1) ->
    v l + v cin == v l1 * pow2 51 + v l0 /\
    S51.felem_fits1 l0 1 /\ uint_v l1 < m + 1)

let carry51 l cin =
  let l' = l +! cin in
  mod_mask_lemma l' 51ul;
  assert (v (mod_mask #U64 #SEC 51ul) == v mask_51);
  FStar.Math.Lemmas.pow2_modulo_modulo_lemma_1 (v l') 51 64;
  FStar.Math.Lemmas.euclidean_division_definition (v l') (pow2 51);
  FStar.Math.Lemmas.pow2_minus 64 51;
  (l' &. mask_51, l' >>. 51ul)


let reduce_513 a =
  let (f0, f1, f2, f3, f4) = (a.(0ul), a.(1ul), a.(2ul), a.(3ul), a.(4ul)) in
  let tmp0, c0 = carry51 #9 f0 (u64 0) in
  let tmp1, c1 = carry51 #10 f1 c0 in
  let tmp2, c2 = carry51 #9 f2 c1 in
  let tmp3, c3 = carry51 #9 f3 c2 in
  let tmp4, c4 = carry51 #9 f4 c3 in
  assert (S51.felem_fits5 (tmp0, tmp1, tmp2, tmp3, tmp4) (1, 1, 1, 1, 1));
  SL51.lemma_carry5_simplify c0 c1 c2 c3 c4 tmp0 tmp1 tmp2 tmp3 tmp4;
  assert (
    S51.as_nat5 (f0, f1, f2, f3, f4) % SC.prime ==
    (S51.as_nat5 (tmp0, tmp1, tmp2, tmp3, tmp4) + v c4 * 19) % SC.prime);

  [@inline_let]
  let tmp0', c5 = carry51 #1 tmp0 (c4 *! u64 19) in

  [@inline_let]
  let tmp1' = tmp1 +! c5 in
  Hacl.Spec.Curve25519.Field51.lemma_mul_inv (tmp0', tmp1, tmp2, tmp3, tmp4) c5;
  make_u64_5 a tmp0' tmp1' tmp2 tmp3 tmp4


[@CInline]
let fmul output input input2 =
  push_frame();
  let tmp = create 10ul (u128 0) in
  BN.fmul output input input2 tmp;
  pop_frame()


[@CInline]
let times_2 out a =
  (**) let h0 = get() in
  let a0 = a.(0ul) in
  let a1 = a.(1ul) in
  let a2 = a.(2ul) in
  let a3 = a.(3ul) in
  let a4 = a.(4ul) in
  let o0 = u64 2 *. a0 in
  let o1 = u64 2 *. a1 in
  let o2 = u64 2 *. a2 in
  let o3 = u64 2 *. a3 in
  let o4 = u64 2 *. a4 in
  make_u64_5 out o0 o1 o2 o3 o4;

  (**) let h1 = get() in
  (**) assert (S51.felem_fits1 a0 1);
  (**) assert (F51.felem_fits h1 out (2, 4, 2, 2, 2));

  calc (==) {
    (2 * (F51.fevalh h0 a)) % SC.prime;
    (==) { calc (==) {
           F51.fevalh h0 a;
           (==) { }
           S51.as_nat5 (a0, a1, a2, a3, a4) % SC.prime;
           }
         }
    (2 * (S51.as_nat5 (a0, a1, a2, a3, a4) % SC.prime)) % SC.prime;
    (==) { FStar.Math.Lemmas.lemma_mod_mul_distr_r 2 (S51.as_nat5 (a0, a1, a2, a3, a4)) SC.prime }
    (2 * S51.as_nat5 (a0, a1, a2, a3, a4)) % SC.prime;
    (==) { calc (==) {
           2 * S51.as_nat5 (a0, a1, a2, a3, a4);
           (==) { SL51.lemma_smul_felem5 (u64 2) (a0, a1, a2, a3, a4) }
           2 * v a0 + 2 * v a1 * S51.pow51 + 2 * v a2 * S51.pow51 * S51.pow51 +
           2 * v a3 * S51.pow51 * S51.pow51 * S51.pow51 +
           2 * v a4 * S51.pow51 * S51.pow51 * S51.pow51 * S51.pow51;
           (==) {
             assert_norm (2 * S51.pow51 < pow2 64);
             assert_norm (4 * S51.pow51 < pow2 64);
             FStar.Math.Lemmas.small_mod (2 * v a0) (pow2 64);
             FStar.Math.Lemmas.small_mod (2 * v a1) (pow2 64);
             FStar.Math.Lemmas.small_mod (2 * v a2) (pow2 64);
             FStar.Math.Lemmas.small_mod (2 * v a3) (pow2 64);
             FStar.Math.Lemmas.small_mod (2 * v a4) (pow2 64)
           }
           S51.as_nat5 (u64 2 *. a0, u64 2 *. a1, u64 2 *. a2, u64 2 *. a3, u64 2 *. a4);
           }
         }
    S51.as_nat5 (u64 2 *. a0, u64 2 *. a1, u64 2 *. a2, u64 2 *. a3, u64 2 *. a4) % SC.prime;
    (==) { }
    F51.fevalh h1 out;
  }


[@CInline]
let times_d out a =
  push_frame();
  let d = create 5ul (u64 0) in
  d.(0ul) <- u64 0x00034dca135978a3;
  d.(1ul) <- u64 0x0001a8283b156ebd;
  d.(2ul) <- u64 0x0005e7a26001c029;
  d.(3ul) <- u64 0x000739c663a03cbb;
  d.(4ul) <- u64 0x00052036cee2b6ff;
  assert_norm (S51.as_nat5 (u64 0x00034dca135978a3, u64 0x0001a8283b156ebd,
    u64 0x0005e7a26001c029, u64 0x000739c663a03cbb, u64 0x00052036cee2b6ff) %
      Spec.Curve25519.prime == Spec.Ed25519.d);
  fmul out d a;
  pop_frame()


[@CInline]
let times_2d out a =
  push_frame();
  let d2 = create 5ul (u64 0) in
  d2.(0ul) <- u64 0x00069b9426b2f159;
  d2.(1ul) <- u64 0x00035050762add7a;
  d2.(2ul) <- u64 0x0003cf44c0038052;
  d2.(3ul) <- u64 0x0006738cc7407977;
  d2.(4ul) <- u64 0x0002406d9dc56dff;
  fmul out d2 a;
  assert_norm (S51.as_nat5 (u64 0x00069b9426b2f159, u64 0x00035050762add7a,
    u64  0x0003cf44c0038052, u64 0x0006738cc7407977, u64  0x0002406d9dc56dff) %
      Spec.Curve25519.prime == 2 `SC.fmul` Spec.Ed25519.d);
  pop_frame()


[@CInline]
let fsquare out a =
  push_frame();
  let tmp = create 5ul (u128 0) in
  BN.fsqr out a tmp;
  pop_frame()


[@CInline]
let fsquare_times output input count =
  push_frame();
  let tmp = create 5ul (u128 0) in
  Hacl.Curve25519_51.fsquare_times output input tmp count;
  pop_frame()


[@CInline]
let fsquare_times_inplace output count =
  push_frame();
  let tmp = create 5ul (u128 0) in
  Hacl.Curve25519_51.fsquare_times output output tmp count;
  pop_frame()


let inverse out a =
  push_frame();
  let tmp = create 10ul (u128 0) in
  Hacl.Curve25519_51.finv out a tmp;
  pop_frame()


[@CInline]
let reduce out =
  let (o0, o1, o2, o3, o4) = (out.(0ul), out.(1ul), out.(2ul), out.(3ul), out.(4ul)) in
  let (f0, f1, f2, f3, f4) = Hacl.Spec.Curve25519.Field51.carry_felem5_full (o0, o1, o2, o3, o4) in
  let (f0, f1, f2, f3, f4) = Hacl.Spec.Curve25519.Field51.subtract_p5 (f0, f1, f2, f3, f4) in
  Math.Lemmas.small_mod (S51.as_nat5 (f0, f1, f2, f3, f4)) Spec.Curve25519.prime;
  make_u64_5 out f0 f1 f2 f3 f4


let load_51 output input =
  push_frame ();
  let u64s = create 4ul (u64 0) in
  let h0 = ST.get () in
  uints_from_bytes_le #U64 u64s input;
  let h1 = ST.get () in
  BSeq.uints_from_bytes_le_nat_lemma #U64 #SEC #4 (as_seq h0 input);
  assert (BSeq.nat_from_intseq_le (as_seq h1 u64s) == BSeq.nat_from_bytes_le (as_seq h0 input));
  let u64s3 = u64s.(3ul) in
  u64s.(3ul) <- u64s3 &. u64 0x7fffffffffffffff;
  mod_mask_lemma u64s3 63ul;
  assert_norm (0x7fffffffffffffff = pow2 63 - 1);
  assert (v (mod_mask #U64 #SEC 63ul) == v (u64 0x7fffffffffffffff));
  let h2 = ST.get () in
  assert (v (LSeq.index (as_seq h2 u64s) 3) < pow2 63);
  Hacl.Spec.Curve25519.Field64.Lemmas.lemma_felem64_mod255 (as_seq h1 u64s);
  assert (BSeq.nat_from_intseq_le (as_seq h2 u64s) == BSeq.nat_from_bytes_le (as_seq h0 input) % pow2 255);

  output.(0ul) <- u64s.(0ul) &. mask_51;
  output.(1ul) <- (u64s.(0ul) >>. 51ul) |. ((u64s.(1ul) &. u64 0x3fffffffff) <<. 13ul);
  output.(2ul) <- (u64s.(1ul) >>. 38ul) |. ((u64s.(2ul) &. u64 0x1ffffff) <<. 26ul);
  output.(3ul) <- (u64s.(2ul) >>. 25ul) |. ((u64s.(3ul) &. u64 0xfff) <<. 39ul);
  output.(4ul) <- u64s.(3ul) >>. 12ul;

  SL51.lemma_load_felem (as_seq h2 u64s);
  pop_frame ()


let store_51 output input =
  let h0 = ST.get () in
  push_frame ();
  let u64s = create 4ul (u64 0) in
  BN.store_felem u64s input;
  let h1 = ST.get () in
  assert (as_seq h1 u64s == BSeq.nat_to_intseq_le 4 (F51.fevalh h0 input));
  uints_to_bytes_le 4ul output u64s;
  BSeq.uints_to_bytes_le_nat_lemma #U64 #SEC 4 (F51.fevalh h0 input);
  pop_frame ()
