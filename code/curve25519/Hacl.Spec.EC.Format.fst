module Hacl.Spec.EC.Format


open Hacl.Cast
open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Bignum.Limb
open Hacl.Spec.Bignum
open Hacl.Spec.EC.Point


#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 100"


type uint8_s = Seq.seq Hacl.UInt8.t

private inline_for_extraction let zero_8 = uint8_to_sint8 0uy

val point_inf: unit -> Tot (t:spoint_513{selem (fst t) = 1 /\ selem (snd t) = 0})
let point_inf () =
  let s = Seq.create 10 limb_zero in
  let x = Seq.slice s 0 5 in
  let z = Seq.slice s 5 10 in
  let x = Seq.upd x 0 limb_one in
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 x;
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 z;
  cut (Hacl.Spec.Bignum.Bigint.seval x = 1);
  cut (Hacl.Spec.Bignum.Bigint.seval z = 0);
  Math.Lemmas.modulo_lemma (Hacl.Spec.Bignum.Bigint.seval x) (pow2 255 - 19);
  Math.Lemmas.modulo_lemma (Hacl.Spec.Bignum.Bigint.seval z) (pow2 255 - 19);
  x, z


val alloc_point: unit -> Tot spoint_513
let alloc_point () =
  let s = Seq.create 10 limb_zero in
  let x = Seq.slice s 0 5 in
  let z = Seq.slice s 5 10 in
  x, z


open FStar.Endianness
open Hacl.Spec.Endianness
open Hacl.Endianness

val load64_le_spec: b:uint8_s{Seq.length b = 8} -> GTot (z:limb{v z = hlittle_endian b})
let load64_le_spec b =
  let z = hlittle_endian b in
  lemma_little_endian_is_bounded (reveal_sbytes b);
  Hacl.Cast.uint64_to_sint64 (FStar.UInt64.uint_to_t z)


val store64_le_spec: z:Hacl.Bignum.Limb.t -> GTot (b:uint8_s{Seq.length b = 8 /\ hlittle_endian b = v z})
let store64_le_spec z =
  let b = little_bytes 8ul (v z) in
  intro_sbytes b


inline_for_extraction let mask_51 : p:t{v p = pow2 51 - 1} = assert_norm(pow2 51 - 1 = 0x7ffffffffffff);
  uint64_to_limb 0x7ffffffffffffuL


inline_for_extraction val seq_upd_5: s0:limb -> s1:limb -> s2:limb -> s3:limb -> s4:limb -> Tot (s:seqelem{Seq.index s 0 == s0 /\ Seq.index s 1 == s1 /\ Seq.index s 2 == s2 /\ Seq.index s 3 == s3 /\ Seq.index s 4 == s4})
inline_for_extraction let seq_upd_5 s0 s1 s2 s3 s4 =
  let s = Seq.create len limb_zero in
  let s = Seq.upd s 0 s0 in
  let s = Seq.upd s 1 s1 in
  let s = Seq.upd s 2 s2 in
  let s = Seq.upd s 3 s3 in
  let s = Seq.upd s 4 s4 in
  s


val fexpand_spec: input:uint8_s{Seq.length input = 32} -> GTot (s:seqelem{Hacl.Spec.EC.AddAndDouble.red_513 s})
let fexpand_spec input =
  let i0 = load64_le_spec (Seq.slice input 0 8) in
  let i1 = load64_le_spec (Seq.slice input 6 14) in
  let i2 = load64_le_spec (Seq.slice input 12 20) in
  let i3 = load64_le_spec (Seq.slice input 19 27) in
  let i4 = load64_le_spec (Seq.slice input 24 32) in
  let output0 = (i0         ) &^ mask_51 in
  let output1 = (i1 >>^ 3ul ) &^ mask_51 in
  let output2 = (i2 >>^ 6ul ) &^ mask_51 in
  let output3 = (i3 >>^ 1ul ) &^ mask_51 in
  let output4 = (i4 >>^ 12ul) &^ mask_51 in
  UInt.logand_mask (v i0) 51;
  UInt.logand_mask (v (i1 >>^ 3ul)) 51;
  UInt.logand_mask (v (i2 >>^ 6ul)) 51;
  UInt.logand_mask (v (i3 >>^ 1ul)) 51;
  UInt.logand_mask (v (i4 >>^ 12ul)) 51;
  seq_upd_5 output0 output1 output2 output3 output4


inline_for_extraction let nineteen : p:t{v p = 19} = assert_norm(pow2 64 > 19); uint64_to_limb 19uL

val fcontract_spec: input:seqelem -> GTot (s:uint8_s{Seq.length s = 32})
let fcontract_spec input =
  let t0 = Seq.index input 0 in
  let t1 = Seq.index input 1 in
  let t2 = Seq.index input 2 in
  let t3 = Seq.index input 3 in
  let t4 = Seq.index input 4 in
  let t1 = t1 +%^ (t0 >>^ 51ul) in
  let t0 = t0 &^ mask_51 in
  let t2 = t2 +%^ (t1 >>^ 51ul) in
  let t1 = t1 &^ mask_51 in
  let t3 = t3 +%^ (t2 >>^ 51ul) in
  let t2 = t2 &^ mask_51 in
  let t4 = t4 +%^ (t3 >>^ 51ul) in
  let t3 = t3 &^ mask_51 in
  let t0 = t0 +%^ (nineteen *%^ (t4 >>^ 51ul)) in
  let t4 = t4 &^ mask_51 in
  let t1 = t1 +%^ (t0 >>^ 51ul) in
  let t0 = t0 &^ mask_51 in
  let t2 = t2 +%^ (t1 >>^ 51ul) in
  let t1 = t1 &^ mask_51 in
  let t3 = t3 +%^ (t2 >>^ 51ul) in
  let t2 = t2 &^ mask_51 in
  let t4 = t4 +%^ (t3 >>^ 51ul) in
  let t3 = t3 &^ mask_51 in
  let t0 = t0 +%^ (nineteen *%^ (t4 >>^ 51ul)) in
  let t4 = t4 &^ mask_51 in
  let t0 = t0 +%^ nineteen in
  let t1 = t1 +%^ (t0 >>^ 51ul) in
  let t0 = t0 &^ mask_51 in
  let t2 = t2 +%^ (t1 >>^ 51ul) in
  let t1 = t1 &^ mask_51 in
  let t3 = t3 +%^ (t2 >>^ 51ul) in
  let t2 = t2 &^ mask_51 in
  let t4 = t4 +%^ (t3 >>^ 51ul) in
  let t3 = t3 &^ mask_51 in
  let t0 = t0 +%^ (nineteen *%^ (t4 >>^ 51ul)) in
  let t4 = t4 &^ mask_51 in
  let two52 = uint64_to_sint64 0x8000000000000uL in
  let t0 = t0 +%^ two52 -%^ nineteen in
  let t1 = t1 +%^ two52 -%^ limb_one in
  let t2 = t2 +%^ two52 -%^ limb_one in
  let t3 = t3 +%^ two52 -%^ limb_one in
  let t4 = t4 +%^ two52 -%^ limb_one in
  let t1 = t1 +%^ (t0 >>^ 51ul) in
  let t0 = t0 &^ mask_51 in
  let t2 = t2 +%^ (t1 >>^ 51ul) in
  let t1 = t1 &^ mask_51 in
  let t3 = t3 +%^ (t2 >>^ 51ul) in
  let t2 = t2 &^ mask_51 in
  let t4 = t4 +%^ (t3 >>^ 51ul) in
  let t3 = t3 &^ mask_51 in
  let t4 = t4 &^ mask_51 in
  let o0 = t0 |^ (t1 <<^ 51ul) in
  let o1 = (t1 >>^ 13ul) |^ (t2 <<^ 38ul) in
  let o2 = (t2 >>^ 26ul) |^ (t3 <<^ 25ul) in
  let o3 = (t3 >>^ 39ul) |^ (t4 <<^ 12ul) in
  FStar.Seq.(store64_le_spec o0 @| store64_le_spec o1 @| store64_le_spec o2 @| store64_le_spec o3)


val point_of_scalar: scalar:uint8_s{Seq.length scalar = keylen} -> GTot spoint_513
let point_of_scalar scalar =
  let s = Seq.create 10 limb_zero in
  let x = Seq.slice s 0 5 in
  let z = Seq.slice s 5 10 in
  let x = fexpand_spec scalar in
  let z = Seq.upd z 0 limb_one in
  x, z

val scalar_of_point: p:spoint_513 -> GTot (scalar:uint8_s{Seq.length scalar = keylen})
let scalar_of_point point =
  let x = sgetx point in
  let z = sgetz point in
  let zmone = Hacl.Spec.Bignum.Crecip.crecip_tot z in
  Hacl.Spec.EC.AddAndDouble2.lemma_513_is_53 x;
  Hacl.Spec.EC.AddAndDouble2.lemma_513_is_55 zmone;
  Hacl.Spec.EC.AddAndDouble.fmul_53_55_is_fine x zmone;
  let y = Hacl.Spec.Bignum.fmul_tot x zmone in
  fcontract_spec y


val format_secret: secret:uint8_s{Seq.length secret = keylen} -> Tot (s:uint8_s{Seq.length s = keylen})
let format_secret secret =
  assert_norm(pow2 8 = 256);
  let e0  = Seq.index secret 0 in
  let e31 = Seq.index secret 31 in
  let open Hacl.UInt8 in
  let e0  = e0 &^ (uint8_to_sint8 248uy) in
  let e31 = e31 &^ (uint8_to_sint8 127uy) in
  let e31 = e31 |^ (uint8_to_sint8 64uy) in
  let e = Seq.upd secret 0 e0 in
  let e = Seq.upd e 31 e31 in
  e
