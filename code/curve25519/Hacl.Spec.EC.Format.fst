module Hacl.Spec.EC.Format


open Hacl.Cast
open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Bignum.Limb
open Hacl.Spec.EC.Point


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

type uint8_s = Seq.seq Hacl.UInt8.t

private inline_for_extraction let zero_8 = uint8_to_sint8 0uy

val point_inf: unit -> Tot spoint_513
let point_inf () =
  let s = Seq.create 10 limb_zero in
  let x = Seq.slice s 0 5 in
  let z = Seq.slice s 5 10 in
  let x = Seq.upd x 0 limb_one in
  x, z


val alloc_point: unit -> Tot spoint_513
let alloc_point () =
  let s = Seq.create 10 limb_zero in
  let x = Seq.slice s 0 5 in
  let z = Seq.slice s 5 10 in
  x, z


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 50"

val load64_le_spec: b:uint8_s{Seq.length b = 8} -> Tot limb
let load64_le_spec b =
  assert_norm (pow2 32 = 0x100000000);
  let b0 = Seq.index b 0 in
  let b1 = Seq.index b 1 in
  let b2 = Seq.index b 2 in
  let b3 = Seq.index b 3 in
  let b4 = Seq.index b 4 in
  let b5 = Seq.index b 5 in
  let b6 = Seq.index b 6 in
  let b7 = Seq.index b 7 in
  Hacl.Bignum.Limb.(
    sint8_to_sint64 b0
    |^ (sint8_to_sint64 b1 <<^ 8ul)
    |^ (sint8_to_sint64 b2 <<^ 16ul)
    |^ (sint8_to_sint64 b3 <<^ 24ul)
    |^ (sint8_to_sint64 b4 <<^ 32ul)
    |^ (sint8_to_sint64 b5 <<^ 40ul)
    |^ (sint8_to_sint64 b6 <<^ 48ul)
    |^ (sint8_to_sint64 b7 <<^ 56ul)
  )


val store64_le_spec: z:Hacl.Bignum.Limb.t -> Tot (b:uint8_s{Seq.length b = 8})
let store64_le_spec z =
  assert_norm (pow2 32 = 0x100000000);
  let open Hacl.Bignum.Limb in
  let b0 = sint64_to_sint8 z in
  let b1 = sint64_to_sint8 (z >>^ 8ul) in
  let b2 = sint64_to_sint8 (z >>^ 16ul) in
  let b3 = sint64_to_sint8 (z >>^ 24ul) in
  let b4 = sint64_to_sint8 (z >>^ 32ul) in
  let b5 = sint64_to_sint8 (z >>^ 40ul) in
  let b6 = sint64_to_sint8 (z >>^ 48ul) in
  let b7 = sint64_to_sint8 (z >>^ 56ul) in
  let s = Seq.create 8 (uint8_to_sint8 0uy) in
  let s = Seq.upd s 0 b0 in
  let s = Seq.upd s 1 b1 in
  let s = Seq.upd s 2 b2 in
  let s = Seq.upd s 3 b3 in
  let s = Seq.upd s 4 b4 in
  let s = Seq.upd s 5 b5 in
  let s = Seq.upd s 6 b6 in
  let s = Seq.upd s 7 b7 in
  s

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


val fexpand_spec: input:uint8_s{Seq.length input = 32} -> Tot (s:seqelem{Hacl.Spec.EC.AddAndDouble.red_513 s})
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

val fcontract_spec: input:seqelem -> Tot (s:uint8_s{Seq.length s = 32})
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


val point_of_scalar: scalar:uint8_s{Seq.length scalar = keylen} -> Tot spoint_513
let point_of_scalar scalar =
  let s = Seq.create 10 limb_zero in
  let x = Seq.slice s 0 5 in
  let z = Seq.slice s 5 10 in
  let x = fexpand_spec scalar in
  let z = Seq.upd z 0 limb_one in
  x, z

val scalar_of_point: p:spoint_513 -> Tot (scalar:uint8_s{Seq.length scalar = keylen})
#set-options "--z3rlimit 10"
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
