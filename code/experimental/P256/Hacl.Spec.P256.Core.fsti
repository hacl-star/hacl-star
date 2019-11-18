module Hacl.Spec.P256.Core

open Lib.IntTypes
open FStar.Math.Lemmas
open FStar.Math.Lib
open Hacl.Spec.P256.Definitions
open Hacl.Spec.P256.Lemmas

open FStar.Mul


inline_for_extraction noextract
val eq_u64:a:uint64 -> b:uint64 -> Tot (r: bool {if uint_v a = uint_v b then r == true else r == false})

inline_for_extraction noextract
val eq_0_u64: a: uint64 -> Tot (r: bool {if uint_v a = 0 then r == true else r == false})

inline_for_extraction noextract
val felem_add: arg1: felem4 {as_nat4 arg1 < prime256} -> arg2: felem4{as_nat4 arg2 < prime256} -> Tot (r : felem4 {as_nat4 r == (as_nat4 arg1 + as_nat4 arg2) % prime256})

inline_for_extraction noextract
val felem_sub: arg1: felem4 {as_nat4 arg1 < prime256} -> arg2: felem4 {as_nat4 arg2 < prime256} -> Tot (r : felem4 {as_nat4 r < prime256 /\ as_nat4 r == (as_nat4 arg1 - as_nat4 arg2) % prime256})

inline_for_extraction noextract
val reduction_prime_2prime: a: felem4 -> Tot (r:felem4{as_nat4 r == as_nat4 a % prime256})

inline_for_extraction noextract 
val shift_left_felem: input: felem4{as_nat4 input < prime256} -> Tot (r: felem4 {as_nat4 r == (as_nat4 input * 2) % prime256})

inline_for_extraction noextract
val upload_prime: unit -> Tot (r: felem4 {as_nat4 r = prime256})

inline_for_extraction noextract 
val shift_256: c: felem4 -> Tot (r: felem8{wide_as_nat4 r = as_nat4 c * pow2 256})

inline_for_extraction noextract
val add8: a: felem8 -> b: felem8 -> Pure (felem9)
  (requires True) 
  (ensures fun r -> let c, o0, o1, o2, o3, o4, o5, o6, o7 = r in 
    uint_v c <= 1 /\  wide_as_nat4 a + wide_as_nat4 b = wide_as_nat4 (o0, o1, o2, o3, o4, o5, o6, o7) + uint_v c * pow2 512)


inline_for_extraction noextract
val add8_without_carry1: a: felem8{wide_as_nat4 a < pow2 449} -> b: felem8 {wide_as_nat4 b < pow2 320} -> Tot (r: felem8 {wide_as_nat4 r = wide_as_nat4 a + wide_as_nat4 b})

inline_for_extraction noextract
val montgomery_multiplication: a: felem4 {as_nat4 a < prime256} -> b: felem4{as_nat4 b < prime256}  -> 
  Tot (result: felem4 {as_nat4 result = as_nat4 a * as_nat4 b * modp_inv2 (pow2 256) % prime256})

inline_for_extraction noextract
val cube_tuple: a: felem4{as_nat4 a < prime256} -> Tot (result: felem4{as_nat4 result = (as_nat4 a * as_nat4 a * as_nat4 a * modp_inv2(pow2 256) * modp_inv2 (pow2 256)) % prime256})

inline_for_extraction noextract
val quatre_tuple: a: felem4 {as_nat4 a < prime256} -> Tot (result : felem4 {as_nat4 result = (as_nat4 a * as_nat4 a * as_nat4 a * as_nat4 a * modp_inv2 (pow2 256) * modp_inv2 (pow2 256) * modp_inv2(pow2 256)) % prime256})

inline_for_extraction noextract
val multByThree_tuple: a: felem4{as_nat4 a < prime256}  -> Tot (result: felem4{as_nat4 result = (as_nat4 a * 3) % prime256})

inline_for_extraction noextract
val multByFour_tuple: a: felem4{as_nat4 a < prime256} -> Tot (result : felem4 {as_nat4 result = (as_nat4 a * 4) % prime256})

inline_for_extraction noextract
val multByEight_tuple: a: felem4 {as_nat4 a < prime256} -> Tot (result: felem4 {as_nat4 result = (as_nat4 a * 8) % prime256})

inline_for_extraction noextract
val multByMinusThree_tuple: a: felem4 {as_nat4 a < prime256} -> Tot (result: felem4 {as_nat4 result = (as_nat4 a * (-3)) % prime256})

inline_for_extraction noextract
val isOne_tuple: a: felem4 -> Tot (r: bool {if as_nat4 a = 1 then r == true else r == false})

inline_for_extraction noextract 
val equalFelem: a: felem4 -> b: felem4 -> Tot (r: uint64 {if as_nat4 a = as_nat4 b then uint_v r == pow2 64 - 1 else uint_v r = 0})

inline_for_extraction noextract 
val isZero_tuple_u: a: felem4 -> Tot (r: uint64 {if as_nat4 a = 0 then uint_v r == pow2 64 - 1 else uint_v r = 0})

inline_for_extraction noextract 
val isZero_tuple_b: a: felem4 ->  Tot (r: bool {if as_nat4 a = 0 then r == true else r == false})
