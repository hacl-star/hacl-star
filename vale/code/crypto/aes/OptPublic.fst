module OptPublic

open FStar.Seq
open Types_s
open Math.Poly2_s
open Math.Poly2.Bits_s
open GF128_s
open GF128

let shift_gf128_key_1 (h:poly) : poly =
  shift_key_1 128 gf128_modulus_low_terms h

let rec g_power (a:poly) (n:nat) : poly =
  if n = 0 then zero else // arbitrary value for n = 0
  if n = 1 then a else
  a *~ g_power a (n - 1)

let gf128_power (h:poly) (n:nat) : poly = shift_gf128_key_1 (g_power h n)

let hkeys_reqs_pub (hkeys:seq quad32) (h_LE:quad32) (v2:quad32) : Prop_s.prop0
  = 
  let h = of_quad32 (reverse_bytes_quad32 h_LE) in
  length hkeys >= 8 /\
  index hkeys 2 == v2 /\
  of_quad32 (index hkeys 0) == gf128_power h 1 /\
  of_quad32 (index hkeys 1) == gf128_power h 2 /\
  of_quad32 (index hkeys 3) == gf128_power h 3 /\
  of_quad32 (index hkeys 4) == gf128_power h 4 /\
  of_quad32 (index hkeys 6) == gf128_power h 5 /\
  of_quad32 (index hkeys 7) == gf128_power h 6 
