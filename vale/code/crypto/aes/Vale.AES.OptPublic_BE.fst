module Vale.AES.OptPublic_BE

open FStar.Mul
open FStar.Seq
open Vale.Def.Types_s
open Vale.Math.Poly2_s
open Vale.Math.Poly2.Bits_s
open Vale.AES.GF128_s
open Vale.AES.GF128
open Vale.Def.Words_s

let shift_gf128_key_1 (h:poly) : poly =
  shift_key_1 128 gf128_modulus_low_terms h

let rec g_power (a:poly) (n:nat) : poly =
  if n = 0 then zero else // arbitrary value for n = 0
  if n = 1 then a else
  a *~ g_power a (n - 1)

let gf128_power (h:poly) (n:nat) : poly = shift_gf128_key_1 (g_power h n)

let hkeys_reqs_pub (hkeys:seq quad32) (h_BE:quad32) : Vale.Def.Prop_s.prop0
  =
  let h = of_quad32 h_BE in
  length hkeys >= 3 /\
  of_quad32 (index hkeys 0) == gf128_power h 1 /\
  of_quad32 (index hkeys 1) == gf128_power h 2 /\
  index hkeys 2 == h_BE
