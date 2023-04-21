module Vale.AES.GHash_BE_s

open Vale.Def.Opaque_s
open Vale.Def.Words_s
open Vale.Def.Types_s
open Vale.AES.GF128_s
open Vale.Lib.Seqs_s
open FStar.Mul
open FStar.Seq

type ghash_plain_BE:eqtype = s:seq quad32 { length s > 0 }

let gf128_mul_BE (a b:quad32) : quad32 =
  gf128_to_quad32 (gf128_mul (gf128_of_quad32 a) (gf128_of_quad32 b))

let rec ghash_BE_def (h_BE:quad32) (x:ghash_plain_BE) : Tot quad32 (decreases %[length x]) =
  let y_i_minus_1 =
    (if length x = 1 then
       Mkfour 0 0 0 0
     else
       ghash_BE_def h_BE (all_but_last x)) in
  let x_i = last x in
  let xor_BE = quad32_xor y_i_minus_1 x_i in
  gf128_mul_BE xor_BE h_BE
[@"opaque_to_smt"] let ghash_BE = opaque_make ghash_BE_def
irreducible let ghash_BE_reveal = opaque_revealer (`%ghash_BE) ghash_BE ghash_BE_def
