module Vale.AES.GHash_s

open Vale.Def.Opaque_s
open Vale.Def.Words_s
open Vale.Def.Types_s
open Vale.AES.GF128_s
open Vale.Lib.Seqs_s
open FStar.Mul
open FStar.Seq

type ghash_plain_LE:eqtype = s:seq quad32 { length s > 0 }

let gf128_mul_LE (a_LE b_LE:quad32) : quad32 =
  let a_BE = reverse_bytes_quad32 a_LE in
  let b_BE = reverse_bytes_quad32 b_LE in
  let ab_BE = gf128_to_quad32 (gf128_mul (gf128_of_quad32 a_BE) (gf128_of_quad32 b_BE)) in
  reverse_bytes_quad32 ab_BE

let rec ghash_LE_def (h_LE:quad32) (x:ghash_plain_LE) : Tot quad32 (decreases %[length x]) =
  let y_i_minus_1 =
    (if length x = 1 then
       Mkfour 0 0 0 0
     else
       ghash_LE_def h_LE (all_but_last x)) in
  let x_i = last x in
  let xor_LE = quad32_xor y_i_minus_1 x_i in
  gf128_mul_LE xor_LE h_LE
[@"opaque_to_smt"] let ghash_LE = opaque_make ghash_LE_def
irreducible let ghash_LE_reveal = opaque_revealer (`%ghash_LE) ghash_LE ghash_LE_def
