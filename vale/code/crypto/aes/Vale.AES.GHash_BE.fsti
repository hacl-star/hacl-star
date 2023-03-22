module Vale.AES.GHash_BE

open Vale.Def.Opaque_s
open Vale.Def.Words_s
open Vale.Def.Types_s
open Vale.Arch.Types
open Vale.AES.GHash_BE_s
open Vale.AES.GF128_s
open Vale.AES.GCTR_BE_s
open Vale.AES.GCM_helpers_BE
open Vale.Lib.Seqs_s
open Vale.Lib.Seqs
open FStar.Seq
open Vale.Math.Poly2_s
open Vale.Math.Poly2
open Vale.Math.Poly2.Bits_s
open Vale.Math.Poly2.Bits
open Vale.AES.GF128
open FStar.Mul
open FStar.Calc
open Vale.AES.OptPublic_BE
open Vale.Math.Poly2.Words
open Vale.Math.Poly2.Lemmas
open Vale.Def.Words.Seq_s

#reset-options

let poly128 = p:poly{degree p < 128}

let fun_seq_quad32_BE_poly128 (s:seq quad32) : (int -> poly128) =
  fun (i:int) -> if 0 <= i && i < length s then of_quad32 (index s i) else zero

let rec ghash_poly (h:poly) (init:poly) (data:int -> poly128) (j:int) (k:int) : Tot poly (decreases (k - j)) =
  if k <= j then init else
  gf128_mul_rev (ghash_poly h init data j (k - 1) +. data (k - 1)) h

val g_power (a:poly) (n:nat) : poly
val lemma_g_power_1 (a:poly) : Lemma (g_power a 1 == a)
val lemma_g_power_n (a:poly) (n:pos) : Lemma (g_power a (n + 1) == a *~ g_power a n)

val gf128_power (h:poly) (n:nat) : poly
val lemma_gf128_power (h:poly) (n:nat) : Lemma
  (gf128_power h n == shift_key_1 128 gf128_modulus_low_terms (g_power h n))

let hkeys_reqs_priv (hkeys:seq quad32) (h_BE:quad32) : Vale.Def.Prop_s.prop0
  =
  let h = of_quad32 h_BE in
  length hkeys >= 3 /\
  index hkeys 2 == h_BE /\
  of_quad32 (index hkeys 0) == gf128_power h 1 /\
  of_quad32 (index hkeys 1) == gf128_power h 2

val lemma_hkeys_reqs_pub_priv (hkeys:seq quad32) (h_BE:quad32) : Lemma
  (hkeys_reqs_pub hkeys h_BE <==> hkeys_reqs_priv hkeys h_BE)

// Unrolled series of n ghash computations
let rec ghash_unroll (h:poly) (prev:poly) (data:int -> poly128) (k:int) (m n:nat) : poly =
  let d = data (k + m) in
  let p = gf128_power h (n + 1) in
  if m = 0 then (prev +. d) *. p else
  ghash_unroll h prev data k (m - 1) (n + 1) +. d *. p

// Unrolled series of n ghash computations in reverse order (last to first)
let rec ghash_unroll_back (h:poly) (prev:poly) (data:int -> poly128) (k:int) (n m:nat) : poly =
  let d = data (k + (n - 1 - m)) in
  let p = gf128_power h (m + 1) in
  let v = if m = n - 1 then prev +. d else d in
  if m = 0 then v *. p else
  ghash_unroll_back h prev data k n (m - 1) +. v *. p

val lemma_ghash_unroll_back_forward (h:poly) (prev:poly) (data:int -> poly128) (k:int) (n:nat) : Lemma
  (ghash_unroll h prev data k n 0 == ghash_unroll_back h prev data k (n + 1) n)

val lemma_ghash_poly_of_unroll (h:poly) (prev:poly) (data:int -> poly128) (k:int) (m:nat) : Lemma
  (requires degree h < 128 /\ degree prev < 128)
  (ensures
    mod_rev 128 (ghash_unroll h prev data k m 0) gf128_modulus ==
    ghash_poly h prev data k (k + m + 1)
  )

let rec ghash_incremental_def (h_BE:quad32) (y_prev:quad32) (x:seq quad32) : Tot quad32 (decreases %[length x]) =
  if length x = 0 then y_prev else
  let y_i_minus_1 = ghash_incremental_def h_BE y_prev (all_but_last x) in
  let x_i = last x in
  let xor_BE = quad32_xor y_i_minus_1 x_i in
  gf128_mul_BE xor_BE h_BE
[@"opaque_to_smt"] let ghash_incremental = opaque_make ghash_incremental_def
irreducible let ghash_incremental_reveal = opaque_revealer (`%ghash_incremental) ghash_incremental ghash_incremental_def

val lemma_ghash_incremental_poly (h_BE:quad32) (y_prev:quad32) (x:seq quad32) : Lemma
  (ensures
    of_quad32 (ghash_incremental h_BE y_prev x) ==
    ghash_poly
      (of_quad32 h_BE)
      (of_quad32 y_prev)
      (fun_seq_quad32_BE_poly128 x) 0 (length x)
  )

// avoids need for extra fuel
val lemma_ghash_incremental_def_0 (h_BE:quad32) (y_prev:quad32) (x:seq quad32) : Lemma
  (requires length x == 0)
  (ensures ghash_incremental_def h_BE y_prev x == y_prev)
  [SMTPat (ghash_incremental_def h_BE y_prev x)]

val ghash_incremental_to_ghash (h:quad32) (x:seq quad32) : Lemma
  (requires length x > 0)
  (ensures ghash_incremental h (Mkfour 0 0 0 0) x == ghash_BE h x)
  (decreases %[length x])

val lemma_hash_append (h:quad32) (y_prev:quad32) (a b:ghash_plain_BE) : Lemma
  (ensures
    ghash_incremental h y_prev (append a b) ==
    (let y_a = ghash_incremental h y_prev a in ghash_incremental h y_a b))
  (decreases %[length b])

let ghash_incremental0 (h:quad32) (y_prev:quad32) (x:seq quad32) : quad32 =
  if length x > 0 then ghash_incremental h y_prev x else y_prev

val lemma_ghash_incremental0_append (h y0 y1 y2:quad32) (s1 s2:seq quad32) : Lemma
  (requires y1 = ghash_incremental0 h y0 s1 /\
            y2 = ghash_incremental0 h y1 s2)
  (ensures  y2 = ghash_incremental0 h y0 (s1 @| s2))

val lemma_hash_append2 (h y_init y_mid y_final:quad32) (s1:seq quad32) (q:quad32) : Lemma
  (requires y_mid = ghash_incremental0 h y_init s1 /\
            y_final = ghash_incremental h y_mid (create 1 q))
  (ensures  y_final == ghash_incremental h y_init (s1 @| (create 1 q)))

val ghash_incremental_bytes_pure_no_extra (old_io io h:quad32) (in_quads:seq quad32) (num_bytes:nat64) : Lemma
  (requires io = ghash_incremental0 h old_io in_quads)
  (ensures  length in_quads == (num_bytes / 16) /\
            num_bytes % 16 == 0 ==>
            (let input_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE in_quads)) 0 num_bytes in
             let padded_bytes = pad_to_128_bits input_bytes in
             let input_quads = be_bytes_to_seq_quad32 padded_bytes in
             num_bytes > 0 ==> length input_quads > 0 /\
                              io == ghash_incremental h old_io input_quads))

#reset-options "--z3rlimit 30"
val lemma_ghash_incremental_bytes_extra_helper (h y_init y_mid y_final:quad32) (input:seq quad32) (final final_padded:quad32) (num_bytes:nat) : Lemma
  (requires (1 <= num_bytes /\
             num_bytes < 16 * length input /\
             16 * (length input - 1) < num_bytes /\
             num_bytes % 16 <> 0 /\ //4096 * num_bytes < pow2_32 /\
             (let num_blocks = num_bytes / 16 in
              let full_blocks = slice input 0 num_blocks in
              y_mid = ghash_incremental0 h y_init full_blocks /\
              final == index input num_blocks /\
              (let padded_bytes = pad_to_128_bits (slice (be_quad32_to_bytes final) 0 (num_bytes % 16)) in
               length padded_bytes == 16 /\
               final_padded == be_bytes_to_quad32 padded_bytes /\
               y_final = ghash_incremental h y_mid (create 1 final_padded)))))
  (ensures (let input_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE input)) 0 num_bytes in
            let padded_bytes = pad_to_128_bits input_bytes in
            let input_quads = be_bytes_to_seq_quad32 padded_bytes in
            length padded_bytes == 16 * length input_quads /\
            y_final == ghash_incremental h y_init input_quads))

val lemma_ghash_incremental_bytes_extra_helper_alt (h y_init y_mid y_final:quad32) (input_blocks:seq quad32) (final final_padded:quad32) (num_bytes:nat) : Lemma
  (requires (1 <= num_bytes /\
             num_bytes < 16 * (length input_blocks) + 16 /\
             16 * (length input_blocks) < num_bytes /\
             num_bytes % 16 <> 0 /\
             y_mid = ghash_incremental0 h y_init input_blocks /\
            (let padded_bytes = pad_to_128_bits (slice (be_quad32_to_bytes final) 0 (num_bytes % 16)) in
             length padded_bytes == 16 /\
             final_padded == be_bytes_to_quad32 padded_bytes /\
             y_final = ghash_incremental h y_mid (create 1 final_padded))))
  (ensures (let input_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE (append input_blocks (create 1 final)))) 0 num_bytes in
            let padded_bytes = pad_to_128_bits input_bytes in
            let input_quads = be_bytes_to_seq_quad32 padded_bytes in
            length padded_bytes == 16 * length input_quads /\
            y_final == ghash_incremental h y_init input_quads))

let lemma_add_mul_zero_low (a0 a1 b0 b1:poly) : Lemma
  (requires a1 == zero \/ b1 == zero)
  (ensures add (mul a0 b0) (mul a1 b1) == mul a0 b0)
  =
  lemma_mul_commute a1 b1;
  lemma_mul_zero a1;
  lemma_mul_zero b1;
  lemma_add_zero (mul a0 b0)

let lemma_add_mul_zero_high (a0 a1 b0 b1:poly) : Lemma
  (requires a0 == zero \/ b0 == zero)
  (ensures add (mul a0 b0) (mul a1 b1) == mul a1 b1)
  =
  lemma_mul_commute a0 b0;
  lemma_mul_zero a0;
  lemma_mul_zero b0;
  lemma_add_commute (mul a0 b0) (mul a1 b1);
  lemma_add_zero (mul a1 b1)

val lemma_div_distribute (a b c:poly) : Lemma
  (requires degree c >= 0)
  (ensures (a +. b) /. c == (a /. c) +. (b /. c))

val lemma_swap128_mask_shift (a:poly) : Lemma
  (requires degree a < 128)
  (ensures (
    let a_sw = swap a 64 in
    mask a 64 == shift a_sw (-64) /\
    shift a (-64) == mask a_sw 64
  ))

val lemma_gf128_constant_shift_rev (_:unit) : Lemma
  (mask (of_quad32 (Mkfour 0 0xc2000000 0 0)) 64 == reverse gf128_low_shift 63 /\
    shift (of_quad32 (Mkfour 0 0xc2000000 0 0)) (-64) == zero)
