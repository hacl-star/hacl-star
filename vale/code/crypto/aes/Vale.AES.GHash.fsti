module Vale.AES.GHash

open Vale.Def.Opaque_s
open Vale.Def.Words_s
open Vale.Def.Types_s
open Vale.Arch.Types
open Vale.AES.GHash_s
open Vale.AES.GF128_s
open Vale.AES.GCTR_s
open Vale.AES.GCM_helpers
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
open Vale.AES.OptPublic

#reset-options "--use_two_phase_tc true"

let poly128 = p:poly{degree p < 128}

let fun_seq_quad32_LE_poly128 (s:seq quad32) : (int -> poly128) =
  fun (i:int) -> if 0 <= i && i < length s then of_quad32 (reverse_bytes_quad32 (index s i)) else zero

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
  let h = of_quad32 (reverse_bytes_quad32 (reverse_bytes_quad32 h_BE)) in
  length hkeys >= 8 /\
  index hkeys 2 == h_BE /\
  of_quad32 (index hkeys 0) == gf128_power h 1 /\
  of_quad32 (index hkeys 1) == gf128_power h 2 /\
  of_quad32 (index hkeys 3) == gf128_power h 3 /\
  of_quad32 (index hkeys 4) == gf128_power h 4 /\
  index hkeys 5 = Mkfour 0 0 0 0 /\
  of_quad32 (index hkeys 6) == gf128_power h 5 /\
  of_quad32 (index hkeys 7) == gf128_power h 6

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

val lemma_ghash_poly_degree (h:poly) (init:poly) (data:int -> poly128) (j:int) (k:int) : Lemma
  (requires degree h < 128 /\ degree init < 128)
  (ensures degree (ghash_poly h init data j k) < 128)
  (decreases (k - j))
  [SMTPat (ghash_poly h init data j k)]

val lemma_ghash_poly_of_unroll (h:poly) (prev:poly) (data:int -> poly128) (k:int) (m:nat) : Lemma
  (requires degree h < 128 /\ degree prev < 128)
  (ensures
    mod_rev 128 (ghash_unroll h prev data k m 0) gf128_modulus ==
    ghash_poly h prev data k (k + m + 1)
  )

let lemma_add_manip (x y z:poly) : Lemma
  (x +. y +. z == x +. z +. y)
  =
  calc (==) {
    x +. y +. z;
    == { lemma_add_associate x y z }
    x +. (y +. z);
    == { lemma_add_commute y z }
    x +. (z +. y);
    == { lemma_add_associate x z y }
    x +. z +. y;
  };
  ()

let rec ghash_incremental_def (h_LE:quad32) (y_prev:quad32) (x:seq quad32) : Tot quad32 (decreases %[length x]) =
  if length x = 0 then y_prev else
  let y_i_minus_1 = ghash_incremental_def h_LE y_prev (all_but_last x) in
  let x_i = last x in
  let xor_LE = quad32_xor y_i_minus_1 x_i in
  gf128_mul_LE xor_LE h_LE
[@"opaque_to_smt"] let ghash_incremental = opaque_make ghash_incremental_def
irreducible let ghash_incremental_reveal = opaque_revealer (`%ghash_incremental) ghash_incremental ghash_incremental_def

val lemma_ghash_incremental_poly (h_LE:quad32) (y_prev:quad32) (x:seq quad32) : Lemma
  (ensures
    of_quad32 (reverse_bytes_quad32 (ghash_incremental h_LE y_prev x)) ==
    ghash_poly
      (of_quad32 (reverse_bytes_quad32 h_LE))
      (of_quad32 (reverse_bytes_quad32 y_prev))
      (fun_seq_quad32_LE_poly128 x) 0 (length x)
  )

// avoids need for extra fuel
val lemma_ghash_incremental_def_0 (h_LE:quad32) (y_prev:quad32) (x:seq quad32) : Lemma
  (requires length x == 0)
  (ensures ghash_incremental_def h_LE y_prev x == y_prev)
  [SMTPat (ghash_incremental_def h_LE y_prev x)]

val ghash_incremental_to_ghash (h:quad32) (x:seq quad32) : Lemma
  (requires length x > 0)
  (ensures ghash_incremental h (Mkfour 0 0 0 0) x == ghash_LE h x)
  (decreases %[length x])

val lemma_hash_append (h:quad32) (y_prev:quad32) (a b:ghash_plain_LE) : Lemma
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

val lemma_hash_append3 (h y_init y_mid1 y_mid2 y_final:quad32) (s1 s2 s3:seq quad32) : Lemma
  (requires y_init = Mkfour 0 0 0 0 /\
            y_mid1 = ghash_incremental0 h y_init s1 /\
            y_mid2 = ghash_incremental0 h y_mid1 s2 /\
            length s3 > 0 /\
            y_final = ghash_incremental h y_mid2 s3)
  (ensures y_final == ghash_LE h (append s1 (append s2 s3)))

val ghash_incremental_bytes_pure_no_extra (old_io io h:quad32) (in_quads:seq quad32) (num_bytes:nat64) : Lemma
  (requires io = ghash_incremental0 h old_io in_quads)
  (ensures  length in_quads == (num_bytes / 16) /\
            num_bytes % 16 == 0 ==>
            (let input_bytes = slice (le_seq_quad32_to_bytes in_quads) 0 num_bytes in
             let padded_bytes = pad_to_128_bits input_bytes in
             let input_quads = le_bytes_to_seq_quad32 padded_bytes in
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
              (let padded_bytes = pad_to_128_bits (slice (le_quad32_to_bytes final) 0 (num_bytes % 16)) in
               length padded_bytes == 16 /\
               final_padded == le_bytes_to_quad32 padded_bytes /\
               y_final = ghash_incremental h y_mid (create 1 final_padded)))))
  (ensures (let input_bytes = slice (le_seq_quad32_to_bytes input) 0 num_bytes in
            let padded_bytes = pad_to_128_bits input_bytes in
            let input_quads = le_bytes_to_seq_quad32 padded_bytes in
            length padded_bytes == 16 * length input_quads /\
            y_final == ghash_incremental h y_init input_quads))

val lemma_ghash_incremental_bytes_extra_helper_alt (h y_init y_mid y_final:quad32) (input_blocks:seq quad32) (final final_padded:quad32) (num_bytes:nat) : Lemma
  (requires (1 <= num_bytes /\
             num_bytes < 16 * (length input_blocks) + 16 /\
             16 * (length input_blocks) < num_bytes /\
             num_bytes % 16 <> 0 /\
             y_mid = ghash_incremental0 h y_init input_blocks /\
            (let padded_bytes = pad_to_128_bits (slice (le_quad32_to_bytes final) 0 (num_bytes % 16)) in
             length padded_bytes == 16 /\
             final_padded == le_bytes_to_quad32 padded_bytes /\
             y_final = ghash_incremental h y_mid (create 1 final_padded))))
  (ensures (let input_bytes = slice (le_seq_quad32_to_bytes (append input_blocks (create 1 final))) 0 num_bytes in
            let padded_bytes = pad_to_128_bits input_bytes in
            let input_quads = le_bytes_to_seq_quad32 padded_bytes in
            length padded_bytes == 16 * length input_quads /\
            y_final == ghash_incremental h y_init input_quads))

val lemma_ghash_registers (h y_init y0 y1 y2 y3 y4 r0 r1 r2 r3:quad32) (input:seq quad32) (bound:nat) : Lemma
  (requires length input >= bound + 4 /\
            r0 == index input (bound + 0) /\
            r1 == index input (bound + 1) /\
            r2 == index input (bound + 2) /\
            r3 == index input (bound + 3) /\
            y0 == ghash_incremental0 h y_init (slice input 0 bound) /\
            y1 == ghash_incremental h y0 (create 1 r0) /\
            y2 == ghash_incremental h y1 (create 1 r1) /\
            y3 == ghash_incremental h y2 (create 1 r2) /\
            y4 == ghash_incremental h y3 (create 1 r3))
  (ensures y4 == ghash_incremental h y_init (slice input 0 (bound + 4)))

(*
val lemma_slice_extension (s:seq quad32) (bound:int) (q:quad32) : Lemma
  (requires 0 <= bound /\ bound + 1 <= length s /\
            index (slice s 0 (bound + 1)) bound == q)
  (ensures equal (slice s 0 (bound + 1))
                 (append (slice s 0 bound) (create 1 q)))
*)
