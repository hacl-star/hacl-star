module Vale.AES.GHash_BE
open FStar.Mul
open Vale.Math.Poly2.Lemmas
open Vale.Math.Poly2.Words

friend Vale.AES.OptPublic_BE

#reset-options

let shift_gf128_key_1 (h:poly) : poly =
  shift_key_1 128 gf128_modulus_low_terms h

let rec g_power (a:poly) (n:nat) : poly =
  if n = 0 then zero else // arbitrary value for n = 0
  if n = 1 then a else
  a *~ g_power a (n - 1)

let lemma_g_power_1 a = ()
let lemma_g_power_n a n = ()

let gf128_power h n = shift_gf128_key_1 (g_power h n)
let lemma_gf128_power h n = ()

let rec ghash_poly_unroll (h:poly) (prev:poly) (data:int -> poly128) (k:int) (m n:nat) : poly =
  let d = data (k + m) in
  let p = g_power h (n + 1) in
  if m = 0 then (prev +. d) *~ p else
  ghash_poly_unroll h prev data k (m - 1) (n + 1) +. d *~ p

let lemma_hkeys_reqs_pub_priv (hkeys:seq quad32) (h_BE:quad32) : Lemma
  (hkeys_reqs_pub hkeys h_BE <==> hkeys_reqs_priv hkeys h_BE)
  =
  ()

let rec lemma_ghash_unroll_back_forward_rec (h:poly) (prev:poly) (data:int -> poly128) (k:int) (n m:nat) : Lemma
  (requires m < n)
  (ensures ghash_unroll h prev data k n 0 ==
    ghash_unroll h prev data k (n - 1 - m) (m + 1) +. ghash_unroll_back h prev data k (n + 1) m)
  =
  lemma_add_all ();
  if m > 0 then lemma_ghash_unroll_back_forward_rec h prev data k n (m - 1)

let lemma_ghash_unroll_back_forward (h:poly) (prev:poly) (data:int -> poly128) (k:int) (n:nat) : Lemma
  (ghash_unroll h prev data k n 0 == ghash_unroll_back h prev data k (n + 1) n)
  =
  lemma_add_all ();
  if n > 0 then lemma_ghash_unroll_back_forward_rec h prev data k n (n - 1)

let lemma_gf128_mul_rev_mod_rev (a h:poly) : Lemma
  (requires degree a < 128 /\ degree h < 128)
  (ensures gf128_mul_rev a h == mod_rev 128 (a *. shift_gf128_key_1 h) gf128_modulus)
  =
  let h1 = shift_gf128_key_1 h in
  let rev x = reverse x 127 in
  let g = gf128_modulus in
  lemma_gf128_degree ();
  calc (==) {
    // gf128_mul_rev a h
    rev ((rev a *. rev h) %. g);
    == {lemma_mod_mul_mod_right (rev a) (rev h) g}
    rev ((rev a *. (rev h %. g)) %. g);
    == {lemma_shift_key_1 128 gf128_modulus_low_terms h}
    rev ((rev a *. (shift (rev h1) 1 %. g)) %. g);
    == {lemma_mod_mul_mod_right (rev a) (shift (rev h1) 1) g}
    rev ((rev a *. (shift (rev h1) 1)) %. g);
    == {lemma_shift_is_mul (rev h1) 1}
    rev ((rev a *. (rev h1 *. monomial 1)) %. g);
    == {lemma_mul_all ()}
    rev (((rev a *. rev h1) *. monomial 1) %. g);
    == {lemma_shift_is_mul (rev a *. rev h1) 1}
    rev (shift (rev a *. rev h1) 1 %. g);
    == {lemma_mul_reverse_shift_1 a h1 127}
    rev (reverse (a *. h1) 255 %. g);
  }

let rec lemma_ghash_poly_unroll_n (h:poly) (prev:poly) (data:int -> poly128) (k:int) (m n:nat) : Lemma
  (ghash_poly_unroll h prev data k m (n + 1) == ghash_poly_unroll h prev data k m n *~ h)
  =
  let d = data (k + m) in
  let p0 = g_power h (n + 1) in
  let p1 = g_power h (n + 2) in
  if m = 0 then
    calc (==) {
      ghash_poly_unroll h prev data k m (n + 1);
      == {}
      (prev +. d) *~ p1;
      == {}
      (prev +. d) *~ (h *~ p0);
      == {lemma_gf128_mul_rev_commute p0 h}
      (prev +. d) *~ (p0 *~ h);
      == {lemma_gf128_mul_rev_associate (prev +. d) p0 h}
      ((prev +. d) *~ p0) *~ h;
      == {}
      ghash_poly_unroll h prev data k m n *~ h;
    }
  else
    let ghash0 = ghash_poly_unroll h prev data k (m - 1) (n + 1) in
    let ghash1 = ghash_poly_unroll h prev data k (m - 1) (n + 2) in
    calc (==) {
      ghash_poly_unroll h prev data k m (n + 1);
      == {}
      ghash1 +. d *~ p1;
      == {lemma_ghash_poly_unroll_n h prev data k (m - 1) (n + 1)}
      ghash0 *~ h +. d *~ p1;
      == {}
      ghash0 *~ h +. d *~ (h *~ p0);
      == {lemma_gf128_mul_rev_commute p0 h}
      ghash0 *~ h +. d *~ (p0 *~ h);
      == {lemma_gf128_mul_rev_associate d p0 h}
      ghash0 *~ h +. (d *~ p0) *~ h;
      == {lemma_gf128_mul_rev_distribute_left ghash0 (d *~ p0) h}
      (ghash0 +. d *~ p0) *~ h;
      == {}
      ghash_poly_unroll h prev data k m n *~ h;
    }

let rec lemma_ghash_poly_unroll (h0:poly) (prev:poly) (data:int -> poly128) (k:int) (m:nat) : Lemma
  (requires degree h0 < 128 /\ degree prev < 128)
  (ensures ghash_poly_unroll h0 prev data k m 0 == ghash_poly h0 prev data k (k + m + 1))
  =
  let d = data (k + m) in
  let p1 = g_power h0 1 in
  let ghash0 = ghash_poly h0 prev data k (k + m) in
  if m = 0 then
    calc (==) {
      ghash_poly_unroll h0 prev data k m 0;
      == {}
      (prev +. d) *~ p1;
      == {}
      (ghash0 +. d) *~ h0;
      == {}
      ghash_poly h0 prev data k (k + m + 1);
    }
  else
    let unroll0 = ghash_poly_unroll h0 prev data k (m - 1) 0 in
    let unroll1 = ghash_poly_unroll h0 prev data k (m - 1) 1 in
    calc (==) {
      ghash_poly_unroll h0 prev data k m 0;
      == {}
      unroll1 +. d *~ p1;
      == {
        calc (==) {
          unroll1;
          == {lemma_ghash_poly_unroll_n h0 prev data k (m - 1) 0}
          unroll0 *~ h0;
          == {lemma_ghash_poly_unroll h0 prev data k (m - 1)}
          ghash0 *~ h0;
        }
      }
      ghash0 *~ h0 +. d *~ h0;
      == {lemma_gf128_mul_rev_distribute_left ghash0 d h0}
      (ghash0 +. d) *~ h0;
      == {}
      ghash_poly h0 prev data k (k + m + 1);
    }

let rec lemma_ghash_unroll_poly_unroll (h:poly) (prev:poly) (data:int -> poly128) (k:int) (m n:nat) : Lemma
  (requires degree h < 128 /\ degree prev < 128)
  (ensures
    mod_rev 128 (ghash_unroll h prev data k m n) gf128_modulus ==
    ghash_poly_unroll h prev data k m n
  )
  =
  let g = gf128_modulus in
  let d = data (k + m) in
  let p = g_power h (n + 1) in
  let sp = shift_gf128_key_1 p in
  lemma_gf128_degree ();
  if m = 0 then
    calc (==) {
      mod_rev 128 (ghash_unroll h prev data k m n) g;
      == {}
      mod_rev 128 ((prev +. d) *. sp) g;
      == {lemma_gf128_mul_rev_mod_rev (prev +. d) p}
      (prev +. d) *~ p;
      == {}
      ghash_poly_unroll h prev data k m n;
    }
  else
    let unroll1 = ghash_unroll h prev data k (m - 1) (n + 1) in
    let ghash0 = ghash_poly_unroll h prev data k (m - 1) (n + 1) in
    calc (==) {
      mod_rev 128 (ghash_unroll h prev data k m n) g;
      == {}
      mod_rev 128 (unroll1 +. d *. sp) g;
      == {lemma_add_mod_rev 128 unroll1 (d *. sp) g}
      mod_rev 128 unroll1 g +. mod_rev 128 (d *. sp) g;
      == {lemma_ghash_unroll_poly_unroll h prev data k (m - 1) (n + 1)}
      ghash0 +. mod_rev 128 (d *. sp) g;
      == {lemma_gf128_mul_rev_mod_rev d p}
      ghash0 +. d *~ p;
      == {}
      ghash_poly_unroll h prev data k m n;
    }

let lemma_ghash_poly_of_unroll h prev data k m =
  lemma_ghash_poly_unroll h prev data k m;
  lemma_ghash_unroll_poly_unroll h prev data k m 0;
  ()

let rec lemma_ghash_incremental_poly_rec (h_BE:quad32) (y_prev:quad32) (x:seq quad32) (data:int -> poly128) : Lemma
  (requires
    (forall (i:int).{:pattern data i \/ index x i} 0 <= i && i < length x ==>
      data i == of_quad32 (index x i))
  )
  (ensures
    of_quad32 (ghash_incremental_def h_BE y_prev x) ==
    ghash_poly (of_quad32 h_BE) (of_quad32 y_prev) data 0 (length x)
  )
  (decreases (length x))
  =
  ghash_incremental_reveal ();
  let (~~) = of_quad32 in
  let h = ~~h_BE in
  let prev = ~~y_prev in
  let m = length x in
  if m > 0 then
    let y_i_minus_1 = ghash_incremental_def h_BE y_prev (all_but_last x) in
    let x_i = last x in
    let xor_BE = quad32_xor y_i_minus_1 x_i in
    let g = gf128_modulus in
    calc (==) {
      ~~(ghash_incremental_def h_BE y_prev x);
      == {}
      ~~(gf128_mul_BE xor_BE h_BE);
      == {lemma_of_to_quad32 (~~xor_BE *~ h)}
      ~~xor_BE *~ h;
      == {lemma_add_quad32 y_i_minus_1 x_i}
      (~~y_i_minus_1 +. ~~x_i) *~ h;
      == {lemma_ghash_incremental_poly_rec h_BE y_prev (all_but_last x) data}
      (ghash_poly h prev data 0 (m - 1) +. data (m - 1)) *~ h;
      == {}
      ghash_poly h prev data 0 m;
    }

let lemma_ghash_incremental_poly h_BE y_prev x =
  ghash_incremental_reveal ();
  lemma_ghash_incremental_poly_rec h_BE y_prev x (fun_seq_quad32_BE_poly128 x)

let lemma_ghash_incremental_def_0 (h_BE:quad32) (y_prev:quad32) (x:seq quad32)
  =
  ()

let rec ghash_incremental_to_ghash (h:quad32) (x:seq quad32)
  =
  ghash_incremental_reveal ();
  ghash_BE_reveal ();
  if length x = 1 then ()
  else ghash_incremental_to_ghash h (all_but_last x)

let rec lemma_hash_append (h:quad32) (y_prev:quad32) (a b:ghash_plain_BE)
  =
  ghash_incremental_reveal ();
  let ab = append a b in
  assert (last ab == last b);
  if length b = 1 then
    (lemma_slice_first_exactly_in_append a b;
     assert (all_but_last ab == a);
     ())
  else
    lemma_hash_append h y_prev a (all_but_last b);
    lemma_all_but_last_append a b;
    assert(all_but_last ab == append a (all_but_last b));
  ()

let lemma_ghash_incremental0_append (h y0 y1 y2:quad32) (s1 s2:seq quad32) : Lemma
  (requires y1 = ghash_incremental0 h y0 s1 /\
            y2 = ghash_incremental0 h y1 s2)
  (ensures  y2 = ghash_incremental0 h y0 (s1 @| s2))
  =
  let s12 = s1 @| s2 in
  if length s1 = 0 then (
    assert (equal s12 s2)
  ) else (
    if length s2 = 0 then (
      assert (equal s12 s1)
    ) else (
      lemma_hash_append h y0 s1 s2
    )
  );
  ()

let lemma_hash_append2 (h y_init y_mid y_final:quad32) (s1:seq quad32) (q:quad32)
  =
  let qs = create 1 q in
  let s12 = s1 @| qs in
  if length s1 = 0 then (
    assert(equal s12 qs)
  ) else (
    lemma_hash_append h y_init s1 qs
  );
  ()

let ghash_incremental_bytes_pure_no_extra (old_io io h:quad32) (in_quads:seq quad32) (num_bytes:nat64) : Lemma
  (requires io = ghash_incremental0 h old_io in_quads)
  (ensures  length in_quads == (num_bytes / 16) /\
            num_bytes % 16 == 0 ==>
            (let input_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE in_quads)) 0 num_bytes in
             let padded_bytes = pad_to_128_bits input_bytes in
             let input_quads = be_bytes_to_seq_quad32 padded_bytes in
             num_bytes > 0 ==> length input_quads > 0 /\
                              io == ghash_incremental h old_io input_quads))
  =
  if length in_quads = (num_bytes / 16) && num_bytes % 16 = 0 && num_bytes > 0 then (
    let input_bytes = slice (le_seq_quad32_to_bytes in_quads) 0 num_bytes in
    no_extra_bytes_helper in_quads num_bytes;
    be_bytes_to_seq_quad32_to_bytes in_quads;
    ()
  ) else ()
  ;
  ()

#reset-options "--z3rlimit 30"
let lemma_ghash_incremental_bytes_extra_helper (h y_init y_mid y_final:quad32) (input:seq quad32) (final final_padded:quad32) (num_bytes:nat)  // Precondition definitions
  =
  let num_blocks = num_bytes / 16 in
  let full_blocks = slice input 0 num_blocks in
  let padded_bytes = pad_to_128_bits (slice (be_quad32_to_bytes final) 0 (num_bytes % 16)) in

  // Postcondition definitions
  let input_bytes = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE input)) 0 num_bytes in
  let padded_bytes' = pad_to_128_bits input_bytes in
  let input_quads = be_bytes_to_seq_quad32 padded_bytes' in

  lemma_hash_append2 h y_init y_mid y_final full_blocks final_padded;
  assert (y_final == ghash_incremental h y_init (full_blocks @| (create 1 final_padded)));

  //// Need to show that input_quads == full_blocks @| (create 1 final_padded)

  // First show that the inputs to input_quads corresponds
  pad_to_128_bits_be_quad32_to_bytes input num_bytes;
  assert (padded_bytes' == seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE (slice input 0 num_blocks)) @| pad_to_128_bits (slice (be_quad32_to_bytes final) 0 (num_bytes % 16)));
  assert (padded_bytes' == seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE full_blocks) @| padded_bytes);

  // Start deconstructing input_quads
  append_distributes_be_bytes_to_seq_quad32 (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE full_blocks)) padded_bytes; // Distribute the be_bytes_to_seq_quad32
  assert (input_quads == (be_bytes_to_seq_quad32 (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE full_blocks))) @| (be_bytes_to_seq_quad32 padded_bytes));
  be_bytes_to_seq_quad32_to_bytes (slice input 0 num_blocks);
  assert (input_quads == full_blocks @| (be_bytes_to_seq_quad32 padded_bytes));
  be_bytes_to_seq_quad_of_singleton final_padded padded_bytes;
  assert (input_quads == full_blocks @| (create 1 final_padded));

  ()

let lemma_ghash_incremental_bytes_extra_helper_alt (h y_init y_mid y_final:quad32) (input_blocks:seq quad32) (final final_padded:quad32) (num_bytes:nat) : Lemma
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
  =
  let q_in = append input_blocks (create 1 final) in
  let num_blocks = num_bytes / 16 in
  let full_blocks = slice q_in 0 num_blocks in
  assert (equal full_blocks input_blocks);
  lemma_ghash_incremental_bytes_extra_helper h y_init y_mid y_final q_in final final_padded num_bytes

let lemma_div_distribute a b c =
  let ab = a +. b in
  let a' = a /. c in
  let b' = b /. c in
  let ab' = ab /. c in
  let a'' = a %. c in
  let b'' = b %. c in
  let ab'' = ab %. c in
  lemma_div_mod a c;
  lemma_div_mod b c;
  lemma_div_mod ab c;
  // (a +. b) == (a) +. (b)
  assert ((ab' *. c +. ab'') == (a' *. c +. a'') +. (b' *. c +. b''));
  lemma_add_define_all ();
  lemma_equal (ab' *. c +. a' *. c +. b' *. c) (ab'' +. a'' +. b'');
  lemma_mul_distribute_left ab' a' c;
  lemma_mul_distribute_left (ab' +. a') b' c;
  assert ((ab' +. a' +. b') *. c == ab'' +. a'' +. b'');
  lemma_mul_smaller_is_zero (ab' +. a' +. b') c;
  assert (ab' +. a' +. b' == zero);
  lemma_zero_define ();
  lemma_equal ab' (a' +. b');
  ()

let lemma_swap128_mask_shift (a:poly) : Lemma
  (requires degree a < 128)
  (ensures (
    let a_sw = swap a 64 in
    mask a 64 == shift a_sw (-64) /\
    shift a (-64) == mask a_sw 64
  ))
  =
  lemma_quad32_double_swap a;
  lemma_quad32_double a;
  lemma_quad32_double (swap a 64);
  lemma_mask_is_mod a 64;
  lemma_shift_is_div (swap a 64) 64;
  lemma_shift_is_div a 64;
  lemma_mask_is_mod (swap a 64) 64

let lemma_gf128_constant_shift_rev ()
  =
  let n0:nat32 = 0 in
  let n1:nat32 = 0xc2000000 in
  let n2:nat32 = 0 in
  let n3:nat32 = 0 in
  let r3 = gf128_low_shift in
  calc (==) {
    of_quad32 (Mkfour n0 n1 n2 n3);
    == {
      calc (==) {
        Mkfour n0 n1 n2 n3;
        == {lemma_quad32_of_nat32s n0 n1 n2 n3}
        to_quad32 (poly128_of_nat32s n0 n1 n2 n3);
        == {
          lemma_bitwise_all ();
          lemma_to_nat 32 (reverse r3 31) n1;
          lemma_equal (poly128_of_nat32s n0 n1 n2 n3) (reverse r3 63)
        }
        to_quad32 (reverse r3 63);
      }
    }
    of_quad32 (to_quad32 (reverse r3 63));
    == {lemma_of_to_quad32 (reverse r3 63)}
    reverse r3 63;
  };
  lemma_bitwise_all ();
  lemma_split_define (reverse gf128_low_shift 63) 64;
  lemma_equal (mask (reverse gf128_low_shift 63) 64) (reverse gf128_low_shift 63);
  lemma_equal (shift (reverse gf128_low_shift 63) (-64)) zero
