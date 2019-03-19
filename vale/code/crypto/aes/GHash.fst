module GHash
open Math.Poly2.Lemmas

#reset-options "--use_two_phase_tc true"

let rec lemma_ghash_poly_degree h init data j k =
  if k > j then lemma_ghash_poly_degree h init data j (k - 1)

let shift_gf128_key_1 h =
  shift_key_1 128 gf128_modulus_low_terms h

let lemma_ghash_rev (h:poly) (init:poly) (data:int -> poly128) (j:int) (k:int) : Lemma
  (requires k > j /\ degree h < 128 /\ degree init < 128 /\ degree (data (k - 1)) < 128)
  (ensures (
    let h1 = shift_gf128_key_1 h in
    let a = ghash_poly h init data j (k - 1) +. data (k - 1) in
    ghash_poly h init data j k == mod_rev 128 (a *. h1) gf128_modulus
  ))
  =
  let h1 = shift_gf128_key_1 h in
  let a = ghash_poly h init data j (k - 1) +. data (k - 1) in
  let rev x = reverse x 127 in
  let g = gf128_modulus in
  lemma_gf128_degree ();
  calc (==) {
    // ghash_poly h init data j k
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

let lemma_ghash_incremental_def_0 (h_LE:quad32) (y_prev:quad32) (x:seq quad32)
  =
  ()

let rec ghash_incremental_to_ghash (h:quad32) (x:seq quad32)
  =
  reveal_opaque ghash_incremental_def;
  reveal_opaque ghash_LE_def;
  if length x = 1 then ()
  else ghash_incremental_to_ghash h (all_but_last x)

let rec lemma_hash_append (h:quad32) (y_prev:quad32) (a b:ghash_plain_LE)
  =
  reveal_opaque ghash_incremental_def;
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

let lemma_hash_append3 (h y_init y_mid1 y_mid2 y_final:quad32) (s1 s2 s3:seq quad32)
  =
  let s23 = append s2 s3 in
  let s123 = append s1 s23 in
  if length s1 = 0 then (
    assert(equal s123 s23);
    if length s2 = 0 then (
      assert(equal s123 s3);
      ghash_incremental_to_ghash h s3
    ) else
      lemma_hash_append h y_mid1 s2 s3;
      ghash_incremental_to_ghash h s23
  ) else if length s2 = 0 then (
    assert(equal s123 (append s1 s3));
    lemma_hash_append h y_init s1 s3;
    ghash_incremental_to_ghash h (append s1 s3)
  ) else (
    lemma_hash_append h y_init s1 s23;
    lemma_hash_append h y_mid1 s2 s3;
    ghash_incremental_to_ghash h s123;
    ()
  )

#reset-options "--z3rlimit 30"
open FStar.Mul
let lemma_ghash_incremental_bytes_extra_helper (h y_init y_mid y_final:quad32) (input:seq quad32) (final final_padded:quad32) (num_bytes:nat)  // Precondition definitions
  =
  let num_blocks = num_bytes / 16 in
  let full_blocks = slice_work_around input num_blocks in
  let padded_bytes = pad_to_128_bits (slice_work_around (le_quad32_to_bytes final) (num_bytes % 16)) in

  // Postcondition definitions
  let input_bytes = slice_work_around (le_seq_quad32_to_bytes input) num_bytes in
  let padded_bytes' = pad_to_128_bits input_bytes in
  let input_quads = le_bytes_to_seq_quad32 padded_bytes' in

  lemma_hash_append2 h y_init y_mid y_final full_blocks final_padded;
  assert (y_final == ghash_incremental h y_init (full_blocks @| (create 1 final_padded)));

  //// Need to show that input_quads == full_blocks @| (create 1 final_padded)

  // First show that the inputs to input_quads corresponds
  pad_to_128_bits_le_quad32_to_bytes input num_bytes;
  assert (padded_bytes' == le_seq_quad32_to_bytes (slice input 0 num_blocks) @| pad_to_128_bits (slice (le_quad32_to_bytes final) 0 (num_bytes % 16)));
  assert (padded_bytes' == le_seq_quad32_to_bytes full_blocks @| padded_bytes);

  // Start deconstructing input_quads
  append_distributes_le_bytes_to_seq_quad32 (le_seq_quad32_to_bytes full_blocks) padded_bytes; // Distribute the le_bytes_to_seq_quad32
  assert (input_quads == (le_bytes_to_seq_quad32 (le_seq_quad32_to_bytes full_blocks)) @| (le_bytes_to_seq_quad32 padded_bytes));
  le_bytes_to_seq_quad32_to_bytes (slice_work_around input num_blocks);
  assert (input_quads == full_blocks @| (le_bytes_to_seq_quad32 padded_bytes));
  le_bytes_to_seq_quad_of_singleton final_padded padded_bytes;
  assert (input_quads == full_blocks @| (create 1 final_padded));

  ()

let lemma_ghash_registers (h y_init y0 y1 y2 y3 y4 r0 r1 r2 r3:quad32) (input:seq quad32) (bound:nat)
  =
  lemma_hash_append2 h y_init y0 y1 (slice input 0 bound) r0;

  let s = (slice input 0 bound) @| (create 1 r0) in
  lemma_hash_append2 h y_init y1 y2 s r1;
  let s = s @| (create 1 r1) in
  lemma_hash_append2 h y_init y2 y3 s r2;
  let s = s @| (create 1 r2) in
  lemma_hash_append2 h y_init y3 y4 s r3;
  let s = s @| (create 1 r3) in  
  assert (equal s (slice input 0 (bound + 4)));
  ()

(*
let lemma_slice_extension (s:seq quad32) (bound:int) (q:quad32)
  =
  ()
*)   
