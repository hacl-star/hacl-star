module GHash

open Opaque_s
open Words_s
open Types_s
open Arch.Types
open GHash_s
open GF128_s
open GCTR_s
open GCM_helpers
open Collections.Seqs_s
open Collections.Seqs
open FStar.Seq

#reset-options "--use_two_phase_tc true"
let rec ghash_incremental_def (h_LE:quad32) (y_prev:quad32) (x:ghash_plain_LE) : Tot quad32 (decreases %[length x]) =
  let y_i_minus_1 =
    (if length x = 1 then
       y_prev
     else
       ghash_incremental_def h_LE y_prev (all_but_last x)) in
  let x_i = last x in
  let xor_LE = quad32_xor y_i_minus_1 x_i in
  gf128_mul_LE xor_LE h_LE

let ghash_incremental = make_opaque ghash_incremental_def

let rec ghash_incremental_to_ghash (h:quad32) (x:ghash_plain_LE) :
  Lemma(ensures ghash_incremental h (Mkfour 0 0 0 0) x == ghash_LE h x)
       (decreases %[length x])
  =
  reveal_opaque ghash_incremental_def;
  reveal_opaque ghash_LE_def;
  if length x = 1 then ()
  else ghash_incremental_to_ghash h (all_but_last x)

let rec lemma_hash_append (h:quad32) (y_prev:quad32) (a b:ghash_plain_LE) :
  Lemma(ensures
        ghash_incremental h y_prev (append a b) ==
        (let y_a = ghash_incremental h y_prev a in
         ghash_incremental h y_a b))
        (decreases %[length b])
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

let ghash_incremental0 (h:quad32) (y_prev:quad32) (x:seq quad32) : quad32 =
  if length x > 0 then ghash_incremental h y_prev x else y_prev

let lemma_hash_append2 (h y_init y_mid y_final:quad32) (s1:seq quad32) (q:quad32) : Lemma
  (requires y_mid = ghash_incremental0 h y_init s1 /\
            y_final = ghash_incremental h y_mid (create 1 q))
  (ensures  y_final == ghash_incremental h y_init (s1 @| (create 1 q)))
  =
  let qs = create 1 q in
  let s12 = s1 @| qs in
  if length s1 = 0 then (
    assert(equal s12 qs)
  ) else (
    lemma_hash_append h y_init s1 qs
  );
  ()

let lemma_hash_append3 (h y_init y_mid1 y_mid2 y_final:quad32) (s1 s2 s3:seq quad32) : Lemma
  (requires y_init = Mkfour 0 0 0 0 /\
            y_mid1 = ghash_incremental0 h y_init s1 /\
            y_mid2 = ghash_incremental0 h y_mid1 s2 /\
            length s3 > 0 /\
            y_final = ghash_incremental h y_mid2 s3)
  (ensures y_final == ghash_LE h (append s1 (append s2 s3)))
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
let lemma_ghash_incremental_bytes_extra_helper (h y_init y_mid y_final:quad32) (input:seq quad32) (final final_padded:quad32) (num_bytes:nat) : Lemma
  (requires (1 <= num_bytes /\
             num_bytes < 16 * length input /\
             16 * (length input - 1) < num_bytes /\
             num_bytes % 16 <> 0 /\ //4096 * num_bytes < pow2_32 /\
             (let num_blocks = num_bytes / 16 in
              let full_blocks = slice_work_around input num_blocks in
              y_mid = ghash_incremental0 h y_init full_blocks /\
              final == index input num_blocks /\
              (let padded_bytes = pad_to_128_bits (slice_work_around (le_quad32_to_bytes final) (num_bytes % 16)) in
               length padded_bytes == 16 /\
               final_padded == le_bytes_to_quad32 padded_bytes /\
               y_final = ghash_incremental h y_mid (create 1 final_padded)))))
  (ensures (let input_bytes = slice_work_around (le_seq_quad32_to_bytes input) num_bytes in
            let padded_bytes = pad_to_128_bits input_bytes in
            let input_quads = le_bytes_to_seq_quad32 padded_bytes in
            length padded_bytes == 16 * length input_quads /\
            y_final == ghash_incremental h y_init input_quads))
  =
  // Precondition definitions
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
