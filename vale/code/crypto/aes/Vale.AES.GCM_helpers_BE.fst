module Vale.AES.GCM_helpers_BE

open FStar.Tactics
open Vale.Def.Words_s
open Vale.Def.Words.Seq_s
open Vale.Def.Types_s
open Vale.Arch.Types
open FStar.Mul
open FStar.Seq
open Vale.Def.Opaque_s
open Vale.Def.Words.Two_s
open Vale.Def.Words.Four_s
open Vale.AES.AES_BE_s
open Vale.AES.GCTR_BE_s
open FStar.Math.Lemmas
open Vale.Lib.Seqs
open Vale.AES.Types_helpers

let no_extra_bytes_helper s num_bytes =
  ()

let be_seq_quad32_to_bytes_tail_prefix (s:seq quad32) (num_bytes:nat) =
  let num_extra = num_bytes % 16 in
  let num_blocks = num_bytes / 16 in
  let final = index s num_blocks in
  let x  = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE s)) (num_blocks * 16) num_bytes in
  let x' = slice (be_quad32_to_bytes final) 0 num_extra in

  be_seq_quad32_to_bytes_of_singleton final;
  assert (be_quad32_to_bytes final == seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE (create 1 final)));
  assert (equal (create 1 final) (slice s num_blocks (length s)));

  assert (x' == slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE (slice s num_blocks (length s)))) 0 num_extra);
  slice_commutes_be_seq_quad32_to_bytes s num_blocks (length s);
  assert (x' == slice (slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE s)) (num_blocks * 16) (length s * 16)) 0 num_extra);
  assert (x' == slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE s)) (num_blocks * 16) num_bytes);

  assert (equal x' x);
  ()

let pad_to_128_bits_multiples (b:seq nat8) : Lemma
  (let full_blocks = (length b) / 16 * 16 in
   let full_bytes, partial_bytes = split b full_blocks in
   pad_to_128_bits b == full_bytes @| pad_to_128_bits partial_bytes)
  =
  let full_blocks = (length b) / 16 * 16 in
  let full_bytes, partial_bytes = split b full_blocks in
  if length b < 16 then (
    assert (full_bytes == empty);
    assert (partial_bytes == b);
    append_empty_l(pad_to_128_bits partial_bytes);
    ()
  ) else (
    assert (length full_bytes + length partial_bytes == length b);
    assert (length full_bytes % 16 == 0);
    let num_extra_bytes = length b % 16 in
    assert (num_extra_bytes == (length partial_bytes) % 16);
    if num_extra_bytes = 0 then (
      lemma_split b full_blocks;
      assert (b == full_bytes @| partial_bytes);
      ()
    ) else (
      let pad = create (16 - num_extra_bytes) 0 in
      assert (equal (b @| pad) (full_bytes @| (partial_bytes @| pad)));
      ()
    );
    ()
  )

let pad_to_128_bits_be_quad32_to_bytes (s:seq quad32) (num_bytes:int) =
  let num_extra = num_bytes % 16 in
  let num_blocks = num_bytes / 16 in
  let full_quads,final_quads = split s num_blocks in
  assert(length final_quads == 1);
  let final_quad = index final_quads 0 in
  let b = slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE s)) 0 num_bytes in
  pad_to_128_bits_multiples b; // ==>  pad_to_128_bits b == full_bytes @| pad_to_128_bits partial_bytes
  let full_blocks = (length b) / 16 * 16 in
  let full_bytes, partial_bytes = split b full_blocks in
  slice_commutes_be_seq_quad32_to_bytes0 s num_blocks;
  slice_slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE s)) 0 num_bytes 0 full_blocks;
  assert (full_bytes == seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE full_quads));

  slice_slice (seq_nat32_to_seq_nat8_BE (seq_four_to_seq_BE s)) 0 num_bytes full_blocks num_bytes;
  be_seq_quad32_to_bytes_tail_prefix s num_bytes;
  ()

#reset-options "--smtencoding.elim_box true --z3rlimit 60 --z3refresh --initial_ifuel 0 --max_ifuel 1 --initial_fuel 1 --max_fuel 1"
let lemma_pad_to_32_bits_helper (s s'':seq4 nat8) (n:nat) : Lemma
  (requires
    n <= 2 /\
    (forall (i:nat).{:pattern (index s i) \/ (index s'' i)} i < 4 ==>
      index s'' i == (if i < n then index s i else 0))
  )
  (ensures four_to_nat 8 (seq_to_four_BE s'') == (four_to_nat 8 (seq_to_four_BE s) / pow2 (8 * (4 - n))) * pow2 (8 * (4 - n)))
  =
  assert (n == 0 \/ n == 1 \/ n == 2);
  assert_norm (four_to_nat 8 (seq_to_four_BE s) == four_to_nat_unfold 8 (seq_to_four_BE s));
  assert_norm (four_to_nat 8 (seq_to_four_BE s'') == four_to_nat_unfold 8 (seq_to_four_BE s''));
  assert_norm (pow2 (2 * 8) == 0x10000);
  assert_norm (pow2 (3 * 8) == 0x1000000);
  assert_norm (pow2 (4 * 8) == 0x100000000);
  let x = four_to_nat 8 (seq_to_four_BE s'') in
  assert (n == 0 ==> x / pow2 (8 * (4 - n)) == x / 0x100000000);
  assert (n == 1 ==> x / pow2 (8 * (4 - n)) == x / 0x1000000);
  assert (n == 2 ==> x / pow2 (8 * (4 - n)) == x / 0x10000);
  assert_norm (((x / pow2 (8 * 4)) * pow2 (8 * 4)) % pow2 (8 * 4) == 0);
  assert_norm (((x / pow2 (8 * 3)) * pow2 (8 * 3)) % pow2 (8 * 3) == 0);
  assert_norm (((x / pow2 (8 * 2)) * pow2 (8 * 2)) % pow2 (8 * 2) == 0);
  ()

let lemma_pad_to_32_bits (s s'':seq4 nat8) (n:nat) : Lemma
  (requires
    n <= 4 /\
    (forall (i:nat).{:pattern (index s i) \/ (index s'' i)} i < 4 ==>
      index s'' i == (if i < n then index s i else 0))
  )
  (ensures four_to_nat 8 (seq_to_four_BE s'') == (four_to_nat 8 (seq_to_four_BE s) / pow2 (8 * (4 - n))) * pow2 (8 * (4 - n)))
  =
  if n <= 2 then lemma_pad_to_32_bits_helper s s'' n else
  assert (n == 3 \/ n == 4);
  assert_norm (four_to_nat 8 (seq_to_four_BE s) == four_to_nat_unfold 8 (seq_to_four_BE s));
  assert_norm (four_to_nat 8 (seq_to_four_BE s'') == four_to_nat_unfold 8 (seq_to_four_BE s''));
  assert_norm (pow2 (0 * 8) == 1);
  assert_norm (pow2 (1 * 8) == 0x100);
  let x = four_to_nat 8 (seq_to_four_BE s'') in
  assert (n == 3 ==> x / pow2 (8 * (4 - n)) == x / 0x100);
  assert (n == 4 ==> x / pow2 (8 * (4 - n)) == x / 0x1);
  assert_norm (((x / pow2 (8 * 1)) * pow2 (8 * 1)) % pow2 (8 * 1) == 0);
  assert_norm (((x / pow2 (8 * 0)) * pow2 (8 * 0)) % pow2 (8 * 0) == 0);
  ()

let lemma_div_n_8_upper1 (q:quad32) (n:nat) : Lemma
  (requires n <= 4)
  (ensures ((hi64 q / pow2 (8 * (8 - n))) * pow2 (8 * (8 - n))) / pow2_32 == (q.hi3 / pow2 (8 * (4 - n))) * pow2 (8 * (4 - n)))
  =
  hi64_reveal ();
  let Mkfour _ _ _ _ = q in // avoid ifuel
  let f (n:nat{n <= 4}) = ((hi64_def q / pow2 (8 * (8 - n))) * pow2 (8 * (8 - n))) / pow2_32 == (q.hi3 / pow2 (8 * (4 - n))) * pow2 (8 * (4 - n)) in
  assert_norm (f 0);
  assert_norm (f 1);
  assert_norm (f 2);
  assert_norm (f 3);
  assert_norm (f 4);
  ()

let lemma_div_n_8_upper2_helper (q:quad32) (n:nat) : Lemma
  (requires n <= 2)
  (ensures (hi64 q / pow2 (8 * (4 - n))) * pow2 (8 * (4 - n)) == 0x100000000 * q.hi3 + (q.hi2 / pow2 (8 * (4 - n))) * pow2 (8 * (4 - n)))
  =
  hi64_reveal ();
  let Mkfour _ _ _ _ = q in // avoid ifuel
  let f (n:nat{n <= 4}) = (hi64_def q / pow2 (8 * (4 - n))) * pow2 (8 * (4 - n)) == 0x100000000 * q.hi3 + (q.hi2 / pow2 (8 * (4 - n))) * pow2 (8 * (4 - n)) in
  assert_norm (f 2);
  assert_norm (f 1);
  assert_norm (f 0);
  ()

let lemma_div_n_8_upper2 (q:quad32) (n:nat) : Lemma
  (requires n <= 4)
  (ensures (hi64 q / pow2 (8 * (4 - n))) * pow2 (8 * (4 - n)) == 0x100000000 * q.hi3 + (q.hi2 / pow2 (8 * (4 - n))) * pow2 (8 * (4 - n)))
  =
  hi64_reveal ();
  if n <= 2 then lemma_div_n_8_upper2_helper q n else
  let Mkfour _ _ _ _ = q in // avoid ifuel
  let f (n:nat{n <= 4}) = (hi64_def q / pow2 (8 * (4 - n))) * pow2 (8 * (4 - n)) == 0x100000000 * q.hi3 + (q.hi2 / pow2 (8 * (4 - n))) * pow2 (8 * (4 - n)) in
  assert_norm (f 4);
  assert_norm (f 3);
  ()

let lemma_div_n_8_lower1 (q:quad32) (n:nat) : Lemma
  (requires n <= 4)
  (ensures ((lo64 q / pow2 (8 * (8 - n))) * pow2 (8 * (8 - n))) / pow2_32 == (q.lo1 / pow2 (8 * (4 - n))) * pow2 (8 * (4 - n)))
  =
  hi64_reveal ();
  lo64_reveal ();
  let Mkfour q0 q1 _ _ = q in
  lemma_div_n_8_upper1 (Mkfour 0 0 q0 q1) n

let lemma_div_n_8_lower2 (q:quad32) (n:nat) : Lemma
  (requires n <= 4)
  (ensures (lo64 q / pow2 (8 * (4 - n))) * pow2 (8 * (4 - n)) == 0x100000000 * q.lo1 + (q.lo0 / pow2 (8 * (4 - n))) * pow2 (8 * (4 - n)))
  =
  hi64_reveal ();
  lo64_reveal ();
  let Mkfour q0 q1 _ _ = q in
  lemma_div_n_8_upper2 (Mkfour 0 0 q0 q1) n

let lemma_64_32_hi1 (q':quad32) (hi hi':nat64) (n:nat) : Lemma
  (requires
    n <= 4 /\
    hi' == (hi / pow2 (8 * (8 - n))) * pow2 (8 * (8 - n)) /\
    four_to_two_two q' == Mktwo (nat_to_two 32 0) (nat_to_two 32 hi')
  )
  (ensures hi' % pow2_32 == 0 /\ hi' / pow2_32 == q'.hi3 /\ q' == Mkfour 0 0 0 q'.hi3)
  =
  assert_norm (((hi / pow2 (8 * 4)) * pow2 (8 * 4)) % pow2_32 == 0);
  assert_norm (((hi / pow2 (8 * 5)) * pow2 (8 * 5)) % pow2_32 == 0);
  assert_norm (((hi / pow2 (8 * 6)) * pow2 (8 * 6)) % pow2_32 == 0);
  assert_norm (((hi / pow2 (8 * 7)) * pow2 (8 * 7)) % pow2_32 == 0);
  assert_norm (((hi / pow2 (8 * 8)) * pow2 (8 * 8)) % pow2_32 == 0);
  assert_norm ((((hi / pow2 (8 * (8 - n))) * pow2 (8 * (8 - n))) / pow2_32) % pow2_32 ==
    ((hi / pow2 (8 * (8 - n))) * pow2 (8 * (8 - n))) / pow2_32);
  assert_norm (nat_to_two 32 hi' == nat_to_two_unfold 32 hi');
  assert_norm (nat_to_two 32 0 == nat_to_two_unfold 32 0);
  ()

let lemma_64_32_hi2 (q':quad32) (hi hi':nat64) (n:nat) : Lemma
  (requires
    n <= 4 /\
    hi' == (hi / pow2 (8 * (4 - n))) * pow2 (8 * (4 - n)) /\
    four_to_two_two q' == Mktwo (nat_to_two 32 0) (nat_to_two 32 hi')
  )
  (ensures hi' == 0x100000000 * q'.hi3 + q'.hi2 /\ q' == Mkfour 0 0 q'.hi2 q'.hi3)
  =
  assert_norm (nat_to_two 32 hi' == nat_to_two_unfold 32 hi');
  assert_norm (nat_to_two 32 0 == nat_to_two_unfold 32 0);
  ()

let lemma_64_32_lo1 (q':quad32) (lo lo':nat64) (n:nat) : Lemma
  (requires
    n <= 4 /\
    lo' == (lo / pow2 (8 * (8 - n))) * pow2 (8 * (8 - n)) /\
    four_to_two_two q' == Mktwo (nat_to_two 32 lo') (Mktwo q'.hi2 q'.hi3)
  )
  (ensures lo' % pow2_32 == 0 /\ lo' / pow2_32 == q'.lo1 /\ q'.lo0 == 0)
  =
  assert_norm (((lo / pow2 (8 * 4)) * pow2 (8 * 4)) % pow2_32 == 0);
  assert_norm (((lo / pow2 (8 * 5)) * pow2 (8 * 5)) % pow2_32 == 0);
  assert_norm (((lo / pow2 (8 * 6)) * pow2 (8 * 6)) % pow2_32 == 0);
  assert_norm (((lo / pow2 (8 * 7)) * pow2 (8 * 7)) % pow2_32 == 0);
  assert_norm (((lo / pow2 (8 * 8)) * pow2 (8 * 8)) % pow2_32 == 0);
  assert_norm (((lo / pow2 (8 * (8 - n))) * pow2 (8 * (8 - n)) / pow2_32) % pow2_32 ==
    ((lo / pow2 (8 * (8 - n))) * pow2 (8 * (8 - n))) / pow2_32);
  assert_norm (nat_to_two 32 lo' == nat_to_two_unfold 32 lo');
  ()

let lemma_64_32_lo2 (q':quad32) (lo lo':nat64) (n:nat) : Lemma
  (requires
    n <= 4 /\
    lo' == (lo / pow2 (8 * (4 - n))) * pow2 (8 * (4 - n)) /\
    four_to_two_two q' == Mktwo (nat_to_two 32 lo') (Mktwo q'.hi2 q'.hi3)
  )
  (ensures lo' == q'.lo0 + 0x100000000 * q'.lo1)
  =
  assert_norm (nat_to_two 32 lo' == nat_to_two_unfold 32 lo');
  ()

let lemma_slices_be_bytes_to_quad32 (s:seq16 nat8) : Lemma
  (ensures (
    let q = be_bytes_to_quad32 s in
    q.hi3 == four_to_nat 8 (seq_to_four_BE (slice s 0 4)) /\
    q.hi2 == four_to_nat 8 (seq_to_four_BE (slice s 4 8)) /\
    q.lo1 == four_to_nat 8 (seq_to_four_BE (slice s 8 12)) /\
    q.lo0 == four_to_nat 8 (seq_to_four_BE (slice s 12 16))
  ))
  =
  reveal_opaque (`%seq_to_seq_four_BE) (seq_to_seq_four_BE #nat8);
  be_bytes_to_quad32_reveal ();
  ()

let lemma_four_zero (_:unit) : Lemma
  (ensures four_to_nat 8 (seq_to_four_BE (create 4 0)) == 0)
  =
  let s = create 4 0 in
  assert_norm (four_to_nat 8 (seq_to_four_BE s) == four_to_nat_unfold 8 (seq_to_four_BE s));
  ()

let pad_to_128_bits_upper (q:quad32) (num_bytes:int) =
  let n = num_bytes in
  let new_hi = ((hi64 q / pow2 ((8 - n) * 8)) * pow2 ((8 - n) * 8)) % pow2_64 in
  hi64_reveal ();
  let f (n:nat{1 <= n /\ n < 8}) = (hi64_def q / pow2 ((8 - n) * 8)) * pow2 ((8 - n) * 8) == ((hi64_def q / pow2 ((8 - n) * 8)) * pow2 ((8 - n) * 8)) % pow2_64 in
  assert_norm (f 1);
  assert_norm (f 2);
  assert_norm (f 3);
  assert_norm (f 4);
  assert_norm (f 5);
  assert_norm (f 6);
  assert_norm (f 7);
  assert (((hi64 q) / pow2 ((8 - n) * 8)) * pow2 ((8 - n) * 8) == (((hi64 q) / pow2 ((8 - n) * 8)) * pow2 ((8 - n) * 8)) % pow2_64);
  let s = be_quad32_to_bytes q in
  let s' = slice s 0 n in
  let q' = two_two_to_four (Mktwo (nat_to_two 32 0) (nat_to_two 32 new_hi)) in
  let s'' = pad_to_128_bits s' in
  let q'' = be_bytes_to_quad32 s'' in

  let s0_4 = slice s 0 4 in
  let s4_8 = slice s 4 8 in
  let s8_12 = slice s 8 12 in
  let s12_16 = slice s 12 16 in
  let s0_4'' = slice s'' 0 4 in
  let s4_8'' = slice s'' 4 8 in
  let s8_12'' = slice s'' 8 12 in
  let s12_16'' = slice s'' 12 16 in

  if n < 4 then
  (
    lemma_div_n_8_upper1 q n;
    lemma_64_32_hi1 q' (hi64 q) new_hi n;
    lemma_pad_to_32_bits s0_4 s0_4'' n;
    ()
  )
  else
  (
    lemma_div_n_8_upper2 q (n - 4);
    lemma_64_32_hi2 q' (hi64 q) new_hi (n - 4);
    lemma_pad_to_32_bits s4_8 s4_8'' (n - 4);
    ()
  );
  
  lemma_slices_be_quad32_to_bytes q;
  lemma_slices_be_bytes_to_quad32 s'';

  lemma_four_zero ();
  let zero_4 : seq nat8 = create 4 0 in
  assert (n < 4 ==> equal s4_8'' zero_4);
  assert (equal s8_12'' zero_4);
  assert (equal s12_16'' zero_4);
  ()

let pad_to_128_bits_lower (q:quad32) (num_bytes:int) =
  let n = num_bytes in
  let new_lo = (((lo64 q) / pow2 ((16 - n) * 8)) * pow2 ((16 - n) * 8)) % pow2_64 in
  lo64_reveal ();
  hi64_reveal ();
  let f (n:nat{8 <= n /\ n < 16}) = (lo64_def q / pow2 ((16 - n) * 8)) * pow2 ((16 - n) * 8) == ((lo64_def q / pow2 ((16 - n) * 8)) * pow2 ((16 - n) * 8)) % pow2_64 in
  assert_norm (f 8);
  assert_norm (f 9);
  assert_norm (f 10);
  assert_norm (f 11);
  assert_norm (f 12);
  assert_norm (f 13);
  assert_norm (f 14);
  assert_norm (f 15);
  assert (((lo64 q) / pow2 ((16 - n) * 8)) * pow2 ((16 - n) * 8) == (((lo64 q) / pow2 ((16 - n) * 8)) * pow2 ((16 - n) * 8)) % pow2_64);
  let s = be_quad32_to_bytes q in
  let s' = slice s 0 n in
  let q' = two_two_to_four (Mktwo (nat_to_two 32 new_lo) (nat_to_two 32 (hi64 q))) in
  let s'' = pad_to_128_bits s' in
  let q'' = be_bytes_to_quad32 s'' in

  let s0_4 = slice s 0 4 in
  let s4_8 = slice s 4 8 in
  let s8_12 = slice s 8 12 in
  let s12_16 = slice s 12 16 in
  let s0_4'' = slice s'' 0 4 in
  let s4_8'' = slice s'' 4 8 in
  let s8_12'' = slice s'' 8 12 in
  let s12_16'' = slice s'' 12 16 in

  let Mkfour q0 q1 q2 q3 = q in
  let Mkfour q0' q1' q2' q3' = q' in
  let Mkfour q0'' q1'' q2'' q3'' = q'' in

  if n < 12 then
  (
    lemma_div_n_8_lower1 q (n - 8);
    lemma_64_32_lo1 q' (lo64 q) new_lo (n - 8);
    lemma_pad_to_32_bits s8_12 s8_12'' (n - 8);
    ()
  )
  else
  (
    lemma_div_n_8_lower2 q (n - 12);
    lemma_64_32_lo2 q' (lo64 q) new_lo (n - 12);
    lemma_pad_to_32_bits s12_16 s12_16'' (n - 12);
    ()
  );

  lemma_slices_be_quad32_to_bytes q;
  lemma_slices_be_bytes_to_quad32 s'';

  lemma_four_zero ();
  let zero_4 : seq nat8 = create 4 0 in
  assert (n < 12 ==> equal s12_16'' zero_4);
  ()

let pad_to_128_bits_lower_8 (q:quad32) =
  small_division_lemma_1 (lo64 q) (pow2 64);
  pad_to_128_bits_lower q 8
