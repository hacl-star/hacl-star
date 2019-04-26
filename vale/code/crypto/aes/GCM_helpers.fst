module GCM_helpers

open FStar.Tactics
open Words_s
open Words.Seq_s
open Types_s
open Arch.Types
open FStar.Mul
open FStar.Seq
open Opaque_s
open Words.Two_s
open Words.Four_s
open AES_s
open GCTR_s
open FStar.Math.Lemmas
open Collections.Seqs

let reveal_le_bytes_to_seq_quad32 () =
  FStar.Pervasives.reveal_opaque (`%le_bytes_to_seq_quad32) le_bytes_to_seq_quad32

let extra_bytes_helper (n:nat) : Lemma
  (requires n % 16 <> 0)
  (ensures bytes_to_quad_size n == n / 16 + 1)
  =
  ()

#reset-options "--smtencoding.elim_box true --z3rlimit 25 --max_ifuel 1 --initial_fuel 0 --max_fuel 1"
let bytes_to_quad_size_no_extra_bytes num_bytes = ()

let no_extra_bytes_helper s num_bytes =
  assert (slice (le_seq_quad32_to_bytes s) 0 num_bytes == le_seq_quad32_to_bytes s); // TODO: this shouldn't be necessary
  ()

let le_seq_quad32_to_bytes_tail_prefix (s:seq quad32) (num_bytes:nat) =
  let num_extra = num_bytes % 16 in
  let num_blocks = num_bytes / 16 in
  let final = index s num_blocks in
  let x  = slice (le_seq_quad32_to_bytes s) (num_blocks * 16) num_bytes in
  let x' = slice (le_quad32_to_bytes final) 0 num_extra in

  le_seq_quad32_to_bytes_of_singleton final;
  assert (le_quad32_to_bytes final == le_seq_quad32_to_bytes (create 1 final));
  assert (equal (create 1 final) (slice s num_blocks (length s)));

  assert (x' == slice (le_seq_quad32_to_bytes (slice s num_blocks (length s))) 0 num_extra);
  slice_commutes_le_seq_quad32_to_bytes s num_blocks (length s);
  assert (x' == slice (slice (le_seq_quad32_to_bytes s) (num_blocks * 16) (length s * 16)) 0 num_extra);
  assert (x' == slice (le_seq_quad32_to_bytes s) (num_blocks * 16) num_bytes);

  assert (equal x' x);
  ()

let index_helper (s:seq quad32) (num_bytes:int) : Lemma
  (requires 1 <= num_bytes /\
             num_bytes < 16 * length s /\
             16 * (length s - 1) < num_bytes /\
             num_bytes % 16 <> 0 /\
             length s == bytes_to_quad_size num_bytes)
  (ensures (let num_blocks = num_bytes / 16 in
            index s num_blocks == index_work_around_quad32 (slice_work_around s (bytes_to_quad_size num_bytes)) num_blocks))
  =
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

let pad_to_128_bits_le_quad32_to_bytes (s:seq quad32) (num_bytes:int) =
  let num_extra = num_bytes % 16 in
  let num_blocks = num_bytes / 16 in
  let full_quads,final_quads = split s num_blocks in
  assert(length final_quads == 1);
  let final_quad = index final_quads 0 in
  let b = slice (le_seq_quad32_to_bytes s) 0 num_bytes in
  pad_to_128_bits_multiples b; // ==>  pad_to_128_bits b == full_bytes @| pad_to_128_bits partial_bytes
  let full_blocks = (length b) / 16 * 16 in
  let full_bytes, partial_bytes = split b full_blocks in
  // Need to show that full_bytes == le_seq_quad32_to_bytes full_quads
  // Need to show that le_quad32_to_bytes final_quad == partial_bytes

  // full_bytes == slice (slice (le_seq_quad32_to_bytes s) 0 num_bytes) 0 full_blocks
  // This should be from slice_slice
  //            == slice (le_seq_quad32_bot_bytes s) 0 full_blocks
  //            == slice (le_seq_quad32_bot_bytes s) 0 (num_blocks * 16)
  //    This follows from slice_commutes_le_seq_quad32_to_bytes0
  // le_seq_quad32_to_bytes full_quads == le_seq_quad32_to_bytes (slice s 0 num_blocks)

  slice_commutes_le_seq_quad32_to_bytes0 s num_blocks;
  // ==>
  (*
    assert (slice (le_seq_quad32_to_bytes s) 0 (num_blocks * 16) ==
            le_seq_quad32_to_bytes (slice s 0 num_blocks));
  *)
  slice_slice (le_seq_quad32_to_bytes s) 0 num_bytes 0 full_blocks;
  assert (full_bytes == le_seq_quad32_to_bytes full_quads);

  // slice (le_quad32_to_bytes final_quad) 0 num_extra == slice (le_quad32_to_bytes (index (slice s num_blocks (length s)) 0)) 0 num_extra
  // F* believes assert (final_quad == index s num_blocks), so we have:
  //               == slice (le_quad32_to_bytes (index s num_blocks)) 0 num_extra
  //
  //               == slice (le_quad32_to_bytes (index s num_blocks)) 0 num_extra
  // from le_seq_quad32_to_bytes_tail_prefix
  //               == slice (le_seq_quad32_to_bytes s) (num_blocks * 16) num_bytes
  //               == slice (le_seq_quad32_to_bytes s) full_blocks num_bytes
  //  From slice_slice
  // partial_bytes == slice (slice (le_seq_quad32_to_bytes s) 0 num_bytes) full_blocks num_bytes

  slice_slice (le_seq_quad32_to_bytes s) 0 num_bytes full_blocks num_bytes;
  le_seq_quad32_to_bytes_tail_prefix s num_bytes;
  ()


(*
let slice_le_quad32_to_bytes_is_mod (q:quad32) (num_bytes:int) : Lemma
  (requires 1 <= num_bytes /\ num_bytes < 16)
  (ensures four_to_nat 32 (slice (le_quad32_to_bytes q) 0 num_bytes) == (four_to_nat 32 q) % (pow2 (8*num_bytes)))
  =
  ()

let insert_0_is_padding (q:quad32) :
  Lemma (let q' = insert_nat64 q 0 1 in
         q' == le_bytes_to_quad32 (pad_to_128_bits (slice (le_quad32_to_bytes q) 0 8)))
  =
  ()
*)


#reset-options "--z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3 --z3cliopt smt.arith.nl=true --max_fuel 2 --initial_fuel 2 --max_ifuel 0 --smtencoding.elim_box true --smtencoding.nl_arith_repr native --z3rlimit 10"
let le_quad32_to_bytes_sel (q : quad32) (i:nat{i < 16}) =
  FStar.Pervasives.reveal_opaque (`%le_quad32_to_bytes) le_quad32_to_bytes;
  let Mkfour q0 q1 q2 q3 = q in
  assert (index (Words.Seq_s.four_to_seq_LE q) 0 == q0);
  assert (index (Words.Seq_s.four_to_seq_LE q) 1 == q1);
  assert (index (Words.Seq_s.four_to_seq_LE q) 2 == q2);
  assert (index (Words.Seq_s.four_to_seq_LE q) 3 == q3);
  let Mkfour q00 q01 q02 q03 = nat_to_four 8 q0 in
  let Mkfour q10 q11 q12 q13 = nat_to_four 8 q1 in
  let Mkfour q20 q21 q22 q23 = nat_to_four 8 q2 in
  let Mkfour q30 q31 q32 q33 = nat_to_four 8 q3 in
  assert_by_tactic (four_select (nat_to_four 8 q0) 0 == q00)
    (fun () -> norm[delta_only ["Words.Four_s.four_select"]]);
  assert_by_tactic (four_select (nat_to_four 8 q0) 1 == q01)
    (fun () -> norm[delta_only ["Words.Four_s.four_select"]]);
  assert_by_tactic (four_select (nat_to_four 8 q0) 2 == q02)
    (fun () -> norm[delta_only ["Words.Four_s.four_select"]]);
  assert_by_tactic (four_select (nat_to_four 8 q0) 3 == q03)
    (fun () -> norm[delta_only ["Words.Four_s.four_select"]]);

  assert_by_tactic (four_select (nat_to_four 8 q1) 0 == q10)
    (fun () -> norm[delta_only ["Words.Four_s.four_select"]]);
  assert_by_tactic (four_select (nat_to_four 8 q1) 1 == q11)
    (fun () -> norm[delta_only ["Words.Four_s.four_select"]]);
  assert_by_tactic (four_select (nat_to_four 8 q1) 2 == q12)
    (fun () -> norm[delta_only ["Words.Four_s.four_select"]]);
  assert_by_tactic (four_select (nat_to_four 8 q1) 3 == q13)
    (fun () -> norm[delta_only ["Words.Four_s.four_select"]]);

  assert_by_tactic (four_select (nat_to_four 8 q2) 0 == q20)
    (fun () -> norm[delta_only ["Words.Four_s.four_select"]]);
  assert_by_tactic (four_select (nat_to_four 8 q2) 1 == q21)
    (fun () -> norm[delta_only ["Words.Four_s.four_select"]]);
  assert_by_tactic (four_select (nat_to_four 8 q2) 2 == q22)
    (fun () -> norm[delta_only ["Words.Four_s.four_select"]]);
  assert_by_tactic (four_select (nat_to_four 8 q2) 3 == q23)
    (fun () -> norm[delta_only ["Words.Four_s.four_select"]]);

  assert_by_tactic (four_select (nat_to_four 8 q3) 0 == q30)
    (fun () -> norm[delta_only ["Words.Four_s.four_select"]]);
  assert_by_tactic (four_select (nat_to_four 8 q3) 1 == q31)
    (fun () -> norm[delta_only ["Words.Four_s.four_select"]]);
  assert_by_tactic (four_select (nat_to_four 8 q3) 2 == q32)
    (fun () -> norm[delta_only ["Words.Four_s.four_select"]]);
  assert_by_tactic (four_select (nat_to_four 8 q3) 3 == q33)
    (fun () -> norm[delta_only ["Words.Four_s.four_select"]]);

  assert(i < 4 ==> (fun n ->
    four_select (index (init (length (four_to_seq_LE q))
                       (fun x -> nat_to_four 8 (index (four_to_seq_LE q) x)))
                            (n / 4))
                       (n % 4)) i == four_select (nat_to_four 8 q0) i);
  assert(4 <= i /\ i < 8 ==> (fun n ->
    four_select (index (init (length (four_to_seq_LE q))
                (fun x -> nat_to_four 8 (index (four_to_seq_LE q) x)))
                (n / 4))
                   (n % 4)) i == four_select (nat_to_four 8 q1) (i % 4));
  assert(8 <= i /\ i < 12 ==> (fun n ->
    four_select (index (init (length (four_to_seq_LE q))
                (fun x -> nat_to_four 8 (index (four_to_seq_LE q) x)))
                (n / 4))
                   (n % 4)) i == four_select (nat_to_four 8 q2) (i % 4));
  assert(12 <= i /\ i < 16 ==> (fun n ->
    four_select (index (init (length (four_to_seq_LE q))
                (fun x -> nat_to_four 8 (index (four_to_seq_LE q) x)))
                (n / 4))
                   (n % 4)) i == four_select (nat_to_four 8 q3) (i % 4));
  assert_by_tactic (i < 16 ==> index (le_quad32_to_bytes q) i =
                   (index (init (length (init (length (four_to_seq_LE q))
                          (fun x -> nat_to_four 8 (index (four_to_seq_LE q) x))) *
                                                                      4)
                          (fun n ->
                            four_select (index (init (length (four_to_seq_LE q))
                                        (fun x -> nat_to_four 8 (index (four_to_seq_LE q) x)))
                            (n / 4))
                          (n % 4))) i))
                       (fun () -> norm[primops; delta_only ["Types_s.le_quad32_to_bytes";
                          "Collections.Seqs_s.seq_map"; "Collections.Seqs_s.compose";
                            "Words.Seq_s.seq_four_to_seq_LE"]]; dump " after norm2");
  assert(i < 4 ==> index (le_quad32_to_bytes q) i == four_select (nat_to_four 8 q0) i);
  assert(4 <= i /\ i < 8 ==> index (le_quad32_to_bytes q) i == four_select (nat_to_four 8 q1) (i % 4));
  assert(8 <= i /\ i < 12 ==> index (le_quad32_to_bytes q) i == four_select (nat_to_four 8 q2) (i % 4));
  assert(12 <= i /\ i < 16 ==> index (le_quad32_to_bytes q) i == four_select (nat_to_four 8 q3) (i % 4))


#reset-options "--smtencoding.elim_box true --z3rlimit 60 --z3refresh --initial_ifuel 0 --max_ifuel 1 --initial_fuel 1 --max_fuel 1"
let lemma_pad_to_32_bits_helper (s s'':seq4 nat8) (n:nat) : Lemma
  (requires
    n <= 2 /\
    (forall (i:nat).{:pattern (index s i) \/ (index s'' i)} i < 4 ==>
      index s'' i == (if i < n then index s i else 0))
  )
  (ensures four_to_nat 8 (seq_to_four_LE s'') == four_to_nat 8 (seq_to_four_LE s) % pow2 (8 * n))
  =
  assert (n == 0 \/ n == 1 \/ n == 2);
  assert_norm (four_to_nat 8 (seq_to_four_LE s) == four_to_nat_unfold 8 (seq_to_four_LE s));
  assert_norm (four_to_nat 8 (seq_to_four_LE s'') == four_to_nat_unfold 8 (seq_to_four_LE s''));
  assert_norm (pow2 (0 * 8) == 1);
  assert_norm (pow2 (1 * 8) == 0x100);
  assert_norm (pow2 (2 * 8) == 0x10000);
  assert_norm (pow2 (3 * 8) == 0x1000000);
  assert_norm (pow2 (4 * 8) == 0x100000000);
  let x = four_to_nat 8 (seq_to_four_LE s'') in
  assert (n == 0 ==> x % pow2 (8 * n) == x % 0x1);
  assert (n == 1 ==> x % pow2 (8 * n) == x % 0x100);
  assert (n == 2 ==> x % pow2 (8 * n) == x % 0x10000);
  ()

let lemma_pad_to_32_bits (s s'':seq4 nat8) (n:nat) : Lemma
  (requires
    n <= 4 /\
    (forall (i:nat).{:pattern (index s i) \/ (index s'' i)} i < 4 ==>
      index s'' i == (if i < n then index s i else 0))
  )
  (ensures four_to_nat 8 (seq_to_four_LE s'') == four_to_nat 8 (seq_to_four_LE s) % pow2 (8 * n))
  =
  if n <= 2 then lemma_pad_to_32_bits_helper s s'' n else
  assert (n == 3 \/ n == 4);
  assert_norm (four_to_nat 8 (seq_to_four_LE s) == four_to_nat_unfold 8 (seq_to_four_LE s));
  assert_norm (four_to_nat 8 (seq_to_four_LE s'') == four_to_nat_unfold 8 (seq_to_four_LE s''));
  assert_norm (pow2 (0 * 8) == 1);
  assert_norm (pow2 (1 * 8) == 0x100);
  assert_norm (pow2 (2 * 8) == 0x10000);
  assert_norm (pow2 (3 * 8) == 0x1000000);
  assert_norm (pow2 (4 * 8) == 0x100000000);
  let x = four_to_nat 8 (seq_to_four_LE s'') in
  assert (n == 3 ==> x % pow2 (8 * n) == x % 0x1000000);
  assert (n == 4 ==> x % pow2 (8 * n) == x % 0x100000000);
  ()

let lemma_mod_n_8_lower1 (q:quad32) (n:nat) : Lemma
  (requires n <= 4)
  (ensures lo64 q % pow2 (8 * n) == q.lo0 % pow2 (8 * n))
  =
  reveal_opaque lo64_def;
  let Mkfour _ _ _ _ = q in // avoid ifuel
  let f (n:nat{n <= 4}) = lo64_def q % pow2 (8 * n) == q.lo0 % pow2 (8 * n) in
  assert_norm (f 0);
  assert_norm (f 1);
  assert_norm (f 2);
  assert_norm (f 3);
  assert_norm (f 4);
  ()

let lemma_mod_n_8_lower2_helper (q:quad32) (n:nat) : Lemma
  (requires n <= 2)
  (ensures lo64 q % pow2 (8 * (4 + n)) == q.lo0 + 0x100000000 * (q.lo1 % pow2 (8 * n)))
  =
  reveal_opaque lo64_def;
  let Mkfour _ _ _ _ = q in // avoid ifuel
  let f (n:nat{n <= 4}) = lo64_def q % pow2 (8 * (4 + n)) == q.lo0 + 0x100000000 * (q.lo1 % pow2 (8 * n)) in
  assert_norm (f 2);
  assert_norm (f 1);
  assert_norm (f 0);
  ()

let lemma_mod_n_8_lower2 (q:quad32) (n:nat) : Lemma
  (requires n <= 4)
  (ensures lo64 q % pow2 (8 * (4 + n)) == q.lo0 + 0x100000000 * (q.lo1 % pow2 (8 * n)))
  =
  reveal_opaque lo64_def;
  if n <= 2 then lemma_mod_n_8_lower2_helper q n else
  let Mkfour _ _ _ _ = q in // avoid ifuel
  let f (n:nat{n <= 4}) = lo64_def q % pow2 (8 * (4 + n)) == q.lo0 + 0x100000000 * (q.lo1 % pow2 (8 * n)) in
  assert_norm (f 4);
  assert_norm (f 3);
  ()

let lemma_mod_n_8_upper1 (q:quad32) (n:nat) : Lemma
  (requires n <= 4)
  (ensures hi64 q % pow2 (8 * n) == q.hi2 % pow2 (8 * n))
  =
  reveal_opaque hi64_def;
  reveal_opaque lo64_def;
  let Mkfour _ _ q2 q3 = q in
  lemma_mod_n_8_lower1 (Mkfour q2 q3 0 0) n

let lemma_mod_n_8_upper2 (q:quad32) (n:nat) : Lemma
  (requires n <= 4)
  (ensures hi64 q % pow2 (8 * (4 + n)) == q.hi2 + 0x100000000 * (q.hi3 % pow2 (8 * n)))
  =
  reveal_opaque hi64_def;
  reveal_opaque lo64_def;
  let Mkfour _ _ q2 q3 = q in
  lemma_mod_n_8_lower2 (Mkfour q2 q3 0 0) n

let lemma_64_32_lo1 (q':quad32) (lo lo':nat64) (n:nat) : Lemma
  (requires
    n <= 4 /\
    lo' == lo % pow2 (8 * n) /\
    four_to_two_two q' == Mktwo (nat_to_two 32 lo') (nat_to_two 32 0)
  )
  (ensures lo' < 0x100000000 /\ lo' == q'.lo0 /\ q' == Mkfour q'.lo0 0 0 0)
  =
  assert_norm (pow2 (0 * 8) == 1);
  assert_norm (pow2 (1 * 8) == 0x100);
  assert_norm (pow2 (2 * 8) == 0x10000);
  assert_norm (pow2 (3 * 8) == 0x1000000);
  assert_norm (pow2 (4 * 8) == 0x100000000);
  assert_norm (nat_to_two 32 lo' == nat_to_two_unfold 32 lo');
  assert_norm (nat_to_two 32 0 == nat_to_two_unfold 32 0);
  ()

let lemma_64_32_lo2 (q':quad32) (lo lo':nat64) (n:nat) : Lemma
  (requires
    n <= 4 /\
    lo' == lo % pow2 (8 * (n + 4)) /\
    four_to_two_two q' == Mktwo (nat_to_two 32 lo') (nat_to_two 32 0)
  )
  (ensures lo' == q'.lo0 + 0x100000000 * q'.lo1 /\ q' == Mkfour q'.lo0 q'.lo1 0 0)
  =
  assert_norm (pow2 (4 * 8) == 0x100000000);
  assert_norm (pow2 (5 * 8) == 0x10000000000);
  assert_norm (pow2 (6 * 8) == 0x1000000000000);
  assert_norm (pow2 (7 * 8) == 0x100000000000000);
  assert_norm (pow2 (8 * 8) == 0x10000000000000000);
  assert_norm (nat_to_two 32 lo' == nat_to_two_unfold 32 lo');
  assert_norm (nat_to_two 32 0 == nat_to_two_unfold 32 0);
  ()

let lemma_64_32_hi1 (q':quad32) (hi hi':nat64) (n:nat) : Lemma
  (requires
    n <= 4 /\
    hi' == hi % pow2 (8 * n) /\
    four_to_two_two q' == Mktwo (Mktwo q'.lo0 q'.lo1) (nat_to_two 32 hi')
  )
  (ensures hi' < 0x100000000 /\ hi' == q'.hi2 /\ q'.hi3 == 0)
  =
  assert_norm (pow2 (0 * 8) == 1);
  assert_norm (pow2 (1 * 8) == 0x100);
  assert_norm (pow2 (2 * 8) == 0x10000);
  assert_norm (pow2 (3 * 8) == 0x1000000);
  assert_norm (pow2 (4 * 8) == 0x100000000);
  assert_norm (nat_to_two 32 hi' == nat_to_two_unfold 32 hi');
  ()

let lemma_64_32_hi2 (q':quad32) (hi hi':nat64) (n:nat) : Lemma
  (requires
    n <= 4 /\
    hi' == hi % pow2 (8 * (n + 4)) /\
    four_to_two_two q' == Mktwo (Mktwo q'.lo0 q'.lo1) (nat_to_two 32 hi')
  )
  (ensures hi' == q'.hi2 + 0x100000000 * q'.hi3)
  =
  assert_norm (pow2 (4 * 8) == 0x100000000);
  assert_norm (pow2 (5 * 8) == 0x10000000000);
  assert_norm (pow2 (6 * 8) == 0x1000000000000);
  assert_norm (pow2 (7 * 8) == 0x100000000000000);
  assert_norm (pow2 (8 * 8) == 0x10000000000000000);
  assert_norm (nat_to_two 32 hi' == nat_to_two_unfold 32 hi');
  ()

let lemma_slices_le_quad32_to_bytes (q:quad32) : Lemma
  (ensures (
    let s = le_quad32_to_bytes q in
    q.lo0 == four_to_nat 8 (seq_to_four_LE (slice s 0 4)) /\
    q.lo1 == four_to_nat 8 (seq_to_four_LE (slice s 4 8)) /\
    q.hi2 == four_to_nat 8 (seq_to_four_LE (slice s 8 12)) /\
    q.hi3 == four_to_nat 8 (seq_to_four_LE (slice s 12 16))
  ))
  =
  FStar.Pervasives.reveal_opaque (`%le_quad32_to_bytes) le_quad32_to_bytes;
  ()

let lemma_slices_le_bytes_to_quad32 (s:seq16 nat8) : Lemma
  (ensures (
    let q = le_bytes_to_quad32 s in
    q.lo0 == four_to_nat 8 (seq_to_four_LE (slice s 0 4)) /\
    q.lo1 == four_to_nat 8 (seq_to_four_LE (slice s 4 8)) /\
    q.hi2 == four_to_nat 8 (seq_to_four_LE (slice s 8 12)) /\
    q.hi3 == four_to_nat 8 (seq_to_four_LE (slice s 12 16))
  ))
  =
  reveal_opaque le_bytes_to_quad32_def;
  ()

let lemma_four_zero (_:unit) : Lemma
  (ensures four_to_nat 8 (seq_to_four_LE (create 4 0)) == 0)
  =
  let s = create 4 0 in
  assert_norm (four_to_nat 8 (seq_to_four_LE s) == four_to_nat_unfold 8 (seq_to_four_LE s));
  ()

let pad_to_128_bits_lower (q:quad32) (num_bytes:int) =
  let n = num_bytes in
  let new_lo = (lo64 q) % pow2 (n * 8) in
  pow2_lt_compat 64 (n * 8);
  let s = le_quad32_to_bytes q in
  let s' = slice s 0 n in
  let q' = insert_nat64 (insert_nat64 q 0 1) new_lo 0 in
  reveal_opaque insert_nat64;
  let s'' = pad_to_128_bits s' in
  let q'' = le_bytes_to_quad32 s'' in

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

  if n < 4 then
  (
    lemma_mod_n_8_lower1 q n;
    lemma_64_32_lo1 q' (lo64 q) new_lo n;
    lemma_pad_to_32_bits s0_4 s0_4'' n;
    ()
  )
  else
  (
    lemma_mod_n_8_lower2 q (n - 4);
    lemma_64_32_lo2 q' (lo64 q) new_lo (n - 4);
    lemma_pad_to_32_bits s4_8 s4_8'' (n - 4);
    ()
  );

  lemma_slices_le_quad32_to_bytes q;
  lemma_slices_le_bytes_to_quad32 s'';

  lemma_four_zero ();
  let zero_4 : seq nat8 = create 4 0 in
  assert (n < 4 ==> equal s4_8'' zero_4);
  assert (equal s8_12'' zero_4);
  assert (equal s12_16'' zero_4);
  ()

let pad_to_128_bits_upper (q:quad32) (num_bytes:int) =
  let n = num_bytes in
  let new_hi = (hi64 q) % pow2 ((n - 8) * 8) in
  pow2_lt_compat 64 ((n - 8) * 8);
  let s = le_quad32_to_bytes q in
  let s' = slice s 0 n in
  let q' = insert_nat64 q new_hi 1 in
  reveal_opaque insert_nat64;
  let s'' = pad_to_128_bits s' in
  let q'' = le_bytes_to_quad32 s'' in

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
    lemma_mod_n_8_upper1 q (n - 8);
    lemma_64_32_hi1 q' (hi64 q) new_hi (n - 8);
    lemma_pad_to_32_bits s8_12 s8_12'' (n - 8);
    ()
  )
  else
  (
    lemma_mod_n_8_upper2 q (n - 12);
    lemma_64_32_hi2 q' (hi64 q) new_hi (n - 12);
    lemma_pad_to_32_bits s12_16 s12_16'' (n - 12);
    ()
  );

  lemma_slices_le_quad32_to_bytes q;
  lemma_slices_le_bytes_to_quad32 s'';

  lemma_four_zero ();
  let zero_4 : seq nat8 = create 4 0 in
  assert (n < 12 ==> equal s12_16'' zero_4);
  ()
