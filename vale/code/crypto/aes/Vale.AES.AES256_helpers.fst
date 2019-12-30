module Vale.AES.AES256_helpers

let lemma_reveal_expand_key_256 (key:aes_key_LE AES_256) (round:nat) : Lemma
  (expand_key_256 key round == (
    if round = 0 then Mkfour key.[0] key.[1] key.[2] key.[3]
    else if round = 1 then Mkfour key.[4] key.[5] key.[6] key.[7]
    else round_key_256 (expand_key_256 key (round - 2)) (expand_key_256 key (round - 1)) round
  ))
  =
  expand_key_256_reveal ()

#reset-options "--initial_fuel 8 --max_fuel 8 --max_ifuel 0"
let lemma_expand_key_256_0 (key:aes_key_LE AES_256) : Lemma
  (equal key (expand_key AES_256 key 8))
  =
  expand_key_reveal ()

open FStar.Mul
#reset-options "--initial_fuel 1 --max_fuel 1 --max_ifuel 0 --z3rlimit 40 --using_facts_from '* -FStar.Seq.Properties'"
let lemma_expand_key_256_i (key:aes_key_LE AES_256) (i:nat) : Lemma
  (requires
    1 < i /\ i < 15
  )
  (ensures (
    let m = 4 * (i - 2) in
    let n = 4 * i in
    let v = expand_key AES_256 key n in          // Current
    let w = expand_key AES_256 key (n + 4) in    // Next 4 words
    let prev0 =                    Mkfour v.[m + 0] v.[m + 1] v.[m + 2] v.[m + 3] in  // Penultimate 4 words in Current
    let prev1 =                    Mkfour v.[m + 4] v.[m + 5] v.[m + 6] v.[m + 7] in  // Ultimate 4 words in Current
    round_key_256 prev0 prev1 i == Mkfour w.[n + 0] w.[n + 1] w.[n + 2] w.[n + 3]  // NextQuad == Next 4 words
  ))
  =
  expand_key_reveal ();
  let n = 4 * i in
  // unfold expand_key 8 times (could use fuel, but that unfolds everything):
  let _ = expand_key AES_256 key (n + 1) in
  let _ = expand_key AES_256 key (n + 2) in
  let _ = expand_key AES_256 key (n + 3) in
  let _ = expand_key AES_256 key (n + 4) in
  if i < 14 then (
    let _ = expand_key AES_256 key (n + 5) in
    let _ = expand_key AES_256 key (n + 6) in
    let _ = expand_key AES_256 key (n + 7) in
    ()
  ) else ();
  ()
#reset-options

// expand_key for large 'size' argument agrees with expand_key for smaller 'size' argument
let rec lemma_expand_append (key:aes_key_LE AES_256) (size1:nat) (size2:nat) : Lemma
  (requires size1 <= size2 /\ size2 <= 60)
  (ensures equal (expand_key AES_256 key size1) (slice (expand_key AES_256 key size2) 0 size1))
  (decreases size2)
  =
  expand_key_reveal ();
  if size1 < size2 then lemma_expand_append key size1 (size2 - 1)

// quad32 key expansion is equivalent to nat32 key expansion
let rec lemma_expand_key_256 (key:seq nat32) (size:nat) =
  lemma_expand_append key (4 * size) 60;
  if size = 0 then () else
  let i = size - 1 in
  lemma_expand_key_256 key i;
  lemma_reveal_expand_key_256 key i;
  if i < 2 then
  (
    lemma_expand_append key 4 60;
    lemma_expand_append key 8 60;
    lemma_expand_key_256_0 key
  )
  else
  (
    lemma_expand_append key (4 * i) 60;
    lemma_expand_key_256 key (i - 1);
    lemma_expand_key_256_i key i
  )

// SIMD version of round_key_256 is equivalent to scalar round_key_256
#push-options "--max_fuel 3 --initial_fuel 3 --max_ifuel 3 --initial_ifuel 3"  // REVIEW: Why do we need this?
let lemma_simd_round_key (prev0 prev1:quad32) (rcon:nat32) (round:int) =
  quad32_xor_reveal ();
  reverse_bytes_nat32_reveal ();
  commute_rot_word_sub_word prev1.hi3;
  Vale.Arch.Types.xor_lemmas ()
#pop-options

let lemma_round_key_256_rcon_odd (prev0 prev1:quad32) (rcon:nat32) (round:int) =
  ()
