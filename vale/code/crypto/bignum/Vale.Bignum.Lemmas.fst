module Vale.Bignum.Lemmas
open FStar.Mul

let rec lemma_sum_seq_left_right_rec (s:seq int) (i j k:nat) : Lemma
  (requires i <= j /\ j <= k /\ k <= length s)
  (ensures sum_seq_left s i j + sum_seq_right s j k == sum_seq_right s i k)
  (decreases j)
  =
  if i < j then lemma_sum_seq_left_right_rec s i (j - 1) k

let lemma_sum_seq_left_right s i j =
  lemma_sum_seq_left_right_rec s i j j

let rec lemma_pow_nat a b =
  if b > 0 then (
    lemma_pow_nat a (b - 1);
    FStar.Math.Lemmas.nat_times_nat_is_nat a (pow_int a (b - 1))
  )

let rec lemma_sum_pow_seq_bound_rec (#n:nat) (s:seq (natN n)) (i:nat{i <= length s}) : Lemma
  (ensures 0 <= sum_pow_seq_left s i /\ sum_pow_seq_left s i < pow_int n i)
  =
  let open FStar.Math.Lemmas in
  if i > 0 then (
    calc (<=) {
      0;
      <= {lemma_sum_pow_seq_bound_rec s (i - 1)}
      sum_pow_seq_left s (i - 1);
      <= {lemma_pow_nat n (i - 1); nat_times_nat_is_nat s.[i - 1] (pow_int n (i - 1))}
      s.[i - 1] * pow_int n (i - 1) + sum_seq_left (pow_seq s) 0 (i - 1);
      == {}
      sum_pow_seq_left s i;
    };
    calc (<=) {
      sum_pow_seq_left s i + 1;
      == {}
      s.[i - 1] * pow_int n (i - 1) + sum_seq_left (pow_seq s) 0 (i - 1) + 1;
      <= {lemma_sum_pow_seq_bound_rec s (i - 1)}
      s.[i - 1] * pow_int n (i - 1) + pow_int n (i - 1);
      <= {lemma_pow_nat n (i - 1); lemma_mult_le_right (pow_int n (i - 1)) s.[i - 1] (n - 1)}
      (n - 1) * pow_int n (i - 1) + pow_int n (i - 1);
      == {}
      pow_int n i;
    }
  )

let rec lemma_sum_pow_seq_bound #n s =
  lemma_sum_pow_seq_bound_rec s (length s)

let lemma_seq_add_is_norm #n as bs c0 i =
  ()

#push-options "--z3cliopt smt.arith.nl=true"
#restart-solver
let lemma_last_carry_mul a b c =
  ()
#pop-options

#push-options "--z3cliopt smt.arith.nl=true"
#restart-solver
let lemma_add_lo_mul_right #n a b c m =
  reveal_add_lo_all ()
#pop-options

let rec lemma_seq_add_rec (#n:nat) (as bs:seq (natN n)) (c0:nat1) (i:nat) : Lemma
  (requires i <= length as /\ length bs == length as)
  (ensures (
    let xs = fst (seq_add as bs c0) in
    let ci = seq_add_c as bs c0 i in
    sum_pow_seq_left xs i + last_carry n i ci == sum_pow_seq_left as i + sum_pow_seq_left bs i + c0
  ))
  (decreases i)
  =
  if (i > 0) then (
    let xs = fst (seq_add as bs c0) in
    let ci = seq_add_c as bs c0 i in
    let i' = i - 1 in
    let ci' = seq_add_c as bs c0 i' in
    calc (==) {
      sum_pow_seq_left xs i + last_carry n i ci;
      == {}
      xs.[i'] * pow_int n i' + sum_pow_seq_left xs i' + last_carry n i ci;
      == {lemma_seq_add_rec as bs c0 i'}
      xs.[i'] * pow_int n i' + sum_pow_seq_left as i' + sum_pow_seq_left bs i' + c0 - last_carry n i' ci' + last_carry n i ci;
      == {
        reveal_add_hi_all ();
        lemma_last_carry_mul n i' ci';
        lemma_add_lo_mul_right as.[i'] bs.[i'] ci' (pow_int n i')
      }
      sum_pow_seq_left as i + sum_pow_seq_left bs i + c0;
    }
  )

let lemma_seq_add #n as bs c0 =
  lemma_seq_add_rec as bs c0 (length as)

#push-options "--z3rlimit 100 --z3cliopt smt.arith.nl=true --max_ifuel 0"
#restart-solver
let rec lemma_seq_scale_rec (#n:nat) (a:natN n) (bs:seq (natN n)) (d:natN n) (i:nat) : Lemma
  (requires i <= length bs)
  (ensures (
    a * sum_pow_seq_left bs i + d ==
      sum_pow_seq_left (seq_scale_lo a bs) i + sum_pow_seq_left (seq_scale_hi a bs d) (i + 1)
  ))
  (decreases i)
  =
  reveal_mul_lo_all ();
  reveal_mul_hi_all ();
  if i = 0 then (
    assert (sum_pow_seq_left (seq_scale_hi a bs d) 0 == 0);
    assert (sum_pow_seq_left (seq_scale_hi a bs d) 1 == d)
  ) else (
    lemma_seq_scale_rec a bs d (i - 1)
  )
#pop-options

let rec lemma_seq_scale_carry1 (a:natN 1) (bs:seq (natN 1)) (d:natN 1) (i:nat) : Lemma
  (requires i <= length bs + 1)
  (ensures (
    seq_add_c (seq_scale_lo a bs) (seq_scale_hi a bs d) 0 i == 0
  ))
  =
  reveal_add_hi_all ();
  if i > 0 then lemma_seq_scale_carry1 a bs d (i - 1)

let lemma_seq_scale_carry #n a bs d =
  reveal_add_hi_all ();
  reveal_mul_lo_all ();
  reveal_mul_hi_all ();
  let l = length bs in
  if l = 0 then assert (seq_add_c (seq_scale_lo a bs) (seq_scale_hi a bs d) 0 0 == 0)
  else if n = 1 then lemma_seq_scale_carry1 a bs d (l + 1)
  else (
    lemma_mul_n_bound a bs.[l - 1];
    lemma_mul_div_n_lt a bs.[l - 1];
    ()
  )

let lemma_seq_scale #n a bs d =
  let l = length bs in
  calc (==) {
    sum_pow_seq (seq_scale a bs d);
    == {
      lemma_seq_scale_carry a bs d;
      lemma_seq_add_rec (seq_scale_lo a bs) (seq_scale_hi a bs d) 0 (l + 1)
    }
    sum_pow_seq (seq_scale_lo a bs) + sum_pow_seq (seq_scale_hi a bs d);
  };
  calc (==) {
    sum_pow_seq (seq_scale_lo a bs) + sum_pow_seq (seq_scale_hi a bs d);
    == {assert (0 * pow_int n l == 0)}
    sum_pow_seq_left (seq_scale_lo a bs) l + sum_pow_seq (seq_scale_hi a bs d);
    == {lemma_seq_scale_rec a bs d (length bs)}
    a * sum_pow_seq bs + d;
  }

let lemma_scale_add #n l a d bs rs ys zs qs xs =
  let ys = init (l + 1) (ys_init a bs) in
  let zs = init (l + 1) (zs_init a bs d) in
  let c0 = 0 in
  let o1 = 0 in
  let (qs, _) = seq_add rs zs c0 in
  let (xs, _) = seq_add qs ys c0 in
  assert (equal ys (seq_scale_lo a bs));
  assert (equal zs (seq_scale_hi a bs d));
  lemma_sum_pow_seq_bound bs;
  lemma_sum_pow_seq_bound xs;
  lemma_sum_pow_seq_bound qs;
  lemma_sum_pow_seq_bound_rec rs l;
  lemma_mul_nat_bound a (n - 1) (sum_pow_seq bs) (pow_int n l - 1);
  lemma_seq_add qs ys c0;
  lemma_seq_add rs zs o1;
  lemma_seq_scale a bs d;
  ()

