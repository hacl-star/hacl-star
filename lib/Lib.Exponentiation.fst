module Lib.Exponentiation

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

module Loops = Lib.LoopCombinators

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

#push-options "--fuel 2"
let lemma_pow0 #t k x = ()

let lemma_pow1 #t k x = lemma_one x

let lemma_pow_unfold #t k x n = ()
#pop-options

let rec lemma_pow_one #t k n =
  if n = 0 then
    lemma_pow0 k one
  else begin
    lemma_pow_unfold k one n;
    //assert (pow k one n == fmul one (pow k one (n - 1)));
    lemma_pow_one k (n - 1);
    //assert (pow k one n == fmul one one);
    lemma_one k.one;
    () end


let rec lemma_pow_add #t k x n m =
  if n = 0 then begin
    calc (==) {
      fmul (pow k x n) (pow k x m);
      (==) { lemma_pow0 k x }
      fmul one (pow k x m);
      (==) { lemma_fmul_comm one (pow k x m) }
      fmul (pow k x m) one;
      (==) { lemma_one (pow k x m) }
      pow k x m;
      }; () end
  else begin
    calc (==) {
      fmul (pow k x n) (pow k x m);
      (==) { lemma_pow_unfold k x n }
      fmul (fmul x (pow k x (n - 1))) (pow k x m);
      (==) { lemma_fmul_assoc x (pow k x (n - 1)) (pow k x m) }
      fmul x (fmul (pow k x (n - 1)) (pow k x m));
      (==) { lemma_pow_add #t k x (n - 1) m }
      fmul x (pow k x (n - 1 + m));
      (==) { lemma_pow_unfold k x (n + m) }
      pow k x (n + m);
      }; () end


let rec lemma_pow_mul #t k x n m =
  if m = 0 then begin
    lemma_pow0 k (pow k x n);
    lemma_pow0 k x;
    () end
  else begin
    calc (==) {
      pow k (pow k x n) m;
      (==) { lemma_pow_unfold k (pow k x n) m }
      fmul (pow k x n) (pow k (pow k x n) (m - 1));
      (==) { lemma_pow_mul k x n (m - 1) }
      fmul (pow k x n) (pow k x (n * (m - 1)));
      (==) { lemma_pow_add k x n (n * (m - 1)) }
      pow k x (n * m);
    }; () end


let rec lemma_pow_double #t k x b =
  if b = 0 then begin
    lemma_pow0 k (fmul x x);
    lemma_pow0 k x end
  else begin
    calc (==) {
      pow k (fmul x x) b;
      (==) { lemma_pow_unfold k (fmul x x) b }
      fmul (fmul x x) (pow k (fmul x x) (b - 1));
      (==) { lemma_pow_double k x (b - 1) }
      fmul (fmul x x) (pow k x (b + b - 2));
      (==) { lemma_pow1 k x }
      fmul (fmul (pow k x 1) (pow k x 1)) (pow k x (b + b - 2));
      (==) { lemma_pow_add k x 1 1 }
      fmul (pow k x 2) (pow k x (b + b - 2));
      (==) { lemma_pow_add k x 2 (b + b - 2) }
      pow k x (b + b);
    }; () end


let rec lemma_pow_mul_base #t k a b n =
  if n = 0 then begin
    lemma_pow0 k a;
    lemma_pow0 k b;
    lemma_one k.one;
    lemma_pow0 k (fmul a b) end
  else begin
    calc (==) {
      fmul (pow k a n) (pow k b n);
      (==) { lemma_pow_unfold k a n; lemma_pow_unfold k b n }
      fmul (fmul a (pow k a (n - 1))) (fmul b (pow k b (n - 1)));
      (==) { lemma_fmul_comm b (pow k b (n - 1));
       lemma_fmul_assoc a (pow k a (n - 1)) (fmul (pow k b (n - 1)) b) }
      fmul a (fmul (pow k a (n - 1)) (fmul (pow k b (n - 1)) b));
      (==) { lemma_fmul_assoc (pow k a (n - 1)) (pow k b (n - 1)) b }
      fmul a (fmul (fmul (pow k a (n - 1)) (pow k b (n - 1))) b);
      (==) { lemma_pow_mul_base #t k a b (n - 1) }
      fmul a (fmul (pow k (fmul a b) (n - 1)) b);
      (==) { lemma_fmul_comm (pow k (fmul a b) (n - 1)) b;
	lemma_fmul_assoc a b (pow k (fmul a b) (n - 1)) }
      fmul (fmul a b) (pow k (fmul a b) (n - 1));
      (==) { lemma_pow_unfold k (fmul a b) n }
      pow k (fmul a b) n;
    }; () end


val lemma_b_mod_pow2i: bBits:nat -> b:nat{b < pow2 bBits} -> i:pos{i <= bBits} ->
  Lemma (b % pow2 i == b / pow2 (i - 1) % 2 * pow2 (i - 1) + b % pow2 (i - 1))
let lemma_b_mod_pow2i bBits b i =
  calc (==) {
    b % pow2 i;
    (==) { Math.Lemmas.euclidean_division_definition (b % pow2 i) (pow2 (i - 1)) }
    b % pow2 i / pow2 (i - 1) * pow2 (i - 1) + b % pow2 i % pow2 (i - 1);
    (==) { Math.Lemmas.pow2_modulo_modulo_lemma_1 b (i - 1) i }
    b % pow2 i / pow2 (i - 1) * pow2 (i - 1) + b % pow2 (i - 1);
    (==) { Math.Lemmas.pow2_modulo_division_lemma_1 b (i - 1) i; assert_norm (pow2 1 = 2) }
    b / pow2 (i - 1) % 2 * pow2 (i - 1) + b % pow2 (i - 1);
  }

val lemma_b_div_pow2ki: bBits:nat -> b:nat{b < pow2 bBits} -> k:pos -> i:pos{k * i <= bBits} ->
  Lemma (b / pow2 (bBits - k * (i - 1)) * pow2 k + b / pow2 (bBits - k * (i - 1) - k) % pow2 k == b / pow2 (bBits - k * i))
let lemma_b_div_pow2ki bBits b k i =
  let c = b / pow2 (bBits - k * i) in
  calc (==) {
    b / pow2 (bBits - k * i);
    (==) { Math.Lemmas.euclidean_division_definition c (pow2 k) }
    c / pow2 k * pow2 k + c % pow2 k;
    (==) { Math.Lemmas.division_multiplication_lemma b (pow2 (bBits - k * i)) (pow2 k) }
    b / (pow2 (bBits - k * i) * pow2 k) * pow2 k + c % pow2 k;
    (==) { Math.Lemmas.pow2_plus (bBits - k * i) k }
    b / pow2 (bBits - k * i + k) * pow2 k + c % pow2 k;
    (==) { Math.Lemmas.distributivity_sub_right k i 1 }
    b / pow2 (bBits - k * (i - 1)) * pow2 k + c % pow2 k;
    }


val lemma_b_div_pow2i: bBits:nat -> b:nat{b < pow2 bBits} -> i:pos{i <= bBits} ->
  Lemma (b / pow2 (bBits - i) == b / pow2 (bBits - i + 1) * 2 + b / pow2 (bBits - i) % 2)
let lemma_b_div_pow2i bBits b i =
  assert_norm (pow2 1 = 2);
  lemma_b_div_pow2ki bBits b 1 i


val exp_rl_lemma_loop:
    #t:Type -> k:exp t
  -> bBits:nat -> b:nat{b < pow2 bBits}
  -> i:nat{i <= bBits}
  -> a0:t ->
  Lemma (let (a, acc) = Loops.repeati i (exp_rl_f k bBits b) (a0, one) in
    acc == pow k a0 (b % pow2 i) /\ a == pow k a0 (pow2 i))

let rec exp_rl_lemma_loop #t k bBits b i a0 =
  let (a, acc) = Loops.repeati i (exp_rl_f k bBits b) (a0, one) in
  if i = 0 then begin
    Loops.eq_repeati0 i (exp_rl_f k bBits b) (a0, one);
    assert_norm (pow2 0 = 1);
    lemma_pow0 k a;
    lemma_pow1 k a;
    () end
  else begin
    Loops.unfold_repeati i (exp_rl_f k bBits b) (a0, one) (i - 1);
    let (a1, acc1) = Loops.repeati (i - 1) (exp_rl_f k bBits b) (a0, one) in
    //assert (a == a1 * a1);
    //assert (acc == (if (b / pow2 (i - 1) % 2 = 1) then acc1 * a1 else acc1));

    exp_rl_lemma_loop #t k bBits b (i - 1) a0;
    assert (acc1 == pow k a0 (b % pow2 (i - 1)) /\ a1 == pow k a0 (pow2 (i - 1)));

    lemma_pow_add k a0 (pow2 (i - 1)) (pow2 (i - 1));
    Math.Lemmas.pow2_double_sum (i - 1);
    assert (a == pow k a0 (pow2 i));

    lemma_b_mod_pow2i bBits b i;
    assert (b % pow2 i == b / pow2 (i - 1) % 2 * pow2 (i - 1) + b % pow2 (i - 1));

    if (b / pow2 (i - 1) % 2 = 1) then begin
      //assert (acc == acc1 * a1);
      assert (acc == fmul (pow k a0 (b % pow2 (i - 1))) (pow k a0 (pow2 (i - 1))));
      lemma_pow_add k a0 (b % pow2 (i - 1)) (pow2 (i - 1));
      assert (acc == pow k a0 (b % pow2 i));
      () end
    else () end


let exp_rl_lemma #t k a bBits b =
  let (a1, acc1) = Loops.repeati bBits (exp_rl_f k bBits b) (a, one) in
  exp_rl_lemma_loop k bBits b bBits a;
  assert (acc1 == pow k a (b % pow2 bBits));
  Math.Lemmas.small_mod b (pow2 bBits)


val exp_lr_lemma_step:
   #t:Type -> k:exp t
  -> a:t -> bBits:nat -> b:nat{b < pow2 bBits}
  -> i:nat{i < bBits}
  -> acc1:t -> Lemma
  (requires acc1 == pow k a (b / pow2 (bBits - i)))
  (ensures  exp_lr_f k a bBits b i acc1 == pow k a (b / pow2 (bBits - i - 1)))

let exp_lr_lemma_step #t k a bBits b i acc1 =
  let acc = exp_lr_f k a bBits b i acc1 in
  lemma_b_div_pow2i bBits b (i + 1);
  assert (b / pow2 (bBits - i - 1) == b / pow2 (bBits - i) * 2 + b / pow2 (bBits - i - 1) % 2);
  lemma_pow_add k a (b / pow2 (bBits - i)) (b / pow2 (bBits - i));
  assert (fmul acc1 acc1 == pow k a (b / pow2 (bBits - i) * 2));

  if (b / pow2 (bBits - i - 1) % 2 = 0) then ()
  else begin
    assert (acc == fmul (pow k a (b / pow2 (bBits - i) * 2)) a);
    lemma_pow1 k a;
    lemma_pow_add k a (b / pow2 (bBits - i) * 2) 1;
    () end


val exp_lr_lemma_loop:
    #t:Type -> k:exp t
  -> a:t -> bBits:nat -> b:nat{b < pow2 bBits}
  -> i:nat{i <= bBits} ->
  Lemma (let acc = Loops.repeati i (exp_lr_f k a bBits b) one in
    acc == pow k a (b / pow2 (bBits - i)))

let rec exp_lr_lemma_loop #t k a bBits b i =
  let acc = Loops.repeati i (exp_lr_f k a bBits b) one in
  if i = 0 then begin
    Loops.eq_repeati0 i (exp_lr_f k a bBits b) one;
    lemma_pow0 k a;
    () end
  else begin
    let acc1 = Loops.repeati (i - 1) (exp_lr_f k a bBits b) one in
    Loops.unfold_repeati i (exp_lr_f k a bBits b) one (i - 1);
    //assert (acc == exp_lr_f k a bBits b (i - 1) acc1);
    exp_lr_lemma_loop k a bBits b (i - 1);
    //assert (acc1 == pow k a (b / pow2 (bBits - i + 1)));
    exp_lr_lemma_step #t k a bBits b (i - 1) acc1;
    //assert (acc == pow k a (b / pow2 (bBits - i)));
    () end


let exp_lr_lemma #t k a bBits b =
  let acc = Loops.repeati bBits (exp_lr_f k a bBits b) one in
  exp_lr_lemma_loop #t k a bBits b bBits;
  assert (acc == pow k a (b / pow2 0));
  assert_norm (pow2 0 = 1)


val exp_mont_ladder_lemma_step:
    #t:Type -> k:exp t
  -> bBits:nat -> b:nat{b < pow2 bBits}
  -> r1:t -> r0'':t -> r1'':t
  -> i:nat{i < bBits} -> Lemma
  (requires
    r1'' == fmul r0'' r1 /\ r0'' == pow k r1 (b / pow2 (bBits - i)))
  (ensures
   (let (r0', r1') = exp_mont_ladder_f k bBits b i (r0'', r1'') in
    r1' == fmul r0' r1 /\ r0' == pow k r1 (b / pow2 (bBits - i - 1))))

let exp_mont_ladder_lemma_step #t k bBits b r1 r0'' r1'' i =
  let (r0', r1') = exp_mont_ladder_f k bBits b i (r0'', r1'') in
  lemma_b_div_pow2i bBits b (i + 1);
  assert (b / pow2 (bBits - i - 1) == b / pow2 (bBits - i) * 2 + b / pow2 (bBits - i - 1) % 2);
  lemma_pow_add k r1 (b / pow2 (bBits - i)) (b / pow2 (bBits - i));
  assert (fmul r0'' r0'' == pow k r1 (b / pow2 (bBits - i) * 2));

  if (b / pow2 (bBits - i - 1) % 2 = 0) then begin
    assert (r0' == pow k r1 (b / pow2 (bBits - i - 1)));
    //assert (r1' == fmul r1'' r0'');
    assert (r1' == fmul (fmul r0'' r1) r0'');
    lemma_fmul_comm r0'' r1;
    lemma_fmul_assoc r1 r0'' r0'';
    assert (r1' == fmul r1 r0');
    lemma_fmul_comm r1 r0';
    () end
  else begin
    //assert (r0' == fmul r0'' r1'');
    assert (r0' == fmul r0'' (fmul r0'' r1));
    lemma_fmul_assoc r0'' r0'' r1;
    lemma_pow1 k r1;
    lemma_pow_add k r1 (b / pow2 (bBits - i) * 2) 1;
    assert (r0' == pow k r1 (b / pow2 (bBits - i - 1)));
    //assert (r1' == fmul r1'' r1'');
    assert (r1' == fmul (fmul r0'' r1) (fmul r0'' r1));
    lemma_fmul_comm r0'' r1;
    lemma_fmul_assoc r1 r0'' (fmul r0'' r1);
    assert (r1' == fmul r1 r0');
    lemma_fmul_comm r1 r0';
    () end


val exp_mont_ladder_lemma_loop:
    #t:Type -> k:exp t
  -> bBits:nat -> b:nat{b < pow2 bBits}
  -> r1:t -> i:nat{i <= bBits} ->
  Lemma (let (r0', r1') = Loops.repeati i (exp_mont_ladder_f k bBits b) (one, r1) in
    r1' == fmul r0' r1 /\ r0' == pow k r1 (b / pow2 (bBits - i)))

let rec exp_mont_ladder_lemma_loop #t k bBits b r1 i =
  let (r0', r1') = Loops.repeati i (exp_mont_ladder_f k bBits b) (one, r1) in
  if i = 0 then begin
    Loops.eq_repeati0 i (exp_mont_ladder_f k bBits b) (one, r1);
    Math.Lemmas.small_div b (pow2 bBits);
    lemma_pow0 k r1;
    lemma_one r1;
    lemma_fmul_comm r1 one; //fmul one r1 == r1
    () end
  else begin
    let (r0'', r1'') = Loops.repeati (i - 1) (exp_mont_ladder_f k bBits b) (one, r1) in
    Loops.unfold_repeati i (exp_mont_ladder_f k bBits b) (one, r1) (i - 1);
    //assert ((r0', r1') == exp_mont_ladder_f k bBits b (i - 1) (r0'', r1''));
    exp_mont_ladder_lemma_loop k bBits b r1 (i - 1);
    //assert (r1'' == fmul r0'' r1);
    //assert (r0'' == pow k r1 (b / pow2 (bBits - i + 1)));
    exp_mont_ladder_lemma_step #t k bBits b r1 r0'' r1'' (i - 1);
    //assert (r1' == fmul r0' r1 /\ r0' == pow k r1 (b / pow2 (bBits - i)));
    () end


let exp_mont_ladder_lemma # t k a bBits b =
  let (r0, r1) = Loops.repeati bBits (exp_mont_ladder_f k bBits b) (one, a) in
  exp_mont_ladder_lemma_loop #t k bBits b a bBits;
  assert_norm (pow2 0 = 1)


val exp_mont_ladder_swap2_lemma_loop:
    #t:Type -> k:exp t
  -> a:t -> bBits:nat -> b:nat{b < pow2 bBits}
  -> i:nat{i <= bBits} ->
  Lemma
  (let (r0', r1') = Loops.repeati i (exp_mont_ladder_swap2_f k bBits b) (one, a) in
   let (r0'', r1'') = Loops.repeati i (exp_mont_ladder_f k bBits b) (one, a) in
   r0' == r0'' /\ r1' == r1'')

let rec exp_mont_ladder_swap2_lemma_loop #t k a bBits b i =
  if i = 0 then begin
    Loops.eq_repeati0 i (exp_mont_ladder_swap2_f k bBits b) (one, a);
    Loops.eq_repeati0 i (exp_mont_ladder_f k bBits b) (one, a);
    () end
  else begin
    Loops.unfold_repeati i (exp_mont_ladder_swap2_f k bBits b) (one, a) (i - 1);
    Loops.unfold_repeati i (exp_mont_ladder_f k bBits b) (one, a) (i - 1);
    exp_mont_ladder_swap2_lemma_loop k a bBits b (i - 1);
    () end


let exp_mont_ladder_swap2_lemma #t k a bBits b =
  exp_mont_ladder_swap2_lemma_loop #t k a bBits b bBits


val exp_mont_ladder_swap_lemma_loop:
    #t:Type -> k:exp t
  -> a:t -> bBits:nat -> b:nat{b < pow2 bBits}
  -> sw0:nat{sw0 == b / pow2 bBits % 2}
  -> i:nat{i <= bBits} ->
  Lemma
  (let (r0', r1', sw) = Loops.repeati i (exp_mont_ladder_swap_f k bBits b) (one, a, sw0) in
   let (r0'', r1'') = Loops.repeati i (exp_mont_ladder_f k bBits b) (cswap sw0 one a) in
   let bit = b / pow2 (bBits - i) % 2 in
   sw == bit /\ cswap bit r0' r1' == (r0'', r1''))

let rec exp_mont_ladder_swap_lemma_loop #t k a bBits b sw0 i =
  if i = 0 then begin
    Loops.eq_repeati0 i (exp_mont_ladder_swap_f k bBits b) (one, a, sw0);
    Loops.eq_repeati0 i (exp_mont_ladder_f k bBits b) (cswap sw0 one a);
    () end
  else begin
    Loops.unfold_repeati i (exp_mont_ladder_swap_f k bBits b) (one, a, sw0) (i - 1);
    Loops.unfold_repeati i (exp_mont_ladder_f k bBits b) (cswap sw0 one a) (i - 1);
    exp_mont_ladder_swap_lemma_loop k a bBits b sw0 (i - 1);
    () end


let exp_mont_ladder_swap_lemma #t k a bBits b =
  exp_mont_ladder_swap_lemma_loop #t k a bBits b 0 bBits


val exp_pow2_loop_lemma: #t:Type -> k:exp t -> a:t -> b:nat -> i:nat{i <= b} ->
  Lemma (Loops.repeat i (fsqr k) a == pow k a (pow2 i))
let rec exp_pow2_loop_lemma #t k a b i =
  if i = 0 then begin
    Loops.eq_repeat0 (fsqr k) a;
    assert_norm (pow2 0 = 1);
    lemma_pow1 k a end
  else begin
    Loops.unfold_repeat b (fsqr k) a (i - 1);
    exp_pow2_loop_lemma k a b (i - 1);
    lemma_pow_add k a (pow2 (i - 1)) (pow2 (i - 1));
    Math.Lemmas.pow2_double_sum (i - 1);
    () end

let exp_pow2_lemma #t k a b = exp_pow2_loop_lemma k a b b

val precomp_table_loop_lemma:
    #t:Type -> k:exp t -> a:t
  -> table_len:size_nat{1 < table_len} ->
  Pure (lseq t table_len)
  (requires True)
  (ensures  fun res ->
    res == precomp_table k a table_len /\
    (forall (i:nat{i < table_len}). index res i == pow k a i))

let precomp_table_loop_lemma #t k a table_len =
  let table = create table_len one in
  let table = table.[0] <- one in
  let table = table.[1] <- a in
  lemma_pow0 k a;
  lemma_pow1 k a;
  assert (table.[0] == pow k a 0);
  assert (table.[1] == pow k a 1);

  Loops.eq_repeati0 (table_len - 2) (precomp_table_f #t k a table_len) table;
  Loops.repeati_inductive (table_len - 2)
  (fun i table_i ->
    table_i == Loops.repeati i (precomp_table_f #t k a table_len) table /\
   (forall (i0:nat{i0 < i + 2}). index table_i i0 == pow k a i0))
  (fun i table_i ->
    let table_i1 = precomp_table_f #t k a table_len i table_i in
    Loops.unfold_repeati (i + 1) (precomp_table_f #t k a table_len) table i;
    //assert (table_i1 == Loops.repeati (i + 1) (precomp_table_f #t k a table_len) table);
    //assert (table_i.[i + 1] == pow k a (i + 1));
    lemma_pow_add k a (i + 1) 1;
    //assert (table_i1.[i + 2] == pow k a (i + 2));
    table_i1)
  table

let precomp_table_lemma #t k a table_len =
  let _ = precomp_table_loop_lemma #t k a table_len in ()


val exp_fw_lemma_step:
    #t:Type -> k:exp t
  -> a:t
  -> bBits:nat -> b:nat{b < pow2 bBits}
  -> l:pos
  -> table_len:size_nat{1 < table_len /\ table_len == pow2 l}
  -> table:lseq t table_len
  -> i:pos{l * i <= bBits}
  -> acc1:t -> Lemma
  (requires
    acc1 == pow k a (b / pow2 (bBits - l * (i - 1))) /\
    table == precomp_table k a table_len)
  (ensures
    exp_fw_f k bBits b l table_len table (i - 1) acc1 == pow k a (b / pow2 (bBits - l * i)))

let exp_fw_lemma_step #t k a bBits b l table_len table i acc1 =
  let acc = exp_fw_f k bBits b l table_len table (i - 1) acc1 in
  exp_pow2_lemma k acc1 l;
  precomp_table_lemma k a table_len;
  assert (acc == fmul (pow k acc1 (pow2 l)) (pow k a (b / pow2 (bBits - l * (i - 1) - l) % pow2 l)));

  let r1 = pow k a (b / pow2 (bBits - l * (i - 1)) * pow2 l) in
  let r2 = pow k a (b / pow2 (bBits - l * (i - 1) - l) % pow2 l) in

  calc (==) {
    fmul (pow k acc1 (pow2 l)) r2;
    (==) { }
    fmul (pow k (pow k a (b / pow2 (bBits - l * (i - 1)))) (pow2 l)) r2;
    (==) { lemma_pow_mul k a (b / pow2 (bBits - l * (i - 1))) (pow2 l) }
    fmul r1 r2;
    (==) { lemma_pow_add k a (b / pow2 (bBits - l * (i - 1)) * pow2 l) (b / pow2 (bBits - l * (i - 1) - l) % pow2 l) }
    pow k a (b / pow2 (bBits - l * (i - 1)) * pow2 l + b / pow2 (bBits - l * (i - 1) - l) % pow2 l);
    (==) { lemma_b_div_pow2ki bBits b l i }
    pow k a (b / pow2 (bBits - l * i));
    }


val exp_fw_lemma_loop:
    #t:Type -> k:exp t
  -> a:t
  -> bBits:nat -> b:nat{b < pow2 bBits}
  -> l:pos
  -> table_len:size_nat{1 < table_len /\ table_len == pow2 l}
  -> table:lseq t table_len
  -> i:nat{l * i <= bBits} -> Lemma
  (requires table == precomp_table k a table_len)
  (ensures  (let acc = Loops.repeati i (exp_fw_f k bBits b l table_len table) one in
    acc == pow k a (b / pow2 (bBits - l * i))))

let rec exp_fw_lemma_loop #t k a bBits b l table_len table i =
  let acc = Loops.repeati i (exp_fw_f k bBits b l table_len table) one in
  if i = 0 then begin
    Loops.eq_repeati0 i (exp_fw_f k bBits b l table_len table) one;
    Math.Lemmas.small_div b (pow2 bBits);
    lemma_pow0 k a;
    () end
  else begin
    Loops.unfold_repeati i (exp_fw_f k bBits b l table_len table) one (i - 1);
    let acc1 = Loops.repeati (i - 1) (exp_fw_f k bBits b l table_len table) one in
    //assert (acc == exp_fw_f k bBits b l table_len table (i - 1) acc1);
    exp_fw_lemma_loop k a bBits b l table_len table (i - 1);
    //assert (acc1 == pow k a (b / pow2 (bBits - l * (i - 1))));
    exp_fw_lemma_step k a bBits b l table_len table i acc1;
    //assert (acc == pow k a (b / pow2 (bBits - l * i)));
    () end


let exp_fw_lemma #t k a bBits b l =
  let table_len = pow2 l in
  Math.Lemmas.pow2_le_compat l 1;
  let table = precomp_table k a table_len in
  let acc = Loops.repeati (bBits / l) (exp_fw_f k bBits b l table_len table) one in
  exp_fw_lemma_loop k a bBits b l table_len table (bBits / l);
  assert (acc == pow k a (b / pow2 (bBits - l * (bBits / l))));
  Math.Lemmas.euclidean_division_definition bBits l;
  assert (acc == pow k a (b / pow2 (bBits % l)));

  let c = bBits % l in
  let res = if c = 0 then acc else fmul (pow k acc (pow2 c)) (pow k a (b % pow2 c)) in
  if c = 0 then begin
    assert_norm (pow2 0 = 1);
    assert (acc == pow k a b) end
  else begin
    calc (==) {
      fmul (pow k acc (pow2 c)) (pow k a (b % pow2 c));
      (==) {  }
      fmul (pow k (pow k a (b / pow2 c)) (pow2 c)) (pow k a (b % pow2 c));
      (==) { lemma_pow_mul k a (b / pow2 c) (pow2 c) }
      fmul (pow k a (b / pow2 c * pow2 c)) (pow k a (b % pow2 c));
      (==) { lemma_pow_add k a (b / pow2 c * pow2 c) (b % pow2 c) }
      pow k a (b / pow2 c * pow2 c + b % pow2 c);
      (==) { Math.Lemmas.euclidean_division_definition b (pow2 c) }
      pow k a b;
      }; () end
