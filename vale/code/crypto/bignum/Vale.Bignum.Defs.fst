module Vale.Bignum.Defs
open FStar.Mul

let lemma_mul_nat_bound a a' b b' =
  let open FStar.Math.Lemmas in
  nat_times_nat_is_nat a b;
  lemma_mult_le_left a b b'; // a * b <= a * b'
  lemma_mult_le_right b' a a'; // a * b' <= a' * b'
  ()

let lemma_mul_n_bound #n a b =
  lemma_mul_nat_bound a (n - 1) b (n - 1)

#restart-solver
let lemma_mul_div_n_lt #n a b =
  let open FStar.Math.Lemmas in
  lemma_mul_n_bound a b;
  lemma_div_le (a * b) ((n - 1) * (n - 1)) n;
  calc (==) {
    (n - 1) * (n - 1);
    == {distributivity_sub_right (n - 1) n 1}
    (n - 1) * n - (n - 1) * 1;
    == {}
    (n - 2) * n + 1;
  };
  if n > 1 then small_division_lemma_1 1 n; // 1 / n == 0
  lemma_div_plus 1 (n - 2) n; // (1 + (n - 2) * n) / n == 1 / n + (n - 2)
  ()

let lemma_mul_div_n #n a b =
  let open FStar.Math.Lemmas in
  nat_times_nat_is_nat a b;
  nat_over_pos_is_nat (a * b) n;
  lemma_mul_div_n_lt a b

let add_lo #n a b c = add_lo_def a b c
let reveal_add_lo #n a b c = ()
let reveal_add_lo_all () = ()

let add_hi #n a b c = add_hi_def a b c
let reveal_add_hi #n a b c = ()
let reveal_add_hi_all () = ()

let mul_lo #n a b = mul_lo_def a b
let reveal_mul_lo #n a b = ()
let reveal_mul_lo_all () = ()

let mul_hi #n a b = mul_hi_def a b
let reveal_mul_hi #n a b = ()
let reveal_mul_hi_all () = ()
