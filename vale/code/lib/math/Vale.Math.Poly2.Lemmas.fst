module Vale.Math.Poly2.Lemmas
open FStar.Mul

let lemma_pointwise_equal a b pf =
  FStar.Classical.forall_intro pf;
  lemma_equal a b

let lemma_index a =
  FStar.Classical.forall_intro (lemma_index_i a)

let lemma_index_all () =
  FStar.Classical.forall_intro_2 lemma_index_i

let lemma_zero_define () =
  FStar.Classical.forall_intro lemma_zero_define_i

let lemma_one_define () =
  FStar.Classical.forall_intro lemma_one_define_i

let lemma_monomial_define n =
  FStar.Classical.forall_intro (lemma_monomial_define_i n)

let lemma_monomial_define_all () =
  FStar.Classical.forall_intro_with_pat (fun n -> monomial n) lemma_monomial_define

let lemma_ones_define n =
  FStar.Classical.forall_intro (lemma_ones_define_i n)

let lemma_ones_define_all () =
  FStar.Classical.forall_intro_with_pat (fun n -> ones n) lemma_ones_define

let lemma_shift_define p n =
  FStar.Classical.forall_intro (lemma_shift_define_i p n)

let lemma_shift_define_forward p n =
  lemma_shift_define p n

let lemma_shift_define_all () =
  FStar.Classical.forall_intro_2_with_pat (fun p n -> shift p n) lemma_shift_define

let lemma_and_define a b =
  FStar.Classical.forall_intro (lemma_and_define_i a b)

let lemma_and_define_all () =
  FStar.Classical.forall_intro_2_with_pat (fun a b -> poly_and a b) lemma_and_define

let lemma_or_define a b =
  FStar.Classical.forall_intro (lemma_or_define_i a b)

let lemma_or_define_all () =
  FStar.Classical.forall_intro_2_with_pat (fun a b -> poly_or a b) lemma_or_define

let lemma_mask_define p n =
  FStar.Classical.forall_intro (lemma_mask_define_i p n);
  ()

let lemma_mask_define_all () =
  FStar.Classical.forall_intro_2_with_pat (fun p n -> mask p n) lemma_mask_define

let lemma_reverse_define p n =
  FStar.Classical.forall_intro (lemma_reverse_define_i p n)

let lemma_reverse_define_all () =
  FStar.Classical.forall_intro_2 lemma_reverse_define

let lemma_degree_negative a =
  let f (i:int) : Lemma (not a.[i]) =
    lemma_index_i a i
    in
  FStar.Classical.forall_intro f;
  lemma_zero_define ();
  lemma_equal a zero

let lemma_degree_is a n =
  lemma_index a;
  lemma_index_i a n;
  lemma_degree a

let lemma_zero_degree =
  lemma_degree zero;
  lemma_zero_define ()

let lemma_one_degree =
  lemma_one_define ();
  lemma_degree_is one 0

let lemma_monomial_degree n =
  lemma_monomial_define n;
  lemma_degree_is (monomial n) n

let lemma_ones_degree n =
  lemma_ones_define n;
  lemma_degree_is (ones n) (n - 1)

let lemma_shift_degree a n =
  lemma_index a;
  lemma_degree a;
  lemma_shift_define a n;
  lemma_zero_define ();
  if degree a < 0 || degree a + n < 0 then
  (
    lemma_equal zero (shift a n);
    lemma_degree_negative (shift a n)
  )
  else
    lemma_degree_is (shift a n) (degree a + n)

let lemma_and_degree a b =
  lemma_and_define a b;
  lemma_index_all ();
  lemma_degree a;
  lemma_degree b;
  lemma_degree (poly_and a b)

let lemma_or_degree a b =
  lemma_or_define a b;
  lemma_index_all ();
  lemma_degree a;
  lemma_degree b;
  lemma_degree_is (poly_or a b) (FStar.Math.Lib.max (degree a) (degree b))

let lemma_mask_degree a n =
  lemma_mask_define a n;
  lemma_degree (mask a n)

let lemma_reverse_degree a n =
  lemma_index a;
  lemma_reverse_define a n;
  lemma_degree (reverse a n)

let lemma_of_list_degree l =
  let len = List.length l in
  let s = seq_of_list l in
  let a = of_seq s in
  assert (forall (i:nat).{:pattern (index s i)} i < len ==> index s i == List.index l i);
  lemma_index a;
  lemma_degree a;
  lemma_zero_define ();
  if len > 0 then
    lemma_degree_is a (len - 1)
  else
    assert (not a.[degree a])

let lemma_add_define a b =
  FStar.Classical.forall_intro (lemma_add_define_i a b)

let lemma_add_define_all () =
  FStar.Classical.forall_intro_2_with_pat (fun a b -> (a +. b)) lemma_add_define

let lemma_add_zero_right = lemma_add_zero
let lemma_add_zero_left a = lemma_add_zero a; lemma_add_commute a zero

let lemma_add_all () =
  FStar.Classical.forall_intro_with_pat (fun a -> a +. zero) lemma_add_zero;
  FStar.Classical.forall_intro_with_pat (fun a -> a +. a) lemma_add_cancel;
  FStar.Classical.forall_intro_2_with_pat (fun a b -> a +. b) lemma_add_commute;
  FStar.Classical.forall_intro_3_with_pat (fun a b c -> a +. (b +. c)) lemma_add_associate

let lemma_bitwise_all () =
  lemma_index_all ();
  lemma_zero_define ();
  lemma_one_define ();
  lemma_monomial_define_all ();
  lemma_ones_define_all ();
  lemma_shift_define_all ();
  lemma_and_define_all ();
  lemma_or_define_all ();
  lemma_mask_define_all ();
  lemma_reverse_define_all ();
  lemma_add_define_all ();
  ()

let lemma_monomial_add_degree n a =
  lemma_bitwise_all ();
  lemma_degree_is (monomial n +. a) n;
  lemma_degree_is (a +. monomial n) n;
  ()

let lemma_and_zero a =
  lemma_bitwise_all ();
  lemma_equal (poly_and a zero) zero;
  lemma_equal (poly_and zero a) zero;
  ()

let lemma_and_ones a n =
  lemma_bitwise_all ();
  lemma_equal (poly_and a (ones n)) a;
  lemma_equal (poly_and (ones n) a) a;
  ()

let lemma_and_ones_smt (a:poly) (n:nat) : Lemma
  (requires degree a < n)
  (ensures poly_and a (ones n) == a /\ poly_and (ones n) a == a)
  [SMTPat (poly_and a (ones n)); SMTPat (poly_and (ones n) a)]
  =
  lemma_and_ones a n

let lemma_and_consts () =
  let f1 a n : Lemma (degree a < n ==> poly_and a (ones n) == a) =
    if degree a < n then lemma_and_ones a n
    in
  let f2 a n : Lemma (degree a < n ==> poly_and (ones n) a == a) =
    if degree a < n then lemma_and_ones a n
    in
  FStar.Classical.forall_intro lemma_and_zero;
  FStar.Classical.forall_intro_2 f1;
  FStar.Classical.forall_intro_2 f2;
  ()

let lemma_or_zero a =
  lemma_bitwise_all ();
  lemma_equal (poly_or a zero) a;
  lemma_equal (poly_or zero a) a;
  ()

let lemma_or_ones a n =
  lemma_bitwise_all ();
  lemma_equal (poly_or a (ones n)) (ones n);
  lemma_equal (poly_or (ones n) a) (ones n);
  ()

let lemma_or_consts () =
  let f1 a n : Lemma (degree a < n ==> poly_or a (ones n) == (ones n)) =
    if degree a < n then lemma_or_ones a n
    in
  let f2 a n : Lemma (degree a < n ==> poly_or (ones n) a == (ones n)) =
    if degree a < n then lemma_or_ones a n
    in
  FStar.Classical.forall_intro lemma_or_zero;
  FStar.Classical.forall_intro_2 f1;
  FStar.Classical.forall_intro_2 f2;
  ()

let lemma_mul_distribute_left a b c =
  lemma_mul_commute (a +. b) c;
  lemma_mul_commute a c;
  lemma_mul_commute b c;
  lemma_mul_distribute c a b

let lemma_mul_distribute_right a b c = lemma_mul_distribute a b c

let lemma_mul_smaller_is_zero a b =
  lemma_mul_zero b;
  (if degree a < 0 then lemma_degree_negative a);
  lemma_mul_commute a b;
  ()

let lemma_mul_monomials m n =
  lemma_shift_is_mul (monomial m) n; // monomial m *. monomial n == shift (monomial m) n
  lemma_monomial_define m;
  lemma_monomial_define (m + n);
  lemma_shift_define (monomial m) n;
  lemma_equal (shift (monomial m) n) (monomial (m + n))

let lemma_add_reverse a b n =
  lemma_bitwise_all ();
  lemma_equal (reverse (a +. b) n) (reverse a n +. reverse b n)

let lemma_mul_reverse_shift_1 a b n =
  let ab = a *. b in
  let ra = reverse a n in
  let rb = reverse b n in
  let rab = reverse ab (n + n) in
  let rab1 = reverse ab (n + n + 1) in
  lemma_index ab;
  lemma_mul_reverse a b n;
  lemma_reverse_define ab (n + n);
  lemma_reverse_define ab (n + n + 1);
  lemma_shift_define (ra *. rb) 1;
  lemma_equal rab1 (shift (ra *. rb) 1)

let lemma_shift_is_mul_right = lemma_shift_is_mul
let lemma_shift_is_mul_left a n =
  lemma_shift_is_mul a n;
  lemma_mul_commute (monomial n) a

let lemma_shift_shift a m n =
  lemma_index_all ();
  lemma_shift_define_all ();
  lemma_equal (shift a (m + n)) (shift (shift a m) n);
  ()

let lemma_mul_all () =
  FStar.Classical.forall_intro_with_pat (fun a -> a *. zero) lemma_mul_zero;
  FStar.Classical.forall_intro_with_pat (fun a -> a *. one) lemma_mul_one;
  FStar.Classical.forall_intro_2_with_pat (fun a b -> a *. b) lemma_mul_commute;
  FStar.Classical.forall_intro_3_with_pat (fun a b c -> a *. (b *. c)) lemma_mul_associate

let lemma_mod_distribute a b c =
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
  assert (ab'' +. a'' +. b'' == zero);
  lemma_zero_define ();
  lemma_equal ab'' (a'' +. b'');
  ()

let lemma_div_mod_unique a b x y =
  let x' = a /. b in
  let y' = a %. b in
  lemma_div_mod a b;
  assert (x *. b +. y == x' *. b +. y');
  lemma_add_define_all ();
  lemma_equal (x *. b +. x' *. b) (y +. y');
  lemma_mul_distribute_left x x' b;
  assert ((x +. x') *. b == y +. y');
  lemma_mul_smaller_is_zero (x +. x') b;
  assert (y +. y' == zero);
  lemma_zero_define ();
  lemma_equal x x';
  lemma_equal y y';
  ()

let lemma_div_mod_exact a b =
  // (a *. b == a *. b +. zero)
  lemma_add_zero (a *. b);
  lemma_div_mod_unique (a *. b +. zero) b a zero

let lemma_mod_small a b =
  lemma_mul_zero b;
  lemma_mul_commute b zero;
  lemma_add_zero a;
  lemma_add_commute a zero;
  lemma_div_mod_unique a b zero a

let lemma_mod_mod a b =
  lemma_mod_small (a %. b) b

let lemma_mod_cancel a =
  lemma_mul_one a;
  lemma_mul_commute a one;
  lemma_div_mod_exact one a

let lemma_mod_mul_mod a b c =
  let ab = a %. b in
  let abc = ab *. c in
  let ac = a *. c in
  let x = abc /. b in
  let y = abc %. b in
  let x' = ac /. b in
  let y' = ac %. b in
  lemma_div_mod abc b;
  lemma_div_mod ac b;
  // ab *. c == x *. b +. y
  // a *. c == x' *. b +. y'
  assert ((ab *. c) +. (a *. c) == (x *. b +. y) +. (x' *. b +. y'));
  lemma_mul_distribute_left ab a c;
  assert ((ab +. a) *. c == (x *. b +. y) +. (x' *. b +. y'));

  // prove that ab +. a is a multiple of b by proving (ab +. a) %. b == zero
  lemma_mod_distribute ab a b;
  lemma_mod_mod a b;
  lemma_add_cancel ab;
  lemma_div_mod (ab +. a) b;
  let z = (ab +. a) /. b in
  lemma_add_zero (z *. b);
  assert (ab +. a == z *. b);

  assert ((z *. b) *. c == (x *. b +. y) +. (x' *. b +. y'));
  lemma_mul_associate z b c;
  lemma_mul_commute b c;
  lemma_mul_associate z c b;
  assert ((z *. c) *. b == (x *. b +. y) +. (x' *. b +. y'));
  lemma_add_define_all ();
  lemma_equal ((z *. c) *. b +. x *. b +. x' *. b) (y +. y');
  lemma_mul_distribute_left (z *. c) x b;
  lemma_mul_distribute_left (z *. c +. x) x' b;
  assert ((z *. c +. x +. x') *. b == y +. y');
  lemma_mul_smaller_is_zero (z *. c +. x +. x') b;
  lemma_add_cancel_eq y y';
  ()

let lemma_mod_mul_mod_right a b c =
  lemma_mul_all ();
  lemma_mod_mul_mod b c a

let lemma_shift_mod a b n =
  lemma_shift_is_mul a n;
  lemma_shift_is_mul (a %. b) n;
  lemma_mod_mul_mod a b (monomial n);
  ()

let lemma_mod_reduce a b c =
  calc (==) {
    (a *. b) %. (b +. c);
    == {lemma_add_zero_right ((a *. b) %. (b +. c))}
    (a *. b) %. (b +. c) +. zero;
    == {lemma_div_mod_exact a (b +. c)}
    (a *. b) %. (b +. c) +. (a *. (b +. c)) %. (b +. c);
    == {lemma_mod_distribute (a *. b) (a *. (b +. c)) (b +. c)}
    (a *. b  +. a *. (b +. c)) %. (b +. c);
    == {lemma_mul_distribute_right a b (b +. c)}
    (a *. (b +. (b +. c))) %. (b +. c);
    == {lemma_add_all ()}
    (a *. c) %. (b +. c);
  }

let lemma_split_define a n =
  let b = monomial n in
  lemma_div_mod a b;
  lemma_shift_is_mul (a /. b) n;
  lemma_shift_define (a /. b) n;
  lemma_add_define_all ();
  lemma_index_all ();
  ()

let lemma_split_define_forward a n =
  lemma_split_define a n

let lemma_combine_define a b n =
  let m = monomial n in
  let ab = a *. m +. b in
  lemma_div_mod ab m;
  lemma_div_mod_unique (a *. m +. b) m a b;
  lemma_shift_is_mul a n;
  lemma_shift_define a n;
  lemma_add_define_all ();
  lemma_index_all ();
  ()

let lemma_mask_is_mod a n =
  lemma_bitwise_all ();
  lemma_split_define a n;
  lemma_equal (mask a n) (a %. monomial n)

let lemma_shift_is_div a n =
  lemma_bitwise_all ();
  lemma_split_define a n;
  lemma_equal (shift a (-n)) (a /. monomial n)

let lemma_mod_monomial a n =
  lemma_index_all ();
  lemma_split_define a n;
  ()

