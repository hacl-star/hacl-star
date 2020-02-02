module Vale.AES.GF128
open FStar.Mul
open Vale.Arch.TypesNative
open Vale.Math.Poly2.Bits

#reset-options "--z3rlimit 20"
let lemma_shift_left_1 a =
  reveal_to_quad32 a;
  reveal_to_quad32 (shift a 1);
  lemma_zero_nth 32;
  lemma_ishl_nth_all 32;
  lemma_ishr_nth_all 32;
  lemma_ixor_nth_all 32;
  lemma_index_all ();
  lemma_shift_define a 1;
  lemma_reverse_define_all ();
  quad32_xor_reveal ();
  reverse_bytes_nat32_reveal ();
  lemma_quad32_vec_equal (to_quad32 (shift a 1)) (quad32_shift_left_1 (to_quad32 a));
  ()

let lemma_shift_2_left_1 lo hi =
  let n = monomial 128 in
  let a = hi *. n +. lo in
  let a' = shift a 1 in
  let (qlo', qhi') = quad32_shift_2_left_1 (to_quad32 lo) (to_quad32 hi) in
  reveal_to_quad32 lo;
  reveal_to_quad32 hi;
  reveal_to_quad32 (a' %. n);
  reveal_to_quad32 (a' /. n);
  lemma_zero_nth 32;
  lemma_ishl_nth_all 32;
  lemma_ishr_nth_all 32;
  lemma_ixor_nth_all 32;
  lemma_index_all ();
  lemma_shift_define a 1;
  lemma_add_define_all ();
  lemma_reverse_define_all ();
  lemma_div_mod a' n;
  lemma_shift_is_mul hi 128;
  lemma_shift_define hi 128;
  lemma_shift_is_mul (a' /. n) 128;
  let lemma_lo () : Lemma (qlo' == to_quad32 (a' %. n)) =
    lemma_shift_define (a' /. n) 128;
    quad32_xor_reveal ();
    reverse_bytes_nat32_reveal ();
    lemma_quad32_vec_equal qlo' (to_quad32 (a' %. n))
    in
  let lemma_hi () : Lemma (qhi' == to_quad32 (a' /. n)) =
    lemma_shift_define_forward (a' /. n) 128;
    quad32_xor_reveal ();
    reverse_bytes_nat32_reveal ();
    lemma_quad32_vec_equal qhi' (to_quad32 (a' /. n))
    in
  lemma_lo ();
  lemma_hi ();
  ()
#reset-options

let lemma_reverse_reverse a n =
  lemma_reverse_define_all ();
  lemma_index_all ();
  lemma_equal a (reverse (reverse a n) n)

let lemma_gf128_degree () =
  lemma_add_define_all ();
  lemma_monomial_define 128;
  lemma_degree_is gf128_modulus_low_terms 7;
  lemma_degree_is (monomial 128) 128;
  lemma_degree_is gf128_modulus 128;
  ()

let lemma_gf128_constant_rev q =
  let n0:nat32 = 0 in
  let n1:nat32 = 0 in
  let n2:nat32 = 0 in
  let n3:nat32 = 0xe1000000 in
  calc (==) {
    Mkfour n0 n1 n2 n3;
    == {lemma_quad32_of_nat32s n0 n1 n2 n3}
    to_quad32 (poly128_of_nat32s n0 n1 n2 n3);
    == {
      lemma_bitwise_all ();
      lemma_to_nat 32 (reverse gf128_modulus_low_terms 31) 0xe1000000;
      lemma_equal (poly128_of_nat32s n0 n1 n2 n3) (reverse gf128_modulus_low_terms 127)
    }
    to_quad32 (reverse gf128_modulus_low_terms 127);
  };
  Vale.Arch.Types.lemma_quad32_xor ()

let lemma_quad32_double_hi_rev a =
  let ra = reverse a 127 in
  lemma_split_define ra 64;
  lemma_split_define_forward a 64;
  lemma_index_all ();
  lemma_add_define_all ();
  lemma_reverse_define_all ();
  lemma_equal (a /. monomial 64) (reverse ra 63);
  lemma_quad32_double a

let lemma_gf128_mul a b c d n =
  let m = monomial n in
  let ab = a *. m +. b in
  let cd = c *. m +. d in
  let ac = a *. c in
  let ad = a *. d in
  let bc = b *. c in
  let bd = b *. d in
  let adh = ad /. m in
  let bch = bc /. m in
  let adl = ad %. m in
  let bcl = bc %. m in
  // ab *. cd
  // (a *. m +. b) *. (c *. m +. d)
  lemma_mul_distribute_right (a *. m +. b) (c *. m) d;
  lemma_mul_distribute_left (a *. m) b (c *. m);
  lemma_mul_distribute_left (a *. m) b d;
  // ((a *. m) *. (c *. m) +. b *. (c *. m)) +. ((a *. m) *. d +. b *. d);
  lemma_mul_associate b c m;
  lemma_mul_associate a m d;
  lemma_mul_commute m d;
  lemma_mul_associate a d m;
  lemma_mul_associate a m (c *. m);
  lemma_mul_associate m c m;
  lemma_mul_commute c m;
  lemma_mul_associate c m m;
  lemma_mul_associate a c (m *. m);
  // (ac *. (m *. m) +. bc *. m) +. (ad *. m +. bd)
  lemma_div_mod ad m;
  lemma_div_mod bc m;
  // (ac *. (m *. m) +. (bch *. m +. bcl) *. m) +. ((adh *. m +. adl) *. m +. bd)
  lemma_mul_distribute_left (bch *. m) bcl m;
  lemma_mul_distribute_left (adh *. m) adl m;
  // (ac *. (m *. m) +. (bch *. m *. m +. bcl *. m)) +. ((adh *. m *. m +. adl *. m) +. bd)
  lemma_mul_associate bch m m;
  lemma_mul_associate adh m m;
  // (ac *. (m *. m) +. (bch *. (m *. m) +. bcl *. m)) +. ((adh *. (m *. m) +. adl *. m) +. bd)
  assert (ab *. cd == (ac *. (m *. m) +. (bch *. (m *. m) +. bcl *. m)) +. ((adh *. (m *. m) +. adl *. m) +. bd));
  lemma_add_define_all ();
  lemma_equal (ab *. cd) ((ac *. (m *. m) +. bch *. (m *. m) +. adh *. (m *. m)) +. (bcl *. m +. adl *. m +. bd));
  // (ac *. (m *. m) +. bch *. (m *. m) +. adh *. (m *. m)) +. (bcl *. m +. adl *. m +. bd)
  lemma_mul_distribute_left ac bch (m *. m);
  lemma_mul_distribute_left (ac +. bch) adh (m *. m);
  // (ac +. bch +. adh) *. (m *. m) +. (bcl *. m +. adl *. m +. bd)
  lemma_mul_monomials n n;
  lemma_shift_is_mul (ac +. bch +. adh) (n + n);
  // shift (ac +. bch +. adh) (n + n) +. (bcl *. m +. adl *. m +. bd)
  ()

let lemma_gf128_reduce a b g n h =
  let ab = a *. b in
  let d = ab /. n in
  let m = ab %. n in
  let dh = d *. h in
  let d' = dh /. n in
  let m' = dh %. n in
  lemma_div_mod ab n;
  lemma_div_mod dh n;
  // ab == d *. n +. m
  // dh == d' *. n +. m'

  // ab % g
  // (d *. n +. m) % g
  lemma_add_define_all ();
  lemma_zero_define ();
  lemma_equal n (g +. h);
  // (d *. (g +. h) +. m) % g
  lemma_mul_distribute_right d g h;
  // (d *. g +. dh +. m) % g
  // (d *. g +. (d' *. n +. m') + m) % g
  // (d *. g +. (d' *. (g +. h) +. m') + m) % g
  lemma_mul_distribute_right d' g h;
  // (d *. g +. (d' *. g +. d' *. h +. m') + m) % g
  lemma_equal ab ((d *. g +. d' *. g) +. (d' *. h +. m' +. m));
  lemma_mul_distribute_left d d' g;
  // ((d +. d') *. g +. (d' *. h +. m' +. m)) % g
  lemma_mod_distribute ((d +. d') *. g) (d' *. h +. m' +. m) g;
  lemma_div_mod_exact (d +. d') g;
  lemma_equal (ab %. g) ((d' *. h +. m' +. m) %. g);
  // (d' *. h +. m' +. m) % g
  lemma_mod_small (d' *. h +. m' +. m) g;
  // d' *. h +. m' +. m
  ()

#reset-options "--max_ifuel 0"
let lemma_gf128_reduce_rev a b h n =
  let m = monomial n in
  let g = m +. h in
  lemma_gf128_reduce a b g m h;
  let r x = reverse x (n - 1) in
  let rr x = reverse x (2 * n - 1) in
  let ab = a *. b in
  let d = (a *. b) /. m in
  let dh = d *. h in
  let rab = rr (a *. b) in
  let rd = rab %. m in
  let rdh = rr (r rd *. h) in
  let rdhL = rdh %. m in
  let rdhLh = r (r rdhL *. h) in
  lemma_add_define_all ();
  lemma_reverse_define_all ();
  lemma_index_all ();

  lemma_split_define ab n;
  lemma_split_define_forward rab n;

  lemma_equal (r rd) d;

  lemma_split_define ab n;
  lemma_split_define_forward rab n;
  lemma_equal (rab /. m) (r (ab %. m));

  lemma_split_define dh n;
  lemma_split_define_forward rdh n;
  lemma_equal (rdh /. m) (r (dh %. m));

  lemma_equal (r rdhL) (dh /. m);
  lemma_equal rdhLh (r ((dh /. m) *. h));

  lemma_equal (r ((a *. b) %. g)) (r ((dh /. m) *. h) +. r (dh %. m) +. r ((a *. b) %. m));
  ()

val lemma_odd_reverse_shift_right (a:poly) (n:pos) : Lemma
  (requires degree a < n /\ a.[0])
  (ensures shift (reverse a (n - 1)) 1 == monomial n +. reverse (shift a (-1)) (n - 1))

let lemma_odd_reverse_shift_right a n =
  lemma_bitwise_all ();
  lemma_equal (shift (reverse a (n - 1)) 1) (monomial n +. reverse (shift a (-1)) (n - 1))

val lemma_mul_odd_reverse_shift_right (a h:poly) (n:pos) : Lemma
  (requires degree h < n /\ degree a < n /\ h.[0])
  (ensures (
    let n1 = n - 1 in
    let m = monomial n in
    reverse (a *. h) (n + n - 1) == reverse a n1 *. m +. reverse a n1 *. reverse (shift h (-1)) n1
  ))

let lemma_mul_odd_reverse_shift_right a h n =
  let n1 = n - 1 in
  let nn1 = n + n - 1 in
  let m = monomial n in
  calc (==) {
    reverse (a *. h) nn1;
    == {lemma_mul_reverse_shift_1 a h n1}
    shift (reverse a n1 *. reverse h n1) 1;
    == {lemma_shift_is_mul_left (reverse a n1 *. reverse h n1) 1}
    monomial 1 *. (reverse a n1 *. reverse h n1);
    == {lemma_mul_all ()}
    reverse a n1 *. (monomial 1 *. reverse h n1);
    == {lemma_shift_is_mul_left (reverse h n1) 1}
    reverse a n1 *. shift (reverse h n1) 1;
    == {lemma_odd_reverse_shift_right h n}
    reverse a n1 *. (m +. reverse (shift h (-1)) n1);
    == {lemma_mul_distribute_right (reverse a n1) m (reverse (shift h (-1)) n1)}
    reverse a n1 *. m +. reverse a n1 *. reverse (shift h (-1)) n1;
  }

val lemma_mul_odd_reverse_shift_right_hi (a h:poly) (n:pos) : Lemma
  (requires degree h < n /\ degree a < n /\ h.[0])
  (ensures (
    let n1 = n - 1 in
    let m = monomial n in
    reverse ((a *. h) /. m) n1 == (reverse a n1 *. reverse (shift h (-1)) n1) %. m
  ))

let lemma_mul_odd_reverse_shift_right_hi a h n =
  let n1 = n - 1 in
  let nn1 = n + n - 1 in
  let m = monomial n in
  let ah = a *. h in
  calc (==) {
    reverse (ah /. m) n1;
    == {lemma_shift_is_div ah n}
    reverse (shift ah (-n)) n1;
    == {lemma_bitwise_all (); lemma_equal (reverse (shift ah (-n)) n1) (mask (reverse ah nn1) n)}
    mask (reverse ah nn1) n;
    == {lemma_mask_is_mod (reverse ah nn1) n}
    reverse ah nn1 %. m;
    == {lemma_mul_odd_reverse_shift_right a h n}
    (reverse a n1 *. m +. reverse a n1 *. reverse (shift h (-1)) n1) %. m;
    == {lemma_mod_distribute (reverse a n1 *. m) (reverse a n1 *. reverse (shift h (-1)) n1) m}
    (reverse a n1 *. m) %. m +. (reverse a n1 *. reverse (shift h (-1)) n1) %. m;
    == {lemma_div_mod_exact (reverse a n1) m}
    zero +. (reverse a n1 *. reverse (shift h (-1)) n1) %. m;
    == {lemma_add_all ()}
    (reverse a n1 *. reverse (shift h (-1)) n1) %. m;
  }

val lemma_mul_odd_reverse_shift_right_lo_shift (a h:poly) (n:pos) : Lemma
  (requires degree h < n /\ degree a < n /\ h.[0])
  (ensures (
    let n1 = n - 1 in
    let m = monomial n in
    reverse (((a *. h) %. m) *. m) (n + n - 1) == reverse a n1 +. (reverse a n1 *. reverse (shift h (-1)) n1) /. m
  ))

let lemma_mul_odd_reverse_shift_right_lo_shift a h n =
  let n1 = n - 1 in
  let nn1 = n + n - 1 in
  let m = monomial n in
  let ah = a *. h in
  calc (==) {
    reverse ((ah %. m) *. m) nn1;
    == {lemma_shift_is_mul (ah %. m) n; lemma_mask_is_mod ah n}
    reverse (shift (mask ah n) n) nn1;
    == {
      lemma_bitwise_all ();
      lemma_equal (reverse (shift (mask ah n) n) nn1) (shift (reverse ah nn1) (-n))
    }
    shift (reverse ah nn1) (-n);
    == {lemma_mul_odd_reverse_shift_right a h n}
    shift (reverse a n1 *. m +. reverse a n1 *. reverse (shift h (-1)) n1) (-n);
    == {lemma_shift_is_mul (reverse a n1) n}
    shift (shift (reverse a n1) n +. reverse a n1 *. reverse (shift h (-1)) n1) (-n);
    == {
      lemma_bitwise_all ();
      lemma_equal (shift (shift (reverse a n1) n +. reverse a n1 *. reverse (shift h (-1)) n1) (-n))
        (reverse a n1 +. shift (reverse a n1 *. reverse (shift h (-1)) n1) (-n))
    }
    reverse a n1 +. shift (reverse a n1 *. reverse (shift h (-1)) n1) (-n);
    == {lemma_shift_is_div (reverse a n1 *. reverse (shift h (-1)) n1) n}
    reverse a n1 +. (reverse a n1 *. reverse (shift h (-1)) n1) /. m;
  }

val lemma_reduce_rev_hi (x3 x2 h:poly) (n:pos) : Lemma
  (requires
    degree x3 < n /\
    degree x2 < n /\
    degree (monomial (n + n) +. h) == n + n /\
    degree h < n /\
    h.[0]
  )
  (ensures (
    let nn = n + n in
    let mm = monomial nn in
    let m = monomial n in
    let g = mm +. h in
    let c = reverse (shift h (-1)) (n - 1) in
    let x32 = (x3 *. m +. x2) *. mm in
    let y0 = reverse x3 (n - 1) in
    let y1 = reverse x2 (n - 1) in
    reverse (x32 %. g) (nn - 1) == (y1 +. mask (y0 *. c) n) *. c +. (shift y1 n +. y0 +. swap (y0 *. c) n)
  ))

let lemma_reduce_rev_hi x3 x2 h n =
  let n1 = n - 1 in
  let nn = n + n in
  let nn1 = n + n - 1 in
  let mm = monomial nn in
  let m = monomial n in
  let g = mm +. h in
  let c = reverse (shift h (-1)) n1 in
  let x32 = (x3 *. m +. x2) *. mm in
  let y0 = reverse x3 n1 in
  let y1 = reverse x2 n1 in
  let x3h = x3 *. h in
  let x3hl = x3h %. m in
  let x3hh = x3h /. m in
  lemma_index_i h 0;
  calc (==) {
    ((x3 *. m +. x2) *. mm) %. (mm +. h);
    == {lemma_mod_reduce (x3 *. m +. x2) mm h}
    ((x3 *. m +. x2) *. h) %. (mm +. h);
    == {lemma_mul_distribute_left (x3 *. m) x2 h}
    (x3 *. m *. h +. x2 *. h) %. (mm +. h);
    == {lemma_mod_distribute (x3 *. m *. h) (x2 *. h) (mm +. h)}
    (x3 *. m *. h) %. (mm +. h) +. (x2 *. h) %. (mm +. h);
    == {lemma_mod_small (x2 *. h) (mm +. h)}
    (x3 *. m *. h) %. (mm +. h) +. x2 *. h;
    == {lemma_mul_all ()}
    (x3h *. m) %. (mm +. h) +. x2 *. h;
    == {lemma_div_mod x3h m}
    ((x3hh *. m +. x3hl) *. m) %. (mm +. h) +. x2 *. h;
    == {lemma_mul_distribute_left (x3hh *. m) x3hl m}
    (x3hh *. m *. m +. x3hl *. m) %. (mm +. h) +. x2 *. h;
    == {lemma_mod_distribute (x3hh *. m *. m) (x3hl *. m) (mm +. h)}
    (x3hh *. m *. m) %. (mm +. h) +. (x3hl *. m) %. (mm +. h) +. x2 *. h;
    == {lemma_mod_small (x3hl *. m) (mm +. h)}
    (x3hh *. m *. m) %. (mm +. h) +. (x3hl *. m) +. x2 *. h;
    == {lemma_mul_associate x3hh m m}
    (x3hh *. (m *. m)) %. (mm +. h) +. (x3hl *. m) +. x2 *. h;
    == {lemma_mul_monomials n n}
    (x3hh *. mm) %. (mm +. h) +. (x3hl *. m) +. x2 *. h;
    == {lemma_mod_reduce x3hh mm h}
    (x3hh *. h) %. (mm +. h) +. (x3hl *. m) +. x2 *. h;
    == {lemma_mod_small (x3hh *. h) (mm +. h)}
    x3hh *. h +. (x3hl *. m) +. x2 *. h;
    == {lemma_add_all ()}
    x3hh *. h +. x2 *. h +. (x3hl *. m);
    == {lemma_mul_distribute_left x3hh x2 h}
    (x3hh +. x2) *. h +. x3hl *. m;
  };
  calc (==) {
    reverse (x32 %. g) nn1;
    == {
      // use the calc result from above (could put nested calc here, but it's slower)
    }
    reverse ((x3hh +. x2) *. h +. x3hl *. m) nn1;
    == {lemma_add_reverse ((x3hh +. x2) *. h) (x3hl *. m) nn1}
    reverse ((x3hh +. x2) *. h) nn1 +. reverse (x3hl *. m) nn1;
    == {lemma_mul_odd_reverse_shift_right_lo_shift x3 h n}
    reverse ((x3hh +. x2) *. h) nn1 +. (y0 +. (y0 *. c) /. m);
    == {lemma_mul_odd_reverse_shift_right (x3hh +. x2) h n}
    reverse (x3hh +. x2) n1 *. m +. reverse (x3hh +. x2) n1 *. c +. (y0 +. (y0 *. c) /. m);
    == {lemma_add_reverse x3hh x2 n1}
    (reverse x3hh n1 +. y1) *. m +. (reverse x3hh n1 +. y1) *. c +. (y0 +. (y0 *. c) /. m);
    == {lemma_mul_distribute_left (reverse x3hh n1) y1 c}
    (reverse x3hh n1 +. y1) *. m +. (reverse x3hh n1 *. c +. y1 *. c) +. (y0 +. (y0 *. c) /. m);
    == {lemma_mul_odd_reverse_shift_right_hi x3 h n}
    ((y0 *. c) %. m +. y1) *. m +. (((y0 *. c) %. m) *. c +. y1 *. c) +. (y0 +. (y0 *. c) /. m);
    == {lemma_mul_distribute_left ((y0 *. c) %. m) y1 c}
    ((y0 *. c) %. m +. y1) *. m +. ((y0 *. c) %. m +. y1) *. c +. (y0 +. (y0 *. c) /. m);
    == {
      lemma_shift_is_div (y0 *. c) n;
      lemma_mask_is_mod (y0 *. c) n;
      lemma_shift_is_mul ((y0 *. c) %. m +. y1) n
    }
    shift (mask (y0 *. c) n +. y1) n +. (mask (y0 *. c) n +. y1) *. c +. (y0 +. shift (y0 *. c) (-n));
    == {lemma_add_all ()}
    (y1 +. mask (y0 *. c) n) *. c +. (shift (mask (y0 *. c) n +. y1) n +. (y0 +. shift (y0 *. c) (-n)));
    == {
      lemma_bitwise_all ();
      lemma_equal (shift (mask (y0 *. c) n +. y1) n +. (y0 +. shift (y0 *. c) (-n)))
        (shift y1 n +. y0 +. swap (y0 *. c) n)
    }
    (y1 +. mask (y0 *. c) n) *. c +. (shift y1 n +. y0 +. swap (y0 *. c) n);
  }

#reset-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0"
let lemma_swap_right (a b:poly) (n:nat) : Lemma
  (requires n == 64 /\ degree a < n + n /\ degree b < n + n)
  (ensures swap (swap a n +. b) n == a +. swap b n)
  =
  lemma_bitwise_all ();
  lemma_equal (swap (swap a n +. b) n) (a +. swap b n)

#reset-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0"
let lemma_reduce_rev_bits (a0 a1 a2 c:poly) (n:pos) : Lemma
  (requires
    n == 64 /\ // verification times out unless n is known
    degree a0 < n + n /\
    degree a1 < n + n /\
    degree a2 < n + n /\
    degree c < n
  )
  (ensures (
    let n1 = n - 1 in
    let nn = n + n in
    let nnn = nn + n in
    let rev a = reverse a (nn - 1) in
    let y_10 = a0 +. shift (mask a1 n) n in
    let y_0 = mask y_10 n in
    let y_10c = swap y_10 n +. y_0 *. c in
    let a = a0 +. shift a1 n +. shift a2 nn in
    let x = reverse a (nn + nn - 1) in
    let x0 = mask x n in
    let x1 = mask (shift x (-n)) n in
    let x2 = mask (shift x (-nn)) n in
    let x3 = shift x (-nnn) in
    let y0 = reverse x3 n1 in
    let y1 = reverse x2 n1 in
    (rev (x0 +. shift x1 n) +. ((y1 +. mask (y0 *. c) n) *. c +. (shift y1 n +. y0 +. swap (y0 *. c) n))) ==
      (swap y_10c n +. (a2 +. shift a1 (-n)) +. mask y_10c n *. c)
  ))
=
  let n1 = n - 1 in
  let nn = n + n in
  let nnn = nn + n in
  let rev a = reverse a (nn - 1) in
  let y_10 = a0 +. shift (mask a1 n) n in
  let y_0 = mask y_10 n in
  let y_10c = swap y_10 n +. y_0 *. c in
  let a = a0 +. shift a1 n +. shift a2 nn in
  let x = reverse a (nn + nn - 1) in
  let x0 = mask x n in
  let x1 = mask (shift x (-n)) n in
  let x2 = mask (shift x (-nn)) n in
  let x3 = shift x (-nnn) in
  let y0 = reverse x3 n1 in
  let y1 = reverse x2 n1 in
  calc (==) {
    y0;
    == {lemma_bitwise_all (); lemma_equal y0 y_0}
    y_0;
  };
  calc (==) {
    shift y1 n +. y0;
    == {lemma_bitwise_all (); lemma_equal (shift y1 n +. y0) y_10}
    y_10;
  };
  calc (==) {
    (shift y1 n +. y0 +. swap (y0 *. c) n);
    == {lemma_swap_right (shift y1 n +. y0) (y0 *. c) 64}
    swap (swap y_10 n +. y_0 *. c) n;
  };
  calc (==) {
    rev (x0 +. shift x1 n);
    == {lemma_bitwise_all (); lemma_equal (rev (x0 +. shift x1 n)) (a2 +. shift a1 (-n))}
    a2 +. shift a1 (-n);
  };
  calc (==) {
    y1 +. mask (y0 *. c) n;
    == {lemma_bitwise_all (); lemma_equal (y1 +. mask (y0 *. c) n) (mask y_10c n)}
    mask y_10c n;
  };
  calc (==) {
    (rev (x0 +. shift x1 n) +. ((y1 +. mask (y0 *. c) n) *. c +. (shift y1 n +. y0 +. swap (y0 *. c) n)));
    == {lemma_add_all ()}
    (shift y1 n +. y0 +. swap (y0 *. c) n) +. rev (x0 +. shift x1 n) +. (y1 +. mask (y0 *. c) n) *. c;
  }

#reset-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0"
let lemma_reduce_rev a0 a1 a2 h n =
  (*
    <-----256 bits------>
    |   a2    |
  +      |   a1    |
  +           |    a0   |
  -----------------------
  = | y3 | y2 | y1 | y0 |
    |         |   y_10  |
  *)
  let n1 = n - 1 in
  let nn = n + n in
  let nnn = nn + n in
  let rev a = reverse a (nn - 1) in
  let mm = monomial nn in
  let m = monomial n in
  let g = mm +. h in
  let c = reverse (shift h (-1)) (n - 1) in
  let y_10 = a0 +. shift (mask a1 n) n in
  let y_0 = mask y_10 n in
  let y_10c = swap y_10 n +. y_0 *. c in
  let a = a0 +. shift a1 n +. shift a2 nn in
  let x = reverse a (nn + nn - 1) in
  let x0 = mask x n in
  let x1 = mask (shift x (-n)) n in
  let x2 = mask (shift x (-nn)) n in
  let x3 = shift x (-nnn) in
  let x32 = (x3 *. m +. x2) *. mm in
  let y0 = reverse x3 n1 in
  let y1 = reverse x2 n1 in
  calc (==) {
    x %. g;
    == {
      lemma_bitwise_all ();
      lemma_equal x ((x0 +. shift x1 n) +. shift (x2 +. shift x3 n) nn)
    }
    ((x0 +. shift x1 n) +. shift (x2 +. shift x3 n) nn) %. g;
    == {lemma_mod_distribute (x0 +. shift x1 n) (shift (x2 +. shift x3 n) nn) g}
    (x0 +. shift x1 n) %. g +. shift (x2 +. shift x3 n) nn %. g;
    == {lemma_mod_small (x0 +. shift x1 n) g}
    x0 +. shift x1 n +. shift (x2 +. shift x3 n) nn %. g;
  };
  calc (==) {
    rev (x %. g);
    == {
      lemma_bitwise_all ();
      lemma_equal (rev (x %. g)) (rev (x0 +. shift x1 n) +. rev (shift (x2 +. shift x3 n) nn %. g))
    }
    rev (x0 +. shift x1 n) +. rev (shift (x2 +. shift x3 n) nn %. g);
    == {lemma_add_commute x2 (shift x3 n); lemma_shift_is_mul (x2 +. shift x3 n) nn; lemma_shift_is_mul x3 n}
    rev (x0 +. shift x1 n) +. rev (x32 %. g);
    == {lemma_reduce_rev_hi x3 x2 h n}
    rev (x0 +. shift x1 n) +. ((y1 +. mask (y0 *. c) n) *. c +. (shift y1 n +. y0 +. swap (y0 *. c) n));
    == {lemma_reduce_rev_bits a0 a1 a2 c n}
    swap y_10c n +. (a2 +. shift a1 (-n)) +. mask y_10c n *. c;
  }

let lemma_gf128_low_shift () =
  let n0:nat32 = 0 in
  let n1:nat32 = 0 in
  let n2:nat32 = 0 in
  let n3:nat32 = 0xc2000000 in
  let r3 = gf128_low_shift in
  calc (==) {
    shift (of_quad32 (Mkfour n0 n1 n2 n3)) (-64);
    == {
      calc (==) {
        Mkfour n0 n1 n2 n3;
        == {lemma_quad32_of_nat32s n0 n1 n2 n3}
        to_quad32 (poly128_of_nat32s n0 n1 n2 n3);
        == {
          lemma_bitwise_all ();
          lemma_to_nat 32 (reverse r3 31) n3;
          lemma_equal (poly128_of_nat32s n0 n1 n2 n3) (reverse r3 127)
        }
        to_quad32 (reverse r3 127);
      }
    }
    shift (of_quad32 (to_quad32 (reverse r3 127))) (-64);
    == {lemma_of_to_quad32 (reverse r3 127)}
    shift (reverse r3 127) (-64);
    == {
      lemma_bitwise_all ();
      lemma_equal (shift (reverse r3 127) (-64)) (reverse r3 63)
    }
    reverse r3 63;
  }

let lemma_gf128_high_bit () =
  let n0:nat32 = 0 in
  let n1:nat32 = 0 in
  let n2:nat32 = 0 in
  let n3:nat32 = 0x80000000 in
  let a = monomial 127 in
  let a3 = monomial 31 in
  calc (==) {
    of_quad32 (Mkfour n0 n1 n2 n3);
    == {lemma_quad32_of_nat32s n0 n1 n2 n3}
    of_quad32 (to_quad32 (poly128_of_nat32s n0 n1 n2 n3));
    == {
      lemma_bitwise_all ();
      lemma_to_nat 32 a3 n3;
      lemma_equal (poly128_of_nat32s n0 n1 n2 n3) a
    }
    of_quad32 (to_quad32 a);
    == {lemma_of_to_quad32 a}
    a;
  }

let lemma_gf128_low_shift_1 () =
  let n0:nat32 = 1 in
  let n1:nat32 = 0 in
  let n2:nat32 = 0 in
  let n3:nat32 = 0xc2000000 in
  let a = reverse (shift (monomial 128 +. gf128_modulus_low_terms) (-1)) 127 in
  let a0 = one in
  let a3 = reverse gf128_low_shift 31 in
  calc (==) {
    of_quad32 (Mkfour n0 n1 n2 n3);
    == {lemma_quad32_of_nat32s n0 n1 n2 n3}
    of_quad32 (to_quad32 (poly128_of_nat32s n0 n1 n2 n3));
    == {
      lemma_bitwise_all ();
      lemma_to_nat 32 a0 n0;
      lemma_to_nat 32 a3 n3;
      lemma_equal (poly128_of_nat32s n0 n1 n2 n3) a
    }
    of_quad32 (to_quad32 a);
    == {lemma_of_to_quad32 a}
    a;
  }

let lemma_gf128_mul_rev_commute a b =
  lemma_mul_all ()

let lemma_gf128_mul_rev_associate a b c =
  let rev x = reverse x 127 in
  let ra = rev a in
  let rb = rev b in
  let rc = rev c in
  let g = gf128_modulus in
  lemma_gf128_degree ();
  calc (==) {
    a *~ (b *~ c);
    == {}
    rev (ra *. (rb *. rc %. g) %. g);
    == {lemma_mod_mul_mod_right ra (rb *. rc) g}
    rev (ra *. (rb *. rc) %. g);
    == {lemma_mul_associate ra rb rc}
    rev ((ra *. rb) *. rc %. g);
    == {lemma_mod_mul_mod (ra *. rb) g rc}
    rev ((ra *. rb %. g) *. rc %. g);
    == {}
    (a *~ b) *~ c;
  }

let lemma_gf128_mul_rev_distribute_left a b c =
  let rev x = reverse x 127 in
  let ra = rev a in
  let rb = rev b in
  let rc = rev c in
  let g = gf128_modulus in
  lemma_gf128_degree ();
  calc (==) {
    (a +. b) *~ c;
    == {}
    rev (rev (a +. b) *. rc %. g);
    == {lemma_add_reverse a b 127}
    rev ((ra +. rb) *. rc %. g);
    == {lemma_mul_distribute_left ra rb rc}
    rev ((ra *. rc +. rb *. rc) %. g);
    == {lemma_mod_distribute (ra *. rc) (rb *. rc) g}
    rev (ra *. rc %. g +. rb *. rc %. g);
    == {lemma_add_reverse (ra *. rc %. g) (rb *. rc %. g) 127}
    rev (ra *. rc %. g) +. rev (rb *. rc %. g);
    == {}
    (a *~ c) +. (b *~ c);
  }

let lemma_gf128_mul_rev_distribute_right a b c =
  calc (==) {
    a *~ (b +. c);
    == {lemma_gf128_mul_rev_commute a (b +. c)}
    (b +. c) *~ a;
    == {lemma_gf128_mul_rev_distribute_left b c a}
    b *~ a +. c *~ a;
    == {lemma_gf128_mul_rev_commute a b; lemma_gf128_mul_rev_commute a c}
    a *~ b +. a *~ c;
  }

let lemma_add_mod_rev n a1 a2 b =
  let rev x = reverse x (n - 1) in
  let rev' x = reverse x (n + n - 1) in
  calc (==) {
    // mod_rev n (a1 +. a2) b;
    rev (rev' (a1 +. a2) %. b);
    == {lemma_add_reverse a1 a2 (n + n - 1)}
    rev ((rev' a1 +. rev' a2) %. b);
    == {lemma_mod_distribute (rev' a1) (rev' a2) b}
    rev (rev' a1 %. b +. rev' a2 %. b);
    == {lemma_add_reverse (rev' a1 %. b) (rev' a2 %. b) (n - 1)}
    rev (rev' a1 %. b) +. rev (rev' a2 %. b);
    // mod_rev n a1 b +. mod_rev n a2 b
  }

let lemma_shift_key_1 n f h =
  let g = monomial n +. f in
  lemma_monomial_add_degree n f;
  let rev x = reverse x (n - 1) in
  let h1 = shift h 1 in
  let offset = reverse (shift g (-1)) (n - 1) in
  if h1.[n] then
    calc (==) {
      shift (rev (mask h1 n +. offset)) 1 %. g;
      == {
        lemma_bitwise_all ();
        lemma_equal (shift (rev (mask h1 n +. offset)) 1) (rev h +. g)
      }
      (rev h +. g) %. g;
      == {lemma_mod_distribute (rev h) g g; lemma_mod_cancel g; lemma_add_all ()}
      rev h %. g;
    }
  else
    calc (==) {
      shift (rev (mask h1 n +. zero)) 1 %. g;
      == {
        lemma_bitwise_all ();
        lemma_equal (shift (rev (mask h1 n +. zero)) 1) (rev h)
      }
      rev h %. g;
    }

let lemma_test_high_bit a =
  calc (==) {
    of_nat ((to_quad32 (monomial 127)).hi3);
    == {lemma_quad32_extract_nat32s (monomial 127)}
    shift (monomial 127) (-96);
  };
  calc (==) {
    of_nat (to_quad32 (poly_and a (monomial 127))).hi3;
    == {lemma_quad32_extract_nat32s (poly_and a (monomial 127))}
    shift (poly_and a (monomial 127)) (-96);
  };
  if (shift (monomial 127) (-96) = shift (poly_and a (monomial 127)) (-96)) then
  (
    of_nat32_eq (to_quad32 (poly_and a (monomial 127))).hi3 ((to_quad32 (monomial 127)).hi3);
    lemma_bitwise_all ();
    assert ((shift (monomial 127) (-96)).[31]);
    assert ((shift (poly_and a (monomial 127)) (-96)).[31]);
    assert (a.[127]);
    ()
  );
  if a.[127] then
  (
    lemma_bitwise_all ();
    lemma_equal (shift (monomial 127) (-96)) (shift (poly_and a (monomial 127)) (-96));
    ()
  )

let lemma_Mul128 a b =
  let aL = mask a 64 in
  let bL = mask b 64 in
  let aH = shift a (-64) in
  let bH = shift b (-64) in
  calc (==) {
    a *. b;
    == {
      lemma_bitwise_all ();
      lemma_equal a (aL +. shift aH 64);
      lemma_equal b (bL +. shift bH 64)
    }
    (aL +. shift aH 64) *. (bL +. shift bH 64);
    == {lemma_mul_distribute_left aL (shift aH 64) (bL +. shift bH 64)}
    aL *. (bL +. shift bH 64) +. shift aH 64 *. (bL +. shift bH 64);
    == {lemma_mul_distribute_right aL bL (shift bH 64)}
    aL *. bL +. aL *. shift bH 64 +. shift aH 64 *. (bL +. shift bH 64);
    == {lemma_mul_distribute_right (shift aH 64) bL (shift bH 64)}
    aL *. bL +. aL *. shift bH 64 +. (shift aH 64 *. bL +. shift aH 64 *. shift bH 64);
    == {lemma_add_all ()}
    aL *. bL +. (aL *. shift bH 64 +. shift aH 64 *. bL) +. shift aH 64 *. shift bH 64;
    == {lemma_shift_is_mul aH 64; lemma_shift_is_mul bH 64}
    aL *. bL +. (aL *. (bH *. monomial 64) +. aH *. monomial 64 *. bL) +. aH *. monomial 64 *. (bH *. monomial 64);
    == {lemma_mul_all ()}
    aL *. bL +. (aL *. bH *. monomial 64 +. aH *. bL *. monomial 64) +. aH *. bH *. (monomial 64 *. monomial 64);
    == {lemma_mul_monomials 64 64}
    aL *. bL +. (aL *. bH *. monomial 64 +. aH *. bL *. monomial 64) +. aH *. bH *. monomial 128;
    == {lemma_mul_distribute_left (aL *. bH) (aH *. bL) (monomial 64)}
    aL *. bL +. (aL *. bH +. aH *. bL) *. monomial 64 +. aH *. bH *. monomial 128;
    == {lemma_shift_is_mul (aL *. bH +. aH *. bL) 64; lemma_shift_is_mul (aH *. bH) 128}
    aL *. bL +. shift (aL *. bH +. aH *. bL) 64 +. shift (aH *. bH) 128;
  }

let lemma_Mul128_accum z0 z1 z2 a b =
  let z = z0 +. shift z1 64 +. shift z2 128 in
  let aL = mask a 64 in
  let bL = mask b 64 in
  let aH = shift a (-64) in
  let bH = shift b (-64) in
  calc (==) {
    z +. a *. b;
    == {lemma_Mul128 a b}
    z +. (aL *. bL +. shift (aL *. bH +. aH *. bL) 64 +. shift (aH *. bH) 128);
    == {lemma_shift_is_mul (aL *. bH +. aH *. bL) 64; lemma_shift_is_mul (aH *. bH) 128}
    z +. (aL *. bL +. (aL *. bH +. aH *. bL) *. monomial 64 +. aH *. bH *. monomial 128);
    == {lemma_mul_distribute_left (aL *. bH) (aH *. bL) (monomial 64)}
    z +. (aL *. bL +. (aL *. bH *. monomial 64 +. aH *. bL *. monomial 64) +. aH *. bH *. monomial 128);
    == {lemma_add_all ()}
    z0 +. aL *. bL +. (shift z1 64 +. aL *. bH *. monomial 64 +. aH *. bL *. monomial 64) +. (shift z2 128 +. aH *. bH *. monomial 128);
    == {lemma_shift_is_mul z1 64; lemma_shift_is_mul z2 128}
    z0 +. aL *. bL +. (z1 *. monomial 64 +. aL *. bH *. monomial 64 +. aH *. bL *. monomial 64) +. (z2 *. monomial 128 +. aH *. bH *. monomial 128);
    == {lemma_mul_distribute_left z1 (aL *. bH) (monomial 64)}
    z0 +. aL *. bL +. ((z1 +. aL *. bH) *. monomial 64 +. aH *. bL *. monomial 64) +. (z2 *. monomial 128 +. aH *. bH *. monomial 128);
    == {lemma_mul_distribute_left (z1 +. aL *. bH) (aH *. bL) (monomial 64)}
    z0 +. aL *. bL +. (z1 +. aL *. bH +. aH *. bL) *. monomial 64 +. (z2 *. monomial 128 +. aH *. bH *. monomial 128);
    == {lemma_mul_distribute_left z2 (aH *. bH) (monomial 128)}
    z0 +. aL *. bL +. (z1 +. aL *. bH +. aH *. bL) *. monomial 64 +. (z2 +. aH *. bH) *. monomial 128;
    == {lemma_shift_is_mul (z1 +. aL *. bH +. aH *. bL) 64; lemma_shift_is_mul (z2 +. aH *. bH) 128}
    (z0 +. aL *. bL) +. shift (z1 +. aL *. bH +. aH *. bL) 64 +. shift (z2 +. aH *. bH) 128;
  }

