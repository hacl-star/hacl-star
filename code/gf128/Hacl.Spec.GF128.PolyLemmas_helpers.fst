module Hacl.Spec.GF128.PolyLemmas_helpers

open FStar.Mul

open Vale.Math.Poly2.Bits

let lemma_mul_h_shift_right a h =
  lemma_bitwise_all ();
  calc (==) {
    a *. h;
    == {lemma_equal h (monomial 63 +. monomial 62 +. monomial 57)}
    a *. (monomial 63 +. monomial 62 +. monomial 57);
    == {lemma_mul_distribute_right a (monomial 63 +. monomial 62) (monomial 57)}
    (a *. (monomial 63 +. monomial 62)) +. (a *. monomial 57);
    == {lemma_mul_distribute_right a (monomial 63) (monomial 62)}
    (a *. monomial 63) +. (a *. monomial 62) +. (a *. monomial 57);
    == {
      lemma_shift_is_mul a 63;
      lemma_shift_is_mul a 62;
      lemma_shift_is_mul a 57
    }
    (shift a 63) +. (shift a 62) +. (shift a 57);
  }

let lemma_mul_h_shift_right_mod a h =
  calc (==) {
    (a *. h) %. monomial 64;
    == {lemma_mul_h_shift_right a h}
    (shift a 63 +. shift a 62 +. shift a 57) %. monomial 64;
    == {lemma_mod_distribute (shift a 63 +. shift a 62) (shift a 57) (monomial 64)}
    (shift a 63 +. shift a 62) %. monomial 64 +. shift a 57 %. monomial 64;
    == {lemma_mod_distribute (shift a 63) (shift a 62) (monomial 64)}
    shift a 63 %. monomial 64 +. shift a 62 %. monomial 64 +. shift a 57 %. monomial 64;
  }

let lemma_mul_h_shift_left a h =
  lemma_bitwise_all ();
  lemma_shift_is_div (a *. h) 64;
  lemma_mul_h_shift_right a h;
  lemma_equal (shift (shift a 63 +. shift a 62 +. shift a 57) (-64))
    (shift (shift a 63) (-64) +. shift (shift a 62) (-64) +. shift (shift a 57) (-64));
  lemma_shift_shift a 63 (-64);
  lemma_shift_shift a 62 (-64);
  lemma_shift_shift a 57 (-64)

let lemma_mul_h a h =
  lemma_div_mod (a *. h) (monomial 64);
  lemma_mul_h_shift_right a h;
  lemma_mul_h_shift_left a h

val lemma_h_2 (h:poly) : Lemma
  (requires h == reverse gf128_low_shift 63)
  (ensures h *. h == monomial 126 +. monomial 124 +. monomial 114)

let lemma_h_2 h =
  lemma_bitwise_all ();
  calc (==) {
    h *. h;
    == {lemma_equal h (monomial 63 +. monomial 62 +. monomial 57)}
    (monomial 63 +. monomial 62 +. monomial 57) *. h;
    == {lemma_mul_distribute_left (monomial 63 +. monomial 62) (monomial 57) h}
    (monomial 63 +. monomial 62) *. h +. (monomial 57) *. h;
    == {lemma_mul_distribute_left (monomial 63) (monomial 62) h}
    (monomial 63) *. h +. (monomial 62) *. h +. (monomial 57) *. h;
    == {lemma_equal h (monomial 63 +. monomial 62 +. monomial 57)}
    (monomial 63) *. (monomial 63 +. monomial 62 +. monomial 57) +.
      (monomial 62) *. (monomial 63 +. monomial 62 +. monomial 57) +.
      (monomial 57) *. (monomial 63 +. monomial 62 +. monomial 57);
    == {
      lemma_mul_distribute_right (monomial 63) (monomial 63 +. monomial 62) (monomial 57);
      lemma_mul_distribute_right (monomial 62) (monomial 63 +. monomial 62) (monomial 57);
      lemma_mul_distribute_right (monomial 57) (monomial 63 +. monomial 62) (monomial 57)
    }
    (monomial 63 *. (monomial 63 +. monomial 62) +. monomial 63 *. monomial 57) +.
      (monomial 62 *. (monomial 63 +. monomial 62) +. monomial 62 *. monomial 57) +.
      (monomial 57 *. (monomial 63 +. monomial 62) +. monomial 57 *. monomial 57);
    == {
      lemma_mul_distribute_right (monomial 63) (monomial 63) (monomial 62);
      lemma_mul_distribute_right (monomial 62) (monomial 63) (monomial 62);
      lemma_mul_distribute_right (monomial 57) (monomial 63) (monomial 62)
    }
    (monomial 63 *. monomial 63 +. monomial 63 *. monomial 62 +. monomial 63 *. monomial 57) +.
      (monomial 62 *. monomial 63 +. monomial 62 *. monomial 62 +. monomial 62 *. monomial 57) +.
      (monomial 57 *. monomial 63 +. monomial 57 *. monomial 62 +. monomial 57 *. monomial 57);
    == {
      lemma_mul_monomials 63 63; lemma_mul_monomials 63 62; lemma_mul_monomials 63 57;
      lemma_mul_monomials 62 63; lemma_mul_monomials 62 62; lemma_mul_monomials 62 57;
      lemma_mul_monomials 57 63; lemma_mul_monomials 57 62; lemma_mul_monomials 57 57
    }
    (monomial 126 +. monomial 125 +. monomial 120) +.
      (monomial 125 +. monomial 124 +. monomial 119) +.
      (monomial 120 +. monomial 119 +. monomial 114);
    == {
      lemma_equal ((monomial 126 +. monomial 125 +. monomial 120) +.
        (monomial 125 +. monomial 124 +. monomial 119) +.
        (monomial 120 +. monomial 119 +. monomial 114)) (monomial 126 +. monomial 124 +. monomial 114)
    }
    monomial 126 +. monomial 124 +. monomial 114;
  }

let lemma_mul_h_2_zero a h =
  reveal_defs ();
  calc (==) {
    (((a *. h) %. monomial 64) *. h) %. monomial 64;
    == {lemma_mod_mul_mod (a *. h) (monomial 64) h}
    ((a *. h) *. h) %. monomial 64;
    == {lemma_mul_associate a h h}
    (a *. (h *. h)) %. monomial 64;
    == {lemma_mod_mul_mod_right a (h *. h) (monomial 64)}
    (a *. ((h *. h) %. monomial 64)) %. monomial 64;
    == {lemma_h_2 h}
    (a *. ((monomial 126 +. monomial 124 +. monomial 114) %. monomial 64)) %. monomial 64;
    == {lemma_mod_distribute (monomial 126 +. monomial 124) (monomial 114) (monomial 64)}
    (a *. ((monomial 126 +. monomial 124) %. monomial 64 +. monomial 114 %. monomial 64)) %. monomial 64;
    == {lemma_mod_distribute (monomial 126) (monomial 124) (monomial 64)}
    (a *. (monomial 126 %. monomial 64 +. monomial 124 %. monomial 64 +. monomial 114 %. monomial 64)) %. monomial 64;
    == {
      lemma_mul_monomials 62 64;
      lemma_add_zero (monomial 126);
      lemma_div_mod_unique ((monomial 126) +. zero) (monomial 64) (monomial 62) zero;
      // --> monomial 126 %. monomial 64 == zero
      lemma_mul_monomials 60 64;
      lemma_add_zero (monomial 124);
      lemma_div_mod_unique ((monomial 124) +. zero) (monomial 64) (monomial 60) zero;
      // --> monomial 124 %. monomial 64 == zero
      lemma_mul_monomials 50 64;
      lemma_add_zero (monomial 114);
      lemma_div_mod_unique ((monomial 114) +. zero) (monomial 64) (monomial 50) zero
      // --> monomial 114 %. monomial 64 == zero
    }
    (a *. (zero +. zero +. zero)) %. monomial 64;
    == {lemma_add_zero zero}
    (a *. zero) %. monomial 64;
    == {lemma_mul_zero a}
    zero;
  }

let lemma_shift_left_cancel a a0 a1 =
  reveal_defs ();
  calc (==) {
    shift (((shift a1 64) +. a0) %. monomial 64) 64;
    == {lemma_shift_is_mul a1 64}
    shift ((a1 *. monomial 64 +. a0) %. monomial 64) 64;
    == {lemma_mod_distribute (a1 *. monomial 64) a0 (monomial 64)}
    shift ((a1 *. monomial 64) %. monomial 64 +. a0 %. monomial 64) 64;
    == {lemma_mod_small a0 (monomial 64)}
    shift ((a1 *. monomial 64) %. monomial 64 +. a0) 64;
    == {lemma_mod_mul_mod_right a1 (monomial 64) (monomial 64)}
    shift ((a1 *. (mod (monomial 64) (monomial 64))) %. monomial 64 +. a0) 64;
    == {lemma_mod_cancel (monomial 64)}
    shift ((a1 *. zero) %. monomial 64 +. a0) 64;
    == {lemma_mul_zero a1; lemma_add_zero_left a0}
    shift a0 64;
  }

let lemma_shift_right_cancel a a0 a1 =
  lemma_shift_is_div a 64;
  lemma_shift_is_mul a1 64;
  lemma_div_mod_unique a (monomial 64) a1 a0

let lemma_add_left_shift a0 a1 b =
  lemma_bitwise_all ();
  calc (==) {
    (shift a1 64) +. a0 +. (shift b 64);
    == {lemma_add_commute (shift a1 64) a0}
    a0 +. (shift a1 64) +. (shift b 64);
    == {lemma_add_associate a0 (shift a1 64) (shift b 64)}
    a0 +. ((shift a1 64) +. (shift b 64));
    == {lemma_shift_is_mul a1 64; lemma_shift_is_mul b 64}
    a0 +. (a1 *. monomial 64 +. b *. monomial 64);
    == {lemma_mul_distribute_left a1 b (monomial 64)}
    a0 +. (a1 +. b) *. monomial 64;
    == {lemma_shift_is_mul (a1 +. b) 64}
    a0 +. (shift (a1 +. b) 64);
    == {lemma_add_commute a0 (shift (a1 +. b) 64)}
    (shift (a1 +. b) 64) +. a0;
  }

let lemma_add_left_shift_double a0 a1 b0 b1 =
  lemma_bitwise_all ();
  calc (==) {
    (shift a1 64) +. a0 +. (shift b1 64 +. b0);
    == {lemma_add_associate ((shift a1 64) +. a0) (shift b1 64) b0}
    ((shift a1 64) +. a0 +. shift b1 64) +. b0;
    == {lemma_add_commute (shift a1 64) a0}
    (a0 +. (shift a1 64) +. shift b1 64) +. b0;
    == {lemma_add_associate a0 (shift a1 64) (shift b1 64)}
    (a0 +. (shift a1 64 +. shift b1 64)) +. b0;
    == {lemma_shift_is_mul a1 64; lemma_shift_is_mul b1 64}
    (a0 +. (a1 *. monomial 64 +. b1 *. monomial 64)) +. b0;
    == {lemma_mul_distribute_left a1 b1 (monomial 64)}
    (a0 +. (a1 +. b1) *. monomial 64) +. b0;
    == {lemma_shift_is_mul (a1 +. b1) 64}
    (a0 +. (shift (a1 +. b1) 64)) +. b0;
    == {lemma_add_commute a0 (shift (a1 +. b1) 64)}
    ((shift (a1 +. b1) 64) +. a0) +. b0;
    == {lemma_add_associate (shift (a1 +. b1) 64) a0 b0}
    (shift (a1 +. b1) 64) +. (a0 +. b0);
  }

val lemma_mul_128_x (a:poly) : Lemma
  (requires degree a <= 127 )
  (ensures (
    let n = monomial 64 in
    let nn = monomial 128 in
    let l0_r63 = shift (a %. n) (-63) in
    let l1_r63 = shift (a /. n) (-63) in
    let l0_l1 = (shift (a %. n) 1) %. n in
    let l1_l1 = (shift (a /. n) 1) %. n in
    a *. monomial 1 == l1_r63 *. nn +. (l1_l1 +. l0_r63) *. n +. l0_l1
  ))

let lemma_mul_128_x a =
  let n = monomial 64 in
  let nn = monomial 128 in
  let l0_r63 = shift (a %. n) (-63) in
  let l1_r63 = shift (a /. n) (-63) in
  let l0_l1 = (shift (a %. n) 1) %. n in
  let l1_l1 = (shift (a /. n) 1) %. n in
  calc (==) {
    a *. monomial 1;
    == {lemma_div_mod a n}
    ((a /. n) *. n +. (a %. n)) *. monomial 1;
    == {lemma_mul_distribute_left ((a /. n) *. n) (a %. n) (monomial 1)}
    ((a /. n) *. n) *. monomial 1 +. (a %. n) *. monomial 1;
    == {lemma_shift_is_mul (a %. n) 1}
    ((a /. n) *. n) *. monomial 1 +. (shift (a %. n) 1);
    == {lemma_div_mod (shift (a %. n) 1) n}
    ((a /. n) *. n) *. monomial 1 +.
      (((shift (a %. n) 1) /. n) *. n +. ((shift (a %. n) 1) %. n));
    == {lemma_shift_is_div (shift (a %. n) 1) 64}
    ((a /. n) *. n) *. monomial 1 +.
      ((shift (shift (a %. n) 1) (-64)) *. n +. ((shift (a %. n) 1) %. n));
    == {lemma_shift_shift (a %. n) 1 (-64)}
    ((a /. n) *. n) *. monomial 1 +. (l0_r63 *. n +. l0_l1);
    == {
      lemma_mul_commute (a /. n) n;
      lemma_mul_associate n (a /. n) (monomial 1);
      lemma_mul_commute n ((a /. n) *. monomial 1)
    }
    ((a /. n) *. monomial 1) *. n +. (l0_r63 *. n +. l0_l1);
    == {lemma_shift_is_mul (a /. n) 1}
    (shift (a /. n) 1) *. n +. (l0_r63 *. n +. l0_l1);
    == {lemma_div_mod (shift (a /. n) 1) n}
    (((shift (a /. n) 1) /. n) *. n +. ((shift (a /. n) 1) %. n)) *. n +.
      (l0_r63 *. n +. l0_l1);
    == {lemma_mul_distribute_left (((shift (a /. n) 1) /. n) *. n) ((shift (a /. n) 1) %. n) n}
    (((shift (a /. n) 1) /. n) *. n *. n +. ((shift (a /. n) 1) %. n) *. n) +.
      (l0_r63 *. n +. l0_l1);
    == {lemma_shift_is_div (shift (a /. n) 1) 64}
    ((shift (shift (a /. n) 1) (-64)) *. n *. n +. ((shift (a /. n) 1) %. n) *. n) +.
      (l0_r63 *. n +. l0_l1);
    == {lemma_shift_shift (a /. n) 1 (-64)}
    ((shift (a /. n) (-63)) *. n *. n +. ((shift (a /. n) 1) %. n) *. n) +.
      (l0_r63 *. n +. l0_l1);
    == {lemma_mul_associate (shift (a /. n) (-63)) n n; lemma_mul_monomials 64 64}
    l1_r63 *. nn +. l1_l1 *. n +. (l0_r63 *. n +. l0_l1);
    == {lemma_add_associate (l1_r63 *. nn +. l1_l1 *. n) (l0_r63 *. n) l0_l1}
    (l1_r63 *. nn +. l1_l1 *. n +. l0_r63 *. n) +. l0_l1;
    == {lemma_add_associate (l1_r63 *. nn) (l1_l1 *. n) (l0_r63 *. n)}
    l1_r63 *. nn +. (l1_l1 *. n +. l0_r63 *. n) +. l0_l1;
    == {lemma_mul_distribute_left l1_l1 l0_r63 n}
    l1_r63 *. nn +. (l1_l1 +. l0_r63) *. n +. l0_l1;
  }

let lemma_mul_x hi lo =
  let n = monomial 64 in
  let nn = monomial 128 in
  let l0_r63 = shift (lo %. n) (-63) in
  let l1_r63 = shift (lo /. n) (-63) in
  let l0_l1 = (shift (lo %. n) 1) %. n in
  let l1_l1 = (shift (lo /. n) 1) %. n in
  let h0_r63 = shift (hi %. n) (-63) in
  let h1_r63 = shift (hi /. n) (-63) in
  let h0_l1 = (shift (hi %. n) 1) %. n in
  let h1_l1 = (shift (hi /. n) 1) %. n in
  calc (==) {
    shift (hi *. nn +. lo) 1;
    == {lemma_shift_is_mul (hi *. nn +. lo) 1}
    (hi *. nn +. lo) *. monomial 1;
    == {lemma_mul_distribute_left (hi *. nn) lo (monomial 1)}
    hi *. nn *. monomial 1 +. lo *. monomial 1;
    == {
      lemma_mul_commute hi nn;
      lemma_mul_associate nn hi (monomial 1);
      lemma_mul_commute nn (hi *. monomial 1)
    }
    hi *. monomial 1 *. nn +. lo *. monomial 1;
    == {lemma_mul_128_x hi; lemma_mul_128_x lo}
    (h1_r63 *. nn +. (h1_l1 +. h0_r63) *. n +. h0_l1) *. nn +.
      (l1_r63 *. nn +. (l1_l1 +. l0_r63) *. n +. l0_l1);
    == {
      lemma_shift_is_div hi 64;
      lemma_shift_shift hi (-64) (-63);
      lemma_shift_degree hi (-127);
      lemma_degree_negative h1_r63
    }
    (zero *. nn +. (h1_l1 +. h0_r63) *. n +. h0_l1) *. nn +.
      (l1_r63 *. nn +. (l1_l1 +. l0_r63) *. n +. l0_l1);
    == {
      lemma_mul_commute zero nn;
      lemma_mul_zero nn;
      lemma_add_zero_left ((h1_l1 +. h0_r63) *. n)
    }
    ((h1_l1 +. h0_r63) *. n +. h0_l1) *. nn +.
      (l1_r63 *. nn +. (l1_l1 +. l0_r63) *. n +. l0_l1);
    == {lemma_add_associate (l1_r63 *. nn) ((l1_l1 +. l0_r63) *. n) l0_l1}
    ((h1_l1 +. h0_r63) *. n +. h0_l1) *. nn +.
      (l1_r63 *. nn +. ((l1_l1 +. l0_r63) *. n +. l0_l1));
    == {
      lemma_add_associate (((h1_l1 +. h0_r63) *. n +. h0_l1) *. nn) 
        (l1_r63 *. nn) ((l1_l1 +. l0_r63) *. n +. l0_l1)
    }
    (((h1_l1 +. h0_r63) *. n +. h0_l1) *. nn +. l1_r63 *. nn) +.
      ((l1_l1 +. l0_r63) *. n +. l0_l1);
    == {lemma_mul_distribute_left ((h1_l1 +. h0_r63) *. n +. h0_l1) l1_r63 nn}
    ((((h1_l1 +. h0_r63) *. n +. h0_l1) +. l1_r63) *. nn) +.
      ((l1_l1 +. l0_r63) *. n +. l0_l1);
    == {lemma_add_associate ((h1_l1 +. h0_r63) *. n) h0_l1 l1_r63}
    ((h1_l1 +. h0_r63) *. n +. (h0_l1 +. l1_r63)) *. nn +.
      ((l1_l1 +. l0_r63) *. n +. l0_l1);
    == {
      lemma_shift_is_mul (h1_l1 +. h0_r63) 64;
      lemma_shift_is_mul (l1_l1 +. l0_r63) 64
    }
    (shift (h1_l1 +. h0_r63) 64 +. (h0_l1 +. l1_r63)) *. nn +.
      (shift (l1_l1 +. l0_r63) 64 +. l0_l1);
  }

let lemma_reduce_helper a h =
  let n = monomial 64 in
  let y_10c = swap a 64 +. (mask a 64) *. h in
  calc (==) {
    swap a 64 +. (mask a 64) *. h;
    == {lemma_mask_is_mod a 64; lemma_shift_is_div a 64}
    (shift (a %. n) 64 +. a /. n) +. (a %. n) *. h;
    == {lemma_div_mod ((a %. n) *. h) n}
    (shift (a %. n) 64 +. a /. n) +.
      ((((a %. n) *. h) /. n) *. n +. ((a %. n) *. h) %. n);
    == {lemma_shift_is_mul (((a %. n) *. h) /. n) 64}
    (shift (a %. n) 64 +. a /. n) +.
      (shift (((a %. n) *. h) /. n) 64 +. ((a %. n) *. h) %. n);
    == {lemma_add_left_shift_double (a /. n) (a %. n) 
          (((a %. n) *. h) %. n) (((a %. n) *. h) /. n)}
    shift (a %. n +. ((a %. n) *. h) /. n) 64 +.
      (a /. n +. ((a %. n) *. h) %. n);
  };
  calc (==) {
    swap y_10c 64;
    == {lemma_mask_is_mod y_10c 64; lemma_shift_is_div y_10c 64}
    shift (y_10c %. n) 64 +. y_10c /. n;
    == {
      lemma_shift_is_mul (a %. n +. ((a %. n) *. h) /. n) 64;
      lemma_div_mod_unique y_10c n (a %. n +. ((a %. n) *. h) /. n)
          (a /. n +. ((a %. n) *. h) %. n)
    }
    shift (a /. n +. ((a %. n) *. h) %. n) 64 +.
      (a %. n +. ((a %. n) *. h) /. n);
  };
  calc (==) {
    mask y_10c 64 *. h;
    == {lemma_mask_is_mod y_10c 64}
    (y_10c %. n) *. h;
    == {
      lemma_shift_is_mul (a %. n +. ((a %. n) *. h) /. n) 64;
      lemma_div_mod_unique y_10c n (a %. n +. ((a %. n) *. h) /. n)
          (a /. n +. ((a %. n) *. h) %. n)
    }
    (a /. n +. ((a %. n) *. h) %. n) *. h;
    == {
      lemma_div_mod ((a /. n +. ((a %. n) *. h) %. n) *. h) n;
      lemma_shift_is_mul (((a /. n +. ((a %. n) *. h) %. n) *. h) /. n) 64
    }
    shift (((a /. n +. ((a %. n) *. h) %. n) *. h) /. n) 64 +.
        ((a /. n +. ((a %. n) *. h) %. n) *. h) %. n;
    == {
      lemma_mul_distribute_left (a /. n) (((a %. n) *. h) %. n) h;
      lemma_mod_distribute ((a /. n) *. h) ((((a %. n) *. h) %. n) *. h) n
    }
    shift (((a /. n +. ((a %. n) *. h) %. n) *. h) /. n) 64 +.
        (((a /. n) *. h) %. n +. ((((a %. n) *. h) %. n) *. h) %. n);
    == {
      lemma_mul_h_2_zero (a %. n) h;
      lemma_add_zero_right (((a /. n) *. h) %. n)
    }
    shift (((a /. n +. ((a %. n) *. h) %. n) *. h) /. n) 64 +.
        ((a /. n) *. h) %. n;
  };
  calc (==) {
    swap y_10c 64 +. mask y_10c 64 *. h;
    == {lemma_add_left_shift_double (a %. n +. ((a %. n) *. h) /. n) 
          (a /. n +. ((a %. n) *. h) %. n)
          (((a /. n) *. h) %. n)
          (((a /. n +. ((a %. n) *. h) %. n) *. h) /. n)}
    shift ((a /. n +. ((a %. n) *. h) %. n) +. 
      (((a /. n +. ((a %. n) *. h) %. n) *. h) /. n)) 64 +.
        ((a %. n +. ((a %. n) *. h) /. n) +. ((a /. n) *. h) %. n);
    == {lemma_add_associate (a %. n) (((a %. n) *. h) /. n)
          (((a /. n) *. h) %. n)}
    shift ((a /. n +. ((a %. n) *. h) %. n) +. 
      (((a /. n +. ((a %. n) *. h) %. n) *. h) /. n)) 64 +.
        (a %. n +. (((a %. n) *. h) /. n +. ((a /. n) *. h) %. n));
  }

open Vale.AES.GF128

let lemma_reduce_rev_helper a0 a1 h n =
  let c = reverse (shift h (-1)) (n - 1) in
  let y_10c = swap a0 64 +. (mask a0 64) *. c in
  reveal_defs ();
  lemma_mask_is_mod zero 64;
  lemma_add_zero_right a0;
  lemma_add_zero_right a1;
  lemma_add_commute (swap y_10c 64) a1;
  lemma_add_associate a1 (swap y_10c 64) (mask y_10c 64 *. c);
  lemma_add_commute a1 ((swap y_10c 64) +. (mask y_10c 64 *. c));
  lemma_reduce_rev a0 zero a1 h n;
  ()

val lemma_add_helper1 (ac bc_m ad_m z_ac z_bc_m z_ad_m:poly) :
  Lemma (ensures (
    (z_ac +. ac) +.
      (z_bc_m +. bc_m) +.
      (z_ad_m +. ad_m) ==
    (z_ac +. z_bc_m +. z_ad_m) +. (ac +. bc_m +. ad_m)))

let lemma_add_helper1 ac bc_m ad_m z_ac z_bc_m z_ad_m =
  calc (==) {
    (z_ac +. ac) +.
      (z_bc_m +. bc_m) +.
      (z_ad_m +. ad_m);
    == {
      lemma_add_associate (z_ac +. ac) (z_bc_m +. bc_m) (z_ad_m +. ad_m);
      lemma_add_associate (z_bc_m +. bc_m) (z_ad_m) (ad_m);
      lemma_add_commute (z_bc_m) (bc_m);
      lemma_add_associate (bc_m) (z_bc_m) (z_ad_m);
      lemma_add_associate (z_ac +. ac) (bc_m +. (z_bc_m +. z_ad_m)) (ad_m)
    }
    (z_ac +. ac) +.
      (bc_m +. (z_bc_m +. z_ad_m)) +.
      ad_m;
    == {
      lemma_add_commute (bc_m) (z_bc_m +. z_ad_m);
      lemma_add_associate (z_ac +. ac) (z_bc_m +. z_ad_m) (bc_m);
      lemma_add_commute z_ac ac;
      lemma_add_associate ac z_ac (z_bc_m +. z_ad_m);
      lemma_add_associate z_ac (z_bc_m) (z_ad_m)
    }
    (ac +. (z_ac +. z_bc_m +. z_ad_m)) +.
      bc_m +.
      ad_m;
    == {
      lemma_add_commute ac (z_ac +. z_bc_m +. z_ad_m);
      lemma_add_associate (z_ac +. z_bc_m +. z_ad_m) ac (bc_m);
      lemma_add_associate (z_ac +. z_bc_m +. z_ad_m) (ac +. bc_m) (ad_m)
    }
    (z_ac +. z_bc_m +. z_ad_m) +. (ac +. bc_m +. ad_m);
  }

val lemma_add_helper2 (a b c:poly) :
  Lemma (ensures (a +. b +. c == b +. c +. a))

let lemma_add_helper2 a b c =
  lemma_add_commute b c;
  lemma_add_associate c b a;
  lemma_add_commute c (b +. a);
  lemma_add_commute b a

val lemma_add_helper3 (a b c d:poly) :
  Lemma (ensures (a +. b +. (c +. d) == a +. c +. (b +. d)))

let lemma_add_helper3 a b c d =
  lemma_add_associate (a +. b) c d;
  lemma_add_commute a b;
  lemma_add_associate b a c;
  lemma_add_commute b (a +. c);
  lemma_add_associate (a +. c) b d

val lemma_shift_helper (z_a a:poly) :
  Lemma (ensures (shift (z_a +. a) 128 == shift z_a 128 +. shift a 128))

let lemma_shift_helper z_a a =
  lemma_shift_is_mul_right (z_a +. a) 128;
  lemma_mul_distribute_left z_a a (monomial 128);
  lemma_shift_is_mul_right z_a 128;
  lemma_shift_is_mul_right a 128

val lemma_add_div_dist (ac bc ad z_ac z_bc z_ad:poly) :
  Lemma (ensures (
    let m = monomial 64 in
    (z_ac +. ac) +.
      (z_bc +. bc) /. m +.
      (z_ad +. ad) /. m ==
    (z_ac +. z_bc /. m +. z_ad /. m) +. (ac +. bc /. m +. ad /. m)))

let lemma_add_div_dist ac bc ad z_ac z_bc z_ad =
  let m = monomial 64 in
  Vale.AES.GHash_BE.lemma_div_distribute z_bc bc m;
  Vale.AES.GHash_BE.lemma_div_distribute z_ad ad m;
  lemma_add_helper1 ac (bc /. m) (ad /. m) z_ac (z_bc /. m) (z_ad /. m)

val lemma_add_mod_mul_dist (bd bc ad z_bd z_bc z_ad:poly) :
  Lemma (ensures (
    let m = monomial 64 in
    ((z_bc +. bc) %. m) *. m +.
      ((z_ad +. ad) %. m) *. m +.
      (z_bd +. bd) ==
    ((z_bc %. m) *. m +. (z_ad %. m) *. m +. z_bd) +.
      ((bc  %. m) *. m +. (ad  %. m) *. m +. bd)))

let lemma_add_mod_mul_dist bd bc ad z_bd z_bc z_ad =
  let m = monomial 64 in
  let bc_m = (bc %. m) *. m in
  let ad_m = (ad %. m) *. m in
  let z_bc_m = (z_bc %. m) *. m in
  let z_ad_m = (z_ad %. m) *. m in
  lemma_mod_distribute z_bc bc m;
  lemma_mod_distribute z_ad ad m;
  lemma_mul_distribute_left (z_bc %. m) (bc %. m) m;
  lemma_mul_distribute_left (z_ad %. m) (ad %. m) m;
  lemma_add_helper1 bd bc_m ad_m z_bd z_bc_m z_ad_m;
  lemma_add_helper2 (z_bd +. bd) (((z_bc +. bc) %. m) *. m)
    (((z_ad +. ad) %. m) *. m);
  lemma_add_helper2 z_bd z_bc_m z_ad_m;
  lemma_add_helper2 bd bc_m ad_m

let lemma_gf128_mul_4 a0 b0 c0 d0 a1 b1 c1 d1 a2 b2 c2 d2 a3 b3 c3 d3 =
  let m = monomial 64 in
  (* first poly *)
  let ab0 = a0 *. m +. b0 in
  let cd0 = c0 *. m +. d0 in
  let ac0 = a0 *. c0 in
  let ad0 = a0 *. d0 in
  let bc0 = b0 *. c0 in
  let bd0 = b0 *. d0 in
  (* seond poly *)
  let ab1 = a1 *. m +. b1 in
  let cd1 = c1 *. m +. d1 in
  let ac1 = a1 *. c1 in
  let ad1 = a1 *. d1 in
  let bc1 = b1 *. c1 in
  let bd1 = b1 *. d1 in
  (* third poly *)
  let ab2 = a2 *. m +. b2 in
  let cd2 = c2 *. m +. d2 in
  let ac2 = a2 *. c2 in
  let ad2 = a2 *. d2 in
  let bc2 = b2 *. c2 in
  let bd2 = b2 *. d2 in
  (* fourth poly *)
  let ab3 = a3 *. m +. b3 in
  let cd3 = c3 *. m +. d3 in
  let ac3 = a3 *. c3 in
  let ad3 = a3 *. d3 in
  let bc3 = b3 *. c3 in
  let bd3 = b3 *. d3 in
  (* accums *)
  let z_ac3 = ac0 +. ac1 +. ac2 in
  let z_bc3 = bc0 +. bc1 +. bc2 in
  let z_ad3 = ad0 +. ad1 +. ad2 in
  let z_bd3 = bd0 +. bd1 +. bd2 in
  let z_ac2 = ac0 +. ac1 in
  let z_bc2 = bc0 +. bc1 in
  let z_ad2 = ad0 +. ad1 in
  let z_bd2 = bd0 +. bd1 in
  (* lemmas *)
  calc (==) {
    shift ((z_ac3 +. ac3) +.
      (z_bc3 +. bc3) /. m +.
      (z_ad3 +. ad3) /. m) 128 +.
    (((z_bc3 +. bc3) %. m) *. m +.
      ((z_ad3 +. ad3) %. m) *. m +.
      (z_bd3 +. bd3));
    == {
      lemma_add_div_dist ac3 bc3 ad3 z_ac3 z_bc3 z_ad3;
      lemma_add_mod_mul_dist bd3 bc3 ad3 z_bd3 z_bc3 z_ad3
    }
    shift ((z_ac3 +. z_bc3 /. m +. z_ad3 /. m) +.
      (ac3 +. bc3 /. m +. ad3 /. m)) 128 +.
    (((z_bc3 %. m) *. m +. (z_ad3 %. m) *. m +. z_bd3) +.
      ((bc3 %. m) *. m +. (ad3 %. m) *. m +. bd3));
    == {
      lemma_shift_helper (z_ac3 +. z_bc3 /. m +. z_ad3 /. m) 
        (ac3 +. bc3 /. m +. ad3 /. m);
      lemma_add_helper3
      (shift ((z_ac3 +. z_bc3 /. m +. z_ad3 /. m)) 128)
      (shift (ac3 +. bc3 /. m +. ad3 /. m) 128)
      ((z_bc3 %. m) *. m +. (z_ad3 %. m) *. m +. z_bd3)
      ((bc3 %. m) *. m +. (ad3 %. m) *. m +. bd3)
    }
    shift ((z_ac3 +. z_bc3 /. m +. z_ad3 /. m)) 128 +.
      ((z_bc3 %. m) *. m +. (z_ad3 %. m) *. m +. z_bd3) +.
    ((shift (ac3 +. bc3 /. m +. ad3 /. m) 128) +.
      ((bc3 %. m) *. m +. (ad3 %. m) *. m +. bd3));
    == {lemma_gf128_mul a3 b3 c3 d3 64}
    shift (((z_ac2 +. ac2) +. (z_bc2 +. bc2) /. m +. (z_ad2 +. ad2) /. m)) 128 +.
      (((z_bc2 +. bc2) %. m) *. m +. ((z_ad2 +. ad2) %. m) *. m +. (z_bd2 +. bd2)) +.
    (ab3 *. cd3);
    == {
      lemma_add_div_dist ac2 bc2 ad2 z_ac2 z_bc2 z_ad2;
      lemma_add_mod_mul_dist bd2 bc2 ad2 z_bd2 z_bc2 z_ad2
    }
    (shift ((z_ac2 +. z_bc2 /. m +. z_ad2 /. m) +.
      (ac2 +. bc2 /. m +. ad2 /. m)) 128 +.
    (((z_bc2 %. m) *. m +. (z_ad2 %. m) *. m +. z_bd2) +.
      ((bc2 %. m) *. m +. (ad2 %. m) *. m +. bd2))) +.
    (ab3 *. cd3);
    == {
      lemma_shift_helper (z_ac2 +. z_bc2 /. m +. z_ad2 /. m) 
        (ac2 +. bc2 /. m +. ad2 /. m);
      lemma_add_helper3
      (shift ((z_ac2 +. z_bc2 /. m +. z_ad2 /. m)) 128)
      (shift (ac2 +. bc2 /. m +. ad2 /. m) 128)
      ((z_bc2 %. m) *. m +. (z_ad2 %. m) *. m +. z_bd2)
      ((bc2 %. m) *. m +. (ad2 %. m) *. m +. bd2)
    }
    (shift ((z_ac2 +. z_bc2 /. m +. z_ad2 /. m)) 128 +.
        ((z_bc2 %. m) *. m +. (z_ad2 %. m) *. m +. z_bd2) +.
      ((shift (ac2 +. bc2 /. m +. ad2 /. m) 128) +.
          ((bc2 %. m) *. m +. (ad2 %. m) *. m +. bd2))) +.
    (ab3 *. cd3);
    == {lemma_gf128_mul a2 b2 c2 d2 64}
    (shift (((ac0 +. ac1) +. (bc0 +. bc1) /. m +. (ad0 +. ad1) /. m)) 128 +.
        (((bc0 +. bc1) %. m) *. m +. ((ad0 +. ad1) %. m) *. m +. (bd0 +. bd1)) +.
      (ab2 *. cd2)) +.
    (ab3 *. cd3);
    == {
      lemma_add_div_dist ac1 bc1 ad1 ac0 bc0 ad0;
      lemma_add_mod_mul_dist bd1 bc1 ad1 bd0 bc0 ad0
    }
    ((shift ((ac0 +. bc0 /. m +. ad0 /. m) +.
          (ac1 +. bc1 /. m +. ad1 /. m)) 128 +.
        (((bc0 %. m) *. m +. (ad0 %. m) *. m +. bd0) +.
          ((bc1 %. m) *. m +. (ad1 %. m) *. m +. bd1))) +.
      (ab2 *. cd2)) +.
    (ab3 *. cd3);
    == {
      lemma_shift_helper (ac0 +. bc0 /. m +. ad0 /. m) 
        (ac1 +. bc1 /. m +. ad1 /. m);
      lemma_add_helper3
      (shift ((ac0 +. bc0 /. m +. ad0 /. m)) 128)
      (shift (ac1 +. bc1 /. m +. ad1 /. m) 128)
      ((bc0 %. m) *. m +. (ad0 %. m) *. m +. bd0)
      ((bc1 %. m) *. m +. (ad1 %. m) *. m +. bd1)
    }
    ((shift ((ac0 +. bc0 /. m +. ad0 /. m)) 128 +.
          ((bc0 %. m) *. m +. (ad0 %. m) *. m +. bd0) +.
        ((shift (ac1 +. bc1 /. m +. ad1 /. m) 128) +.
          ((bc1 %. m) *. m +. (ad1 %. m) *. m +. bd1))) +.
      (ab2 *. cd2)) +.
    (ab3 *. cd3);
    == {
      lemma_gf128_mul a1 b1 c1 d1 64;
      lemma_gf128_mul a0 b0 c0 d0 64
    }
    (ab0 *. cd0) +. (ab1 *. cd1) +. (ab2 *. cd2) +. (ab3 *. cd3);
  }

let lemma_add_helper_m a b c d p =
  lemma_add_associate p a b;
  lemma_add_associate p (a +. b) c;
  lemma_add_associate p (a +. b +. c) d;
  lemma_add_commute p (a +. b +. c +. d)

let lemma_mul_reduce_helper1 x1 x2 x3 x4 y1 y2 y3 y4 =
  let x1_r = reverse x1 127 in
  let x2_r = reverse x2 127 in
  let x3_r = reverse x3 127 in
  let x4_r = reverse x4 127 in
  let y1_r = reverse y1 127 in
  let y2_r = reverse y2 127 in
  let y3_r = reverse y3 127 in
  let y4_r = reverse y4 127 in
  calc (==) {
    shift ((x1 *. y1) +. (x2 *. y2) +. (x3 *. y3) +. (x4 *. y4)) 1;
    == {lemma_shift_is_mul ((x1 *. y1) +.
          (x2 *. y2) +. (x3 *. y3) +. (x4 *. y4)) 1}
    ((x1 *. y1) +. (x2 *. y2) +. (x3 *. y3) +. (x4 *. y4)) *. monomial 1;
    == {lemma_mul_distribute_left ((x1 *. y1) +. (x2 *. y2) +. (x3 *. y3))
          (x4 *. y4) (monomial 1)}
    ((x1 *. y1) +. (x2 *. y2) +. (x3 *. y3)) *. monomial 1 +.
      (x4 *. y4) *. monomial 1;
    == {lemma_mul_distribute_left ((x1 *. y1) +. (x2 *. y2))
          (x3 *. y3) (monomial 1)}
    ((x1 *. y1) +. (x2 *. y2)) *. monomial 1 +. (x3 *. y3) *. monomial 1 +.
      (x4 *. y4) *. monomial 1;
    == {lemma_mul_distribute_left (x1 *. y1) (x2 *. y2) (monomial 1)}
    (x1 *. y1) *. monomial 1 +. (x2 *. y2) *. monomial 1 +.
      (x3 *. y3) *. monomial 1 +. (x4 *. y4) *. monomial 1;
    == {lemma_shift_is_mul (x1 *. y1) 1;
        lemma_shift_is_mul (x2 *. y2) 1;
        lemma_shift_is_mul (x3 *. y3) 1;
        lemma_shift_is_mul (x4 *. y4) 1}
    shift (x1 *. y1) 1 +. shift (x2 *. y2) 1 +.
      shift (x3 *. y3) 1 +. shift (x4 *. y4) 1;
    == {lemma_mul_reverse_shift_1 x1_r y1_r 127;
        lemma_mul_reverse_shift_1 x2_r y2_r 127;
        lemma_mul_reverse_shift_1 x3_r y3_r 127;
        lemma_mul_reverse_shift_1 x4_r y4_r 127}
    reverse (x1_r *. y1_r) 255 +. reverse (x2_r *. y2_r) 255 +.
      reverse (x3_r *. y3_r) 255 +. reverse (x4_r *. y4_r) 255;
    == {lemma_add_reverse (x1_r *. y1_r) (x2_r *. y2_r) 255}
    reverse ((x1_r *. y1_r) +. (x2_r *. y2_r)) 255 +.
      reverse (x3_r *. y3_r) 255 +. reverse (x4_r *. y4_r) 255;
    == {lemma_add_reverse ((x1_r *. y1_r) +. (x2_r *. y2_r)) (x3_r *. y3_r) 255}
    reverse ((x1_r *. y1_r) +. (x2_r *. y2_r) +. (x3_r *. y3_r)) 255 +.
      reverse (x4_r *. y4_r) 255;
    == {lemma_add_reverse ((x1_r *. y1_r) +. (x2_r *. y2_r) +. (x3_r *. y3_r))
          (x4_r *. y4_r) 255}
    reverse ((x1_r *. y1_r) +. (x2_r *. y2_r) +. (x3_r *. y3_r) +. (x4_r *. y4_r)) 255;
  }

let lemma_mul_reduce_helper2 z1 z2 z3 z4 g =
  calc (==) {
    (z1 +. z2 +. z3 +. z4) %. g;
    == {lemma_mod_distribute (z1 +. z2 +. z3) z4 g}
    (z1 +. z2 +. z3) %. g +. z4 %. g;
    == {lemma_mod_distribute (z1 +. z2) z3 g}
    (z1 +. z2) %. g +. z3 %. g +. z4 %. g;
    == {lemma_mod_distribute z1 z2 g}
    z1 %. g +. z2 %. g +. z3 %. g +. z4 %. g;
  };
  calc (==) {
    reverse (z1 %. g +. z2 %. g +. z3 %. g +. z4 %. g) 127;
    == {lemma_add_reverse (z1 %. g +. z2 %. g +. z3 %. g) (z4 %. g) 127}
    reverse (z1 %. g +. z2 %. g +. z3 %. g) 127 +. reverse (z4 %. g) 127;
    == {lemma_add_reverse (z1 %. g +. z2 %. g) (z3 %. g) 127}
    reverse (z1 %. g +. z2 %. g) 127 +. reverse (z3 %. g) 127 +. reverse (z4 %. g) 127;
    == {lemma_add_reverse (z1 %. g) (z2 %. g) 127}
    reverse (z1 %. g) 127 +. reverse (z2 %. g) 127 +. reverse (z3 %. g) 127 +. reverse (z4 %. g) 127;
  }
