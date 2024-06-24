module Hacl.Spec.GF128.PolyLemmas_helpers

open FStar.Mul

open Vale.Math.Poly2_s
open Vale.Math.Poly2
open Vale.Math.Poly2.Bits_s
open Vale.Math.Poly2.Lemmas
open Vale.AES.GF128_s

// of_fun 8 (fun (i:nat) -> i = 0 || i = 1 || i = 2 || i = 7)
let gf128_low : poly = gf128_modulus_low_terms

// of_fun 8 (fun (i:nat) -> i = 0 || i = 1 || i = 6)
let gf128_low_shift : poly = shift gf128_modulus_low_terms (-1)

val lemma_mul_h_shift_right (a h:poly) : Lemma
  (requires degree a <= 63 /\ h == reverse gf128_low_shift 63)
  (ensures a *. h == shift a 63 +. shift a 62 +. shift a 57)

val lemma_mul_h_shift_right_mod (a h:poly) : Lemma
  (requires degree a <= 63 /\ h == reverse gf128_low_shift 63)
  (ensures (a *. h) %. monomial 64 ==
    shift a 63 %. monomial 64 +. shift a 62 %. monomial 64 +. shift a 57 %. monomial 64)

val lemma_mul_h_shift_left (a h:poly) : Lemma
  (requires degree a <= 63 /\ h == reverse gf128_low_shift 63)
  (ensures (a *. h) /. monomial 64 == shift a (-1) +. shift a (-2) +. shift a (-7))

val lemma_mul_h (a h:poly) : Lemma
  (requires degree a <= 63 /\ h == reverse gf128_low_shift 63)
  (ensures a *. h == (shift a (-1) +. shift a (-2) +. shift a (-7)) *. monomial 64 +.
    (shift a 63 +. shift a 62 +. shift a 57) %. monomial 64)

val lemma_mul_h_2_zero (a h:poly) : Lemma
  (requires degree a <= 63 /\ h == reverse gf128_low_shift 63)
  (ensures (((a *. h) %. monomial 64) *. h) %. monomial 64 == zero)

val lemma_shift_left_cancel (a a0 a1:poly) : Lemma
  (requires degree a <= 127 /\ degree a0 <= 63 /\
    degree a1 <= 63 /\ a == (shift a1 64) +. a0)
  (ensures shift (a %. monomial 64) 64 == shift a0 64)

val lemma_shift_right_cancel (a a0 a1:poly) : Lemma
  (requires degree a <= 127 /\ degree a0 <= 63 /\
    degree a1 <= 63 /\ a == (shift a1 64) +. a0)
  (ensures shift a (-64) == a1)

val lemma_add_left_shift (a0 a1 b:poly) : Lemma
  (requires degree a0 <= 63 /\ degree a1 <= 63 /\ degree b <= 63)
  (ensures (shift a1 64) +. a0 +. (shift b 64) == (shift (a1 +. b) 64) +. a0)

val lemma_add_left_shift_double (a0 a1 b0 b1:poly) : Lemma
  (requires degree a0 <= 63 /\ degree a1 <= 63 /\
    degree b0 <= 63 /\ degree b1 <= 63)
  (ensures (shift a1 64) +. a0 +. (shift b1 64 +. b0) ==
    (shift (a1 +. b1) 64) +. (a0 +. b0))

val lemma_mul_x (hi lo:poly) : Lemma
  (requires degree hi <= 126 /\ degree lo <= 127)
  (ensures (
    let n = monomial 64 in
    let nn = monomial 128 in
    let l0_r63 = shift (lo %. n) (-63) in
    let l1_r63 = shift (lo /. n) (-63) in
    let l0_l1 = (shift (lo %. n) 1) %. n in
    let l1_l1 = (shift (lo /. n) 1) %. n in
    let h0_r63 = shift (hi %. n) (-63) in
    let h0_l1 = (shift (hi %. n) 1) %. n in
    let h1_l1 = (shift (hi /. n) 1) %. n in
    shift (hi *. nn +. lo) 1 == 
      (shift (h1_l1 +. h0_r63) 64 +. (h0_l1 +. l1_r63)) *. nn +.
        (shift (l1_l1 +. l0_r63) 64 +. l0_l1)
  ))

val lemma_reduce_helper (a h:poly) : Lemma
  (requires degree a <= 127 /\ h == reverse gf128_low_shift 63)
  (ensures (
    let n = monomial 64 in
    let y_10c = swap a 64 +. (mask a 64) *. h in
    swap y_10c 64 +. mask y_10c 64 *. h == 
      (shift ((a /. n +. ((a %. n) *. h) %. n) +. 
        (((a /. n +. ((a %. n) *. h) %. n) *. h) /. n)) 64 +.
          (a %. n +. (((a %. n) *. h) /. n +. ((a /. n) *. h) %. n)))
  ))

val lemma_reduce_rev_helper (a0 a1 h:poly) (n:pos) : Lemma
  (requires
    n == 64 /\
    degree a0 < n + n /\
    degree a1 < n + n /\
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
    let y_10c = swap a0 64 +. (mask a0 64) *. c in
    let a = a0 +. shift a1 128 in
    let x = reverse a (nn + nn - 1) in
    reverse (x %. g) (nn - 1) == swap y_10c 64 +. mask y_10c 64 *. c +. a1
  ))

val lemma_gf128_mul_4 (a0 b0 c0 d0 a1 b1 c1 d1 a2 b2 c2 d2 a3 b3 c3 d3:poly) :
  Lemma (ensures (
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
    (ab0 *. cd0) +. (ab1 *. cd1) +. (ab2 *. cd2) +. (ab3 *. cd3) ==
      shift ((ac0 +. ac1 +. ac2 +. ac3) +.
        (bc0 +. bc1 +. bc2 +. bc3) /. m +.
        (ad0 +. ad1 +. ad2 +. ad3) /. m) 128 +.
      (((bc0 +. bc1 +. bc2 +. bc3) %. m) *. m +.
        ((ad0 +. ad1 +. ad2 +. ad3) %. m) *. m +.
        (bd0 +. bd1 +. bd2 +. bd3))
  ))

val lemma_add_helper_m (a b c d p:poly) :
  Lemma (ensures (p +. a +. b +. c +. d  == (a +. b +. c +. d) +. p))

val lemma_mul_reduce_helper1 (x1 x2 x3 x4 y1 y2 y3 y4:poly) : Lemma 
    (requires degree x1 < 128 /\ degree x2 < 128 /\ degree x3 < 128 /\
      degree x4 < 128 /\ degree y1 < 128 /\ degree y2 < 128 /\
      degree y3 < 128 /\ degree y4 < 128)
    (ensures reverse (shift ((x1 *. y1) +.
      (x2 *. y2) +. (x3 *. y3) +. (x4 *. y4)) 1) 255 ==
      ((reverse x1 127) *. (reverse y1 127)) +.
      ((reverse x2 127) *. (reverse y2 127)) +.
      ((reverse x3 127) *. (reverse y3 127)) +.
      ((reverse x4 127) *. (reverse y4 127)))

val lemma_mul_reduce_helper2 (z1 z2 z3 z4 g:poly) : Lemma
    (requires degree g == 128)
    (ensures reverse ((z1 +. z2 +. z3 +. z4) %. g) 127 ==
      reverse (z1 %. g) 127 +. reverse (z2 %. g) 127 +.
      reverse (z3 %. g) 127 +. reverse (z4 %. g) 127)
