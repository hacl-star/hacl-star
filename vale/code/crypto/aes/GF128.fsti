module GF128
open Words_s
open Words.Four_s
open Types_s
open Arch.Types
open GF128_s
open Math.Poly2_s
open Math.Poly2.Bits_s
open Math.Poly2
open Math.Poly2.Lemmas
open FStar.Seq
open FStar.Mul

val lemma_of_double32_degree (d:double32) : Lemma
  (degree (of_double32 d) < 64)
  [SMTPat (degree (of_double32 d))]

val lemma_of_quad32_degree (q:quad32) : Lemma
  (degree (of_quad32 q) < 128)
  [SMTPat (degree (of_quad32 q))]

val lemma_to_of_quad32 (q:quad32) : Lemma (to_quad32 (of_quad32 q) == q)

val lemma_of_to_quad32 (a:poly) : Lemma
  (requires degree a < 128)
  (ensures of_quad32 (to_quad32 a) == a)

let quad32_shift_left_1 (q:quad32) : quad32 =
  let l = four_map (fun (i:nat32) -> ishl i 1) q in
  let r = four_map (fun (i:nat32) -> ishr i 31) q in
  let Mkfour r0 r1 r2 r3 = r in
  quad32_xor l (Mkfour 0 r0 r1 r2)

let quad32_shift_2_left_1 (qa qb:quad32) : tuple2 quad32 quad32 =
  let la = four_map (fun (i:nat32) -> ishl i 1) qa in
  let lb = four_map (fun (i:nat32) -> ishl i 1) qb in
  let ra = four_map (fun (i:nat32) -> ishr i 31) qa in
  let rb = four_map (fun (i:nat32) -> ishr i 31) qb in
  let Mkfour ra0 ra1 ra2 ra3 = ra in
  let Mkfour rb0 rb1 rb2 rb3 = rb in
  let qa' = quad32_xor la (Mkfour 0 ra0 ra1 ra2) in
  let qb' = quad32_xor lb (quad32_xor (Mkfour ra3 0 0 0) (Mkfour 0 rb0 rb1 rb2)) in
  (qa', qb')

val lemma_shift_left_1 (a:poly) : Lemma
  (requires degree a < 127)
  (ensures to_quad32 (shift a 1) == quad32_shift_left_1 (to_quad32 a))

val lemma_shift_2_left_1 (lo hi:poly) : Lemma
  (requires degree hi < 127 /\ degree lo < 128)
  (ensures (
    let n = monomial 128 in
    let a = hi *. n +. lo in
    let a' = shift a 1 in
    let (lo', hi') = quad32_shift_2_left_1 (to_quad32 lo) (to_quad32 hi) in
    lo' == to_quad32 (a' %. n) /\
    hi' == to_quad32 (a' /. n)
  ))

val lemma_reverse_reverse (a:poly) (n:nat) : Lemma
  (requires degree a <= n)
  (ensures reverse (reverse a n) n == a)
  [SMTPat (reverse (reverse a n) n)]

val lemma_gf128_degree (_:unit) : Lemma
  (ensures
    degree gf128_modulus_low_terms == 7 /\
    degree (monomial 128) == 128 /\
    degree gf128_modulus == 128
  )

val lemma_gf128_constant_rev (q:quad32) : Lemma
  (ensures
    to_quad32 (reverse gf128_modulus_low_terms 127) == Mkfour 0 0 0 0xe1000000 /\
    quad32_xor q q == Mkfour 0 0 0 0
  )

val lemma_quad32_double_hi_rev (a:poly) : Lemma
  (requires degree a <= 127 /\ degree (reverse a 127) <= 63)
  (ensures of_double32 (quad32_double_hi (to_quad32 a)) == reverse (reverse a 127) 63)

// Compute 128-bit multiply in terms of 64-bit multiplies
val lemma_gf128_mul (a b c d:poly) (n:nat) : Lemma
  (ensures (
    let m = monomial n in
    let ab = a *. m +. b in
    let cd = c *. m +. d in
    let ac = a *. c in
    let ad = a *. d in
    let bc = b *. c in
    let bd = b *. d in
    ab *. cd ==
      shift (ac +. bc /. m +. ad /. m) (n + n) +.
      ((bc %. m) *. m +. (ad %. m) *. m +. bd)
  ))

// Compute (a * b) % g, where g = n + h and %. n is easy to compute (e.g. n = x^128)
val lemma_gf128_reduce (a b g n h:poly) : Lemma
  (requires
    degree h >= 0 /\
    degree n > 2 * degree h /\
    degree g == degree n /\
    degree a <= degree n /\
    degree b <= degree n /\
    g == n +. h
  )
  (ensures (
    let d = (a *. b) /. n in
    let dh = d *. h in
    degree ((dh /. n) *. h) <= 2 * degree h /\
    (a *. b) %. g == (dh /. n) *. h +. dh %. n +. (a *. b) %. n
  ))

val lemma_gf128_reduce_rev (a b h:poly) (n:pos) : Lemma
  (requires
    degree h >= 0 /\
    n > 2 * degree h /\
    degree (monomial n +. h) == n /\
    degree a < n /\
    degree b < n
  )
  (ensures (
    let m = monomial n in
    let g = m +. h in
    let r x = reverse x (n - 1) in
    let rr x = reverse x (2 * n - 1) in
    let rab = rr (a *. b) in
    let rd = rab %. m in
    let rdh = rr (r rd *. h) in
    let rdhL = rdh %. m in
    let rdhLh = r (r rdhL *. h) in
    degree (r rdhL) <= 2 * degree h /\
    degree (r rdhLh) <= 2 * degree h /\
    r ((a *. b) %. g) == rdhLh +. rdh /. m +. rab /. m
  ))
