module Vale.AES.GF128
open FStar.Seq
open FStar.Mul
open Vale.Def.Words_s
open Vale.Def.Words.Four_s
open Vale.Def.Types_s
open Vale.Arch.Types
open Vale.AES.GF128_s
open Vale.Math.Poly2_s
open Vale.Math.Poly2.Bits_s
open Vale.Math.Poly2
open Vale.Math.Poly2.Lemmas

let quad32_shift_left_1 (q:quad32) : quad32 =
  let l = four_map (fun (i:nat32) -> ishl i 1) q in
  let r = four_map (fun (i:nat32) -> ishr i 31) q in
  let Mkfour r0 r1 r2 r3 = r in
  quad32_xor l (Mkfour 0 r0 r1 r2)

let quad32_shift_2_left_1 (qa qb:quad32) : quad32 & quad32 =
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
  (requires degree a < 128)
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

// TODO: move this to Poly library
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

val lemma_reduce_rev (a0 a1 a2 h:poly) (n:pos) : Lemma
  (requires
    n == 64 /\ // verification times out unless n is known
    degree a0 < n + n /\
    degree a1 < n + n /\
    degree a2 < n + n /\
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
    let y_10 = a0 +. shift (mask a1 64) 64 in
    let y_0 = mask y_10 64 in
    let y_10c = swap y_10 64 +. y_0 *. c in
    let a = a0 +. shift a1 64 +. shift a2 128 in
    let x = reverse a (nn + nn - 1) in
    reverse (x %. g) (nn - 1) == swap y_10c 64 +. (a2 +. shift a1 (-64)) +. mask y_10c 64 *. c
  ))

// of_fun 8 (fun (i:nat) -> i = 0 || i = 1 || i = 6)
let gf128_low_shift : poly = shift gf128_modulus_low_terms (-1)

// of_fun 8 (fun (i:nat) -> i = 127 || i = 126 || i = 121)
let gf128_rev_shift : poly = reverse gf128_low_shift 127

val lemma_gf128_low_shift (_:unit) : Lemma
  (shift (of_quad32 (Mkfour 0 0 0 0xc2000000)) (-64) == reverse gf128_low_shift 63)

val lemma_gf128_high_bit (_:unit) : Lemma
  (of_quad32 (Mkfour 0 0 0 0x80000000) == monomial 127)

val lemma_gf128_low_shift_1 (_:unit) : Lemma
  (of_quad32 (Mkfour 1 0 0 0xc2000000) == reverse (shift (monomial 128 +. gf128_modulus_low_terms) (-1)) 127)

let gf128_mul_rev (a b:poly) : poly =
  reverse (gf128_mul (reverse a 127) (reverse b 127)) 127

let ( *~ ) = gf128_mul_rev

val lemma_gf128_mul_rev_commute (a b:poly) : Lemma (a *~ b == b *~ a)

val lemma_gf128_mul_rev_associate (a b c:poly) : Lemma
  (a *~ (b *~ c) == (a *~ b) *~ c)

val lemma_gf128_mul_rev_distribute_left (a b c:poly) : Lemma
  ((a +. b) *~ c == a *~ c +. b *~ c)

val lemma_gf128_mul_rev_distribute_right (a b c:poly) : Lemma
  (a *~ (b +. c) == a *~ b +. a *~ c)

// TODO: change definition of reverse from (reverse a 127) to (reverse 128 a)
let mod_rev (n:pos) (a b:poly) : poly =
  reverse (reverse a (n + n - 1) %. b) (n - 1)

val lemma_add_mod_rev (n:pos) (a1 a2 b:poly) : Lemma
  (requires degree b >= 0)
  (ensures mod_rev n (a1 +. a2) b == mod_rev n a1 b +. mod_rev n a2 b)

let shift_key_1 (n:pos) (f h:poly) : poly =
  let g = monomial n +. f in
  let h1 = shift h 1 in
  let offset = reverse (shift g (-1)) (n - 1) in
  mask h1 n +. (if h1.[n] then offset else zero)

val lemma_shift_key_1 (n:pos) (f h:poly) : Lemma
  (requires f.[0] /\ degree f < n /\ degree h < n)
  (ensures (
    let g = monomial n +. f in
    shift (reverse (shift_key_1 n f h) (n - 1)) 1 %. g == reverse h (n - 1) %. g
  ))

val lemma_test_high_bit (a:poly) : Lemma
  (requires degree a < 128)
  (ensures a.[127] == ((to_quad32 (poly_and a (monomial 127))).hi3 = (to_quad32 (monomial 127)).hi3))

val lemma_Mul128 (a b:poly) : Lemma
  (requires degree a < 128 /\ degree b < 128)
  (ensures (
    let aL = mask a 64 in
    let bL = mask b 64 in
    let aH = shift a (-64) in
    let bH = shift b (-64) in
    a *. b == aL *. bL +. shift (aL *. bH +. aH *. bL) 64 +. shift (aH *. bH) 128
  ))

val lemma_Mul128_accum (z0 z1 z2 a b:poly) : Lemma
  (requires degree a < 128 /\ degree b < 128)
  (ensures (
    let z = z0 +. shift z1 64 +. shift z2 128 in
    let aL = mask a 64 in
    let bL = mask b 64 in
    let aH = shift a (-64) in
    let bH = shift b (-64) in
    z +. a *. b == (z0 +. aL *. bL) +. shift (z1 +. aL *. bH +. aH *. bL) 64 +. shift (z2 +. aH *. bH) 128
  ))
