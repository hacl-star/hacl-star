module Vale.AES.GHash
open FStar.Mul
open Vale.Math.Poly2.Lemmas
open Vale.Math.Poly2.Words

friend Vale.AES.OptPublic

#reset-options "--use_two_phase_tc true"

let shift_gf128_key_1 (h:poly) : poly =
  shift_key_1 128 gf128_modulus_low_terms h

let rec g_power (a:poly) (n:nat) : poly =
  if n = 0 then zero else // arbitrary value for n = 0
  if n = 1 then a else
  a *~ g_power a (n - 1)

let lemma_g_power_1 a = ()
let lemma_g_power_n a n = ()

let gf128_power h n = shift_gf128_key_1 (g_power h n)
let lemma_gf128_power h n = ()

let rec ghash_poly_unroll (h:poly) (prev:poly) (data:int -> poly128) (k:int) (m n:nat) : poly =
  let d = data (k + m) in
  let p = g_power h (n + 1) in
  if m = 0 then (prev +. d) *~ p else
  ghash_poly_unroll h prev data k (m - 1) (n + 1) +. d *~ p

let lemma_hkeys_reqs_pub_priv (hkeys:seq quad32) (h_BE:quad32) : Lemma
  (hkeys_reqs_pub hkeys h_BE <==> hkeys_reqs_priv hkeys h_BE)
  =
  ()

let rec lemma_ghash_unroll_back_forward_rec (h:poly) (prev:poly) (data:int -> poly128) (k:int) (n m:nat) : Lemma
  (requires m < n)
  (ensures ghash_unroll h prev data k n 0 ==
    ghash_unroll h prev data k (n - 1 - m) (m + 1) +. ghash_unroll_back h prev data k (n + 1) m)
  =
  lemma_add_all ();
  if m > 0 then lemma_ghash_unroll_back_forward_rec h prev data k n (m - 1)

let lemma_ghash_unroll_back_forward (h:poly) (prev:poly) (data:int -> poly128) (k:int) (n:nat) : Lemma
  (ghash_unroll h prev data k n 0 == ghash_unroll_back h prev data k (n + 1) n)
  =
  lemma_add_all ();
  if n > 0 then lemma_ghash_unroll_back_forward_rec h prev data k n (n - 1)

let lemma_gf128_mul_rev_mod_rev (a h:poly) : Lemma
  (requires degree a < 128 /\ degree h < 128)
  (ensures gf128_mul_rev a h == mod_rev 128 (a *. shift_gf128_key_1 h) gf128_modulus)
  =
  let h1 = shift_gf128_key_1 h in
  let rev x = reverse x 127 in
  let g = gf128_modulus in
  lemma_gf128_degree ();
  calc (==) {
    // gf128_mul_rev a h
    rev ((rev a *. rev h) %. g);
    == {lemma_mod_mul_mod_right (rev a) (rev h) g}
    rev ((rev a *. (rev h %. g)) %. g);
    == {lemma_shift_key_1 128 gf128_modulus_low_terms h}
    rev ((rev a *. (shift (rev h1) 1 %. g)) %. g);
    == {lemma_mod_mul_mod_right (rev a) (shift (rev h1) 1) g}
    rev ((rev a *. (shift (rev h1) 1)) %. g);
    == {lemma_shift_is_mul (rev h1) 1}
    rev ((rev a *. (rev h1 *. monomial 1)) %. g);
    == {lemma_mul_all ()}
    rev (((rev a *. rev h1) *. monomial 1) %. g);
    == {lemma_shift_is_mul (rev a *. rev h1) 1}
    rev (shift (rev a *. rev h1) 1 %. g);
    == {lemma_mul_reverse_shift_1 a h1 127}
    rev (reverse (a *. h1) 255 %. g);
  }

let rec lemma_ghash_poly_degree h init data j k =
  if k > j then lemma_ghash_poly_degree h init data j (k - 1)

let rec lemma_ghash_poly_unroll_n (h:poly) (prev:poly) (data:int -> poly128) (k:int) (m n:nat) : Lemma
  (ghash_poly_unroll h prev data k m (n + 1) == ghash_poly_unroll h prev data k m n *~ h)
  =
  let d = data (k + m) in
  let p0 = g_power h (n + 1) in
  let p1 = g_power h (n + 2) in
  if m = 0 then
    calc (==) {
      ghash_poly_unroll h prev data k m (n + 1);
      == {}
      (prev +. d) *~ p1;
      == {}
      (prev +. d) *~ (h *~ p0);
      == {lemma_gf128_mul_rev_commute p0 h}
      (prev +. d) *~ (p0 *~ h);
      == {lemma_gf128_mul_rev_associate (prev +. d) p0 h}
      ((prev +. d) *~ p0) *~ h;
      == {}
      ghash_poly_unroll h prev data k m n *~ h;
    }
  else
    let ghash0 = ghash_poly_unroll h prev data k (m - 1) (n + 1) in
    let ghash1 = ghash_poly_unroll h prev data k (m - 1) (n + 2) in
    calc (==) {
      ghash_poly_unroll h prev data k m (n + 1);
      == {}
      ghash1 +. d *~ p1;
      == {lemma_ghash_poly_unroll_n h prev data k (m - 1) (n + 1)}
      ghash0 *~ h +. d *~ p1;
      == {}
      ghash0 *~ h +. d *~ (h *~ p0);
      == {lemma_gf128_mul_rev_commute p0 h}
      ghash0 *~ h +. d *~ (p0 *~ h);
      == {lemma_gf128_mul_rev_associate d p0 h}
      ghash0 *~ h +. (d *~ p0) *~ h;
      == {lemma_gf128_mul_rev_distribute_left ghash0 (d *~ p0) h}
      (ghash0 +. d *~ p0) *~ h;
      == {}
      ghash_poly_unroll h prev data k m n *~ h;
    }

let rec lemma_ghash_poly_unroll (h0:poly) (prev:poly) (data:int -> poly128) (k:int) (m:nat) : Lemma
  (requires degree h0 < 128 /\ degree prev < 128)
  (ensures ghash_poly_unroll h0 prev data k m 0 == ghash_poly h0 prev data k (k + m + 1))
  =
  let d = data (k + m) in
  let p1 = g_power h0 1 in
  let ghash0 = ghash_poly h0 prev data k (k + m) in
  if m = 0 then
    calc (==) {
      ghash_poly_unroll h0 prev data k m 0;
      == {}
      (prev +. d) *~ p1;
      == {}
      (ghash0 +. d) *~ h0;
      == {}
      ghash_poly h0 prev data k (k + m + 1);
    }
  else
    let unroll0 = ghash_poly_unroll h0 prev data k (m - 1) 0 in
    let unroll1 = ghash_poly_unroll h0 prev data k (m - 1) 1 in
    calc (==) {
      ghash_poly_unroll h0 prev data k m 0;
      == {}
      unroll1 +. d *~ p1;
      == {
        calc (==) {
          unroll1;
          == {lemma_ghash_poly_unroll_n h0 prev data k (m - 1) 0}
          unroll0 *~ h0;
          == {lemma_ghash_poly_unroll h0 prev data k (m - 1)}
          ghash0 *~ h0;
        }
      }
      ghash0 *~ h0 +. d *~ h0;
      == {lemma_gf128_mul_rev_distribute_left ghash0 d h0}
      (ghash0 +. d) *~ h0;
      == {}
      ghash_poly h0 prev data k (k + m + 1);
    }

let rec lemma_ghash_unroll_poly_unroll (h:poly) (prev:poly) (data:int -> poly128) (k:int) (m n:nat) : Lemma
  (requires degree h < 128 /\ degree prev < 128)
  (ensures
    mod_rev 128 (ghash_unroll h prev data k m n) gf128_modulus ==
    ghash_poly_unroll h prev data k m n
  )
  =
  let g = gf128_modulus in
  let d = data (k + m) in
  let p = g_power h (n + 1) in
  let sp = shift_gf128_key_1 p in
  lemma_gf128_degree ();
  if m = 0 then
    calc (==) {
      mod_rev 128 (ghash_unroll h prev data k m n) g;
      == {}
      mod_rev 128 ((prev +. d) *. sp) g;
      == {lemma_gf128_mul_rev_mod_rev (prev +. d) p}
      (prev +. d) *~ p;
      == {}
      ghash_poly_unroll h prev data k m n;
    }
  else
    let unroll1 = ghash_unroll h prev data k (m - 1) (n + 1) in
    let ghash0 = ghash_poly_unroll h prev data k (m - 1) (n + 1) in
    calc (==) {
      mod_rev 128 (ghash_unroll h prev data k m n) g;
      == {}
      mod_rev 128 (unroll1 +. d *. sp) g;
      == {lemma_add_mod_rev 128 unroll1 (d *. sp) g}
      mod_rev 128 unroll1 g +. mod_rev 128 (d *. sp) g;
      == {lemma_ghash_unroll_poly_unroll h prev data k (m - 1) (n + 1)}
      ghash0 +. mod_rev 128 (d *. sp) g;
      == {lemma_gf128_mul_rev_mod_rev d p}
      ghash0 +. d *~ p;
      == {}
      ghash_poly_unroll h prev data k m n;
    }

let lemma_ghash_poly_of_unroll h prev data k m =
  lemma_ghash_poly_unroll h prev data k m;
  lemma_ghash_unroll_poly_unroll h prev data k m 0;
  ()

// TODO:
// The spec for ghash_LE_def should be rewritten in a more endian-consistent style.
// Right now, it performs the gf128_mul on BE (forward) values but performs the quad32_xor
// on LE (backwards) values.  Xor is endianness-neutral, so it's still correct, but
// it forces us to either insert extra byte reversals into the implementation (see the two
// Pshufb operations in ReduceMul128_LE) or to prove this otherwise-unnecessary lemma:
#reset-options "--z3rlimit 20"
let lemma_reverse_bytes_quad32_xor (a b:quad32) : Lemma
  (reverse_bytes_quad32 (quad32_xor a b) == quad32_xor (reverse_bytes_quad32 a) (reverse_bytes_quad32 b))
  =
  let open Vale.Def.Words.Four_s in
  let open FStar.UInt in
  let open FStar.BV in
  let open Vale.Math.Bits in
  let (!!) = reverse_bytes_quad32 in
  let r32 = reverse_bytes_nat32 in
  let mk4 (x0 x1 x2 x3:nat8) : nat32 = four_to_nat 8 (Mkfour x0 x1 x2 x3) in
  let mk4n (x0 x1 x2 x3:nat8) : nat32 = x0 + x1 * 0x100 + x2 * 0x10000 + x3 * 0x1000000 in
  let mk4m (x0 x1 x2 x3:nat8) : nat32 = add_hide #32 x0 (add_hide #32 (mul_hide #32 x1 0x100) (add_hide #32 (mul_hide #32 x2 0x10000) (mul_hide #32 x3 0x1000000))) in
  let mk4b (x0 x1 x2 x3:bv_t 32) : bv_t 32 = b_add x0 (b_add (b_mul x1 0x100) (b_add (b_mul x2 0x10000) (b_mul x3 0x1000000))) in
  let lemma_mk4_mk4m (a0 a1 a2 a3:nat8) : Lemma
    (mk4 a0 a1 a2 a3 == mk4m a0 a1 a2 a3)
    =
    assert_norm (mk4 a0 a1 a2 a3 == mk4n a0 a1 a2 a3);
    assert_norm (mk4m a0 a1 a2 a3 == mk4n a0 a1 a2 a3)
    in
  let lemma_small_logxor_32_8 (a b:nat8) : Lemma (logxor #32 a b < 0x100) =
    lemma_to_is_bv8 a;
    lemma_to_is_bv8 b;
    let va = b_i2b #32 a in
    let vb = b_i2b #32 b in
    assert_norm (is_bv8 va /\ is_bv8 vb ==> b_xor va vb == b_and (b_xor va vb) (b_i2b 0xff));
    lemma_i2b_equal (logxor #32 a b) (logand (logxor #32 a b) 0xff);
    logand_le (logxor #32 a b) 0xff
    in
  let lemma_small_nat32_xor_32_8 (a b:nat8) : Lemma (nat32_xor a b < 0x100) =
    Vale.Arch.TypesNative.reveal_ixor_all 32;
    lemma_small_logxor_32_8 a b
    in
  let lemma_small_logxor_32_8 : (_:squash (forall (a b:nat8).{:pattern (logxor #32 a b)} logxor #32 a b < 0x100)) =
    // FStar.Classical.forall_intro_2_with_pat didn't work; TODO: use new non-top-level SMTPat feature
    FStar.Classical.forall_intro_2 lemma_small_logxor_32_8
    in
  let lemma_small_logxor_32_8 : (_:squash (forall (a b:nat8).{:pattern (nat32_xor a b)} nat32_xor a b < 0x100)) =
    FStar.Classical.forall_intro_2 lemma_small_nat32_xor_32_8
    in
  let lemma_xor_mk4b (a0 a1 a2 a3 b0 b1 b2 b3:bv_t 32) : Lemma
    (requires
      is_bv8 a0 /\ is_bv8 a1 /\ is_bv8 a2 /\ is_bv8 a3 /\
      is_bv8 b0 /\ is_bv8 b1 /\ is_bv8 b2 /\ is_bv8 b3
    )
    (ensures
      b_xor (mk4b a0 a1 a2 a3) (mk4b b0 b1 b2 b3) ==
      mk4b (b_xor a0 b0) (b_xor a1 b1) (b_xor a2 b2) (b_xor a3 b3)
    )
    =
    let fact1 =
      is_bv8 a0 /\ is_bv8 a1 /\ is_bv8 a2 /\ is_bv8 a3 /\
      is_bv8 b0 /\ is_bv8 b1 /\ is_bv8 b2 /\ is_bv8 b3
      in
    // This turns out to be too slow:
    // assert_norm (fact1 ==> bvxor (mk4b a0 a1 a2 a3) (mk4b b0 b1 b2 b3) == mk4b (bvxor a0 b0) (bvxor a1 b1) (bvxor a2 b2) (bvxor a3 b3));
    let a = mk4b a0 a1 a2 a3 in
    let b = mk4b b0 b1 b2 b3 in
    assert_norm (fact1 ==> b_and (b_xor a b) (b_i2b 0x000000ff) ==        b_xor a0 b0);
    assert_norm (fact1 ==> b_and (b_xor a b) (b_i2b 0x0000ff00) == b_shl (b_xor a1 b1) 8);
    assert_norm (fact1 ==> b_and (b_xor a b) (b_i2b 0x00ff0000) == b_shl (b_xor a2 b2) 16);
    assert_norm (fact1 ==> b_and (b_xor a b) (b_i2b 0xff000000) == b_shl (b_xor a3 b3) 24);
    let f_pre (x x0 x1 x2 x3:bv_t 32) =
      b_and x (b_i2b 0x000000ff) ==       x0 /\
      b_and x (b_i2b 0x0000ff00) == b_shl x1 8 /\
      b_and x (b_i2b 0x00ff0000) == b_shl x2 16 /\
      b_and x (b_i2b 0xff000000) == b_shl x3 24
      in
    let f (x x0 x1 x2 x3:bv_t 32) : Lemma
      (requires f_pre x x0 x1 x2 x3)
      (ensures bveq x (mk4b x0 x1 x2 x3))
      =
      assert_norm (f_pre x x0 x1 x2 x3 ==> bveq x (mk4b x0 x1 x2 x3))
    in
    f (b_xor a b) (b_xor a0 b0) (b_xor a1 b1) (b_xor a2 b2) (b_xor a3 b3);
    lemma_bveq (b_xor a b) (mk4b (b_xor a0 b0) (b_xor a1 b1) (b_xor a2 b2) (b_xor a3 b3));
    ()
    in
  let lemma_logxor_4_nat8 (a0 a1 a2 a3 b0 b1 b2 b3:nat8) : Lemma
    (logxor #32 (mk4m a0 a1 a2 a3) (mk4m b0 b1 b2 b3) == mk4m (logxor #32 a0 b0) (logxor #32 a1 b1) (logxor #32 a2 b2) (logxor #32 a3 b3))
    =
    lemma_to_is_bv8 a0;
    lemma_to_is_bv8 a1;
    lemma_to_is_bv8 a2;
    lemma_to_is_bv8 a3;
    lemma_to_is_bv8 b0;
    lemma_to_is_bv8 b1;
    lemma_to_is_bv8 b2;
    lemma_to_is_bv8 b3;
    lemma_xor_mk4b (b_i2b a0) (b_i2b a1) (b_i2b a2) (b_i2b a3) (b_i2b b0) (b_i2b b1) (b_i2b b2) (b_i2b b3);
    lemma_i2b_equal
      (logxor #32 (mk4m a0 a1 a2 a3) (mk4m b0 b1 b2 b3))
      (mk4m (logxor #32 a0 b0) (logxor #32 a1 b1) (logxor #32 a2 b2) (logxor #32 a3 b3))
    in
  let lemma_xor_4_nat8_n (a0 a1 a2 a3 b0 b1 b2 b3:nat8) : Lemma
    (nat32_xor (mk4m a0 a1 a2 a3) (mk4m b0 b1 b2 b3) == mk4m (nat32_xor a0 b0) (nat32_xor a1 b1) (nat32_xor a2 b2) (nat32_xor a3 b3))
    =
    Vale.Arch.TypesNative.reveal_ixor_all 32;
    lemma_logxor_4_nat8 a0 a1 a2 a3 b0 b1 b2 b3
    in
  let lemma_xor_4_nat8 (a0 a1 a2 a3 b0 b1 b2 b3:nat8) : Lemma
    (nat32_xor (mk4 a0 a1 a2 a3) (mk4 b0 b1 b2 b3) == mk4 (nat32_xor a0 b0) (nat32_xor a1 b1) (nat32_xor a2 b2) (nat32_xor a3 b3))
    =
    lemma_mk4_mk4m a0 a1 a2 a3;
    lemma_mk4_mk4m b0 b1 b2 b3;
    lemma_mk4_mk4m (nat32_xor a0 b0) (nat32_xor a1 b1) (nat32_xor a2 b2) (nat32_xor a3 b3);
    lemma_xor_4_nat8_n a0 a1 a2 a3 b0 b1 b2 b3
    in
  let rev_nat32 (a b:nat32) : Lemma
    (r32 (nat32_xor a b) == nat32_xor (r32 a) (r32 b))
    =
    calc (==) {
      r32 (nat32_xor a b);
      == {reverse_bytes_nat32_reveal ()}
      be_bytes_to_nat32 (reverse_seq (nat32_to_be_bytes (nat32_xor a b)));
      == {
        let x = nat32_xor a b in
        let y = r32 x in
        let Mkfour a0 a1 a2 a3 = nat_to_four 8 a in
        let Mkfour b0 b1 b2 b3 = nat_to_four 8 b in
        let Mkfour x0 x1 x2 x3 = nat_to_four 8 x in
        let Mkfour y0 y1 y2 y3 = nat_to_four 8 y in
        lemma_xor_4_nat8 a0 a1 a2 a3 b0 b1 b2 b3;
        lemma_xor_4_nat8 a3 a2 a1 a0 b3 b2 b1 b0;
        ()
      }
      nat32_xor (be_bytes_to_nat32 (reverse_seq (nat32_to_be_bytes a))) (be_bytes_to_nat32 (reverse_seq (nat32_to_be_bytes b)));
      == {reverse_bytes_nat32_reveal ()}
      nat32_xor (r32 a) (r32 b);
    }
    // r32 n = be_bytes_to_nat32 (reverse_seq (nat32_to_be_bytes n))
    // lemma_ixor_nth_all 32;
    in
  calc (==) {
    !!(quad32_xor a b);
    == {quad32_xor_reveal ()}
    !!(four_map2 nat32_xor a b);
    == {reveal_reverse_bytes_quad32 (four_map2 nat32_xor a b)}
    four_reverse (four_map r32 (four_map2 nat32_xor a b));
    == {
      let Mkfour a0 a1 a2 a3 = a in
      let Mkfour b0 b1 b2 b3 = b in
      rev_nat32 a0 b0;
      rev_nat32 a1 b1;
      rev_nat32 a2 b2;
      rev_nat32 a3 b3;
      ()
    }
    four_reverse (four_map2 nat32_xor (four_map r32 a) (four_map r32 b));
    == {}
    four_map2 nat32_xor (four_reverse (four_map r32 a)) (four_reverse (four_map r32 b));
    == {reveal_reverse_bytes_quad32 a; reveal_reverse_bytes_quad32 b}
    four_map2 nat32_xor !!a !!b;
    == {quad32_xor_reveal ()}
    quad32_xor !!a !!b;
  }

let rec lemma_ghash_incremental_poly_rec (h_LE:quad32) (y_prev:quad32) (x:seq quad32) (data:int -> poly128) : Lemma
  (requires
    (forall (i:int).{:pattern data i \/ index x i} 0 <= i && i < length x ==>
      data i == of_quad32 (reverse_bytes_quad32 (index x i)))
  )
  (ensures
    of_quad32 (reverse_bytes_quad32 (ghash_incremental_def h_LE y_prev x)) ==
    ghash_poly (of_quad32 (reverse_bytes_quad32 h_LE)) (of_quad32 (reverse_bytes_quad32 y_prev)) data 0 (length x)
  )
  (decreases (length x))
  =
  ghash_incremental_reveal ();
  let (~~) = of_quad32 in
  let (!!) = reverse_bytes_quad32 in
  let (~!) x = ~~(!!x) in
  let h = ~!h_LE in
  let prev = ~!y_prev in
  let m = length x in
  if m > 0 then
    let y_i_minus_1 = ghash_incremental_def h_LE y_prev (all_but_last x) in
    let x_i = last x in
    let xor_LE = quad32_xor y_i_minus_1 x_i in
    let g = gf128_modulus in
    calc (==) {
      ~!(ghash_incremental_def h_LE y_prev x);
      == {}
      ~!(gf128_mul_LE xor_LE h_LE);
      == {lemma_of_to_quad32 (~!xor_LE *~ h)}
      ~!xor_LE *~ h;
      == {calc (==) {
        ~!(quad32_xor y_i_minus_1 x_i);
        == {lemma_reverse_bytes_quad32_xor y_i_minus_1 x_i}
        ~~(quad32_xor !!y_i_minus_1 !!x_i);
        == {lemma_add_quad32 !!y_i_minus_1 !!x_i}
        ~!y_i_minus_1 +. ~!x_i;
      }}
      (~!y_i_minus_1 +. ~!x_i) *~ h;
      == {lemma_ghash_incremental_poly_rec h_LE y_prev (all_but_last x) data}
      (ghash_poly h prev data 0 (m - 1) +. data (m - 1)) *~ h;
      == {}
      ghash_poly h prev data 0 m;
    }

let lemma_ghash_incremental_poly h_LE y_prev x =
  ghash_incremental_reveal ();
  lemma_ghash_incremental_poly_rec h_LE y_prev x (fun_seq_quad32_LE_poly128 x)

let lemma_ghash_incremental_def_0 (h_LE:quad32) (y_prev:quad32) (x:seq quad32)
  =
  ()

let rec ghash_incremental_to_ghash (h:quad32) (x:seq quad32)
  =
  ghash_incremental_reveal ();
  ghash_LE_reveal ();
  if length x = 1 then ()
  else ghash_incremental_to_ghash h (all_but_last x)

let rec lemma_hash_append (h:quad32) (y_prev:quad32) (a b:ghash_plain_LE)
  =
  ghash_incremental_reveal ();
  let ab = append a b in
  assert (last ab == last b);
  if length b = 1 then
    (lemma_slice_first_exactly_in_append a b;
     assert (all_but_last ab == a);
     ())
  else
    lemma_hash_append h y_prev a (all_but_last b);
    lemma_all_but_last_append a b;
    assert(all_but_last ab == append a (all_but_last b));
  ()

let lemma_ghash_incremental0_append (h y0 y1 y2:quad32) (s1 s2:seq quad32) : Lemma
  (requires y1 = ghash_incremental0 h y0 s1 /\
            y2 = ghash_incremental0 h y1 s2)
  (ensures  y2 = ghash_incremental0 h y0 (s1 @| s2))
  =
  let s12 = s1 @| s2 in
  if length s1 = 0 then (
    assert (equal s12 s2)
  ) else (
    if length s2 = 0 then (
      assert (equal s12 s1)
    ) else (
      lemma_hash_append h y0 s1 s2
    )
  );
  ()

let lemma_hash_append2 (h y_init y_mid y_final:quad32) (s1:seq quad32) (q:quad32)
  =
  let qs = create 1 q in
  let s12 = s1 @| qs in
  if length s1 = 0 then (
    assert(equal s12 qs)
  ) else (
    lemma_hash_append h y_init s1 qs
  );
  ()

let lemma_hash_append3 (h y_init y_mid1 y_mid2 y_final:quad32) (s1 s2 s3:seq quad32)
  =
  let s23 = append s2 s3 in
  let s123 = append s1 s23 in
  if length s1 = 0 then (
    assert(equal s123 s23);
    if length s2 = 0 then (
      assert(equal s123 s3);
      ghash_incremental_to_ghash h s3
    ) else
      lemma_hash_append h y_mid1 s2 s3;
      ghash_incremental_to_ghash h s23
  ) else if length s2 = 0 then (
    assert(equal s123 (append s1 s3));
    lemma_hash_append h y_init s1 s3;
    ghash_incremental_to_ghash h (append s1 s3)
  ) else (
    lemma_hash_append h y_init s1 s23;
    lemma_hash_append h y_mid1 s2 s3;
    ghash_incremental_to_ghash h s123;
    ()
  )

let ghash_incremental_bytes_pure_no_extra (old_io io h:quad32) (in_quads:seq quad32) (num_bytes:nat64) : Lemma
  (requires io = ghash_incremental0 h old_io in_quads)
  (ensures  length in_quads == (num_bytes / 16) /\
            num_bytes % 16 == 0 ==>
            (let input_bytes = slice (le_seq_quad32_to_bytes in_quads) 0 num_bytes in
             let padded_bytes = pad_to_128_bits input_bytes in
             let input_quads = le_bytes_to_seq_quad32 padded_bytes in
             num_bytes > 0 ==> length input_quads > 0 /\
                              io == ghash_incremental h old_io input_quads))
  =
  if length in_quads = (num_bytes / 16) && num_bytes % 16 = 0 && num_bytes > 0 then (
    let input_bytes = slice (le_seq_quad32_to_bytes in_quads) 0 num_bytes in
    no_extra_bytes_helper in_quads num_bytes;
    le_bytes_to_seq_quad32_to_bytes in_quads;
    ()
  ) else ()
  ;
  ()


#reset-options "--z3rlimit 30"
let lemma_ghash_incremental_bytes_extra_helper (h y_init y_mid y_final:quad32) (input:seq quad32) (final final_padded:quad32) (num_bytes:nat)  // Precondition definitions
  =
  let num_blocks = num_bytes / 16 in
  let full_blocks = slice input 0 num_blocks in
  let padded_bytes = pad_to_128_bits (slice (le_quad32_to_bytes final) 0 (num_bytes % 16)) in

  // Postcondition definitions
  let input_bytes = slice (le_seq_quad32_to_bytes input) 0 num_bytes in
  let padded_bytes' = pad_to_128_bits input_bytes in
  let input_quads = le_bytes_to_seq_quad32 padded_bytes' in

  lemma_hash_append2 h y_init y_mid y_final full_blocks final_padded;
  assert (y_final == ghash_incremental h y_init (full_blocks @| (create 1 final_padded)));

  //// Need to show that input_quads == full_blocks @| (create 1 final_padded)

  // First show that the inputs to input_quads corresponds
  pad_to_128_bits_le_quad32_to_bytes input num_bytes;
  assert (padded_bytes' == le_seq_quad32_to_bytes (slice input 0 num_blocks) @| pad_to_128_bits (slice (le_quad32_to_bytes final) 0 (num_bytes % 16)));
  assert (padded_bytes' == le_seq_quad32_to_bytes full_blocks @| padded_bytes);

  // Start deconstructing input_quads
  append_distributes_le_bytes_to_seq_quad32 (le_seq_quad32_to_bytes full_blocks) padded_bytes; // Distribute the le_bytes_to_seq_quad32
  assert (input_quads == (le_bytes_to_seq_quad32 (le_seq_quad32_to_bytes full_blocks)) @| (le_bytes_to_seq_quad32 padded_bytes));
  le_bytes_to_seq_quad32_to_bytes (slice input 0 num_blocks);
  assert (input_quads == full_blocks @| (le_bytes_to_seq_quad32 padded_bytes));
  le_bytes_to_seq_quad_of_singleton final_padded padded_bytes;
  assert (input_quads == full_blocks @| (create 1 final_padded));

  ()

let lemma_ghash_incremental_bytes_extra_helper_alt (h y_init y_mid y_final:quad32) (input_blocks:seq quad32) (final final_padded:quad32) (num_bytes:nat) : Lemma
  (requires (1 <= num_bytes /\
             num_bytes < 16 * (length input_blocks) + 16 /\
             16 * (length input_blocks) < num_bytes /\
             num_bytes % 16 <> 0 /\
             y_mid = ghash_incremental0 h y_init input_blocks /\
            (let padded_bytes = pad_to_128_bits (slice (le_quad32_to_bytes final) 0 (num_bytes % 16)) in
             length padded_bytes == 16 /\

             final_padded == le_bytes_to_quad32 padded_bytes /\
             y_final = ghash_incremental h y_mid (create 1 final_padded))))
  (ensures (let input_bytes = slice (le_seq_quad32_to_bytes (append input_blocks (create 1 final))) 0 num_bytes in
            let padded_bytes = pad_to_128_bits input_bytes in
            let input_quads = le_bytes_to_seq_quad32 padded_bytes in
            length padded_bytes == 16 * length input_quads /\
            y_final == ghash_incremental h y_init input_quads))
  =
  let q_in = append input_blocks (create 1 final) in
  let num_blocks = num_bytes / 16 in
  let full_blocks = slice q_in 0 num_blocks in
  assert (equal full_blocks input_blocks);
  lemma_ghash_incremental_bytes_extra_helper h y_init y_mid y_final q_in final final_padded num_bytes


let lemma_ghash_registers (h y_init y0 y1 y2 y3 y4 r0 r1 r2 r3:quad32) (input:seq quad32) (bound:nat)
  =
  lemma_hash_append2 h y_init y0 y1 (slice input 0 bound) r0;

  let s = (slice input 0 bound) @| (create 1 r0) in
  lemma_hash_append2 h y_init y1 y2 s r1;
  let s = s @| (create 1 r1) in
  lemma_hash_append2 h y_init y2 y3 s r2;
  let s = s @| (create 1 r2) in
  lemma_hash_append2 h y_init y3 y4 s r3;
  let s = s @| (create 1 r3) in
  assert (equal s (slice input 0 (bound + 4)));
  ()

(*
let lemma_slice_extension (s:seq quad32) (bound:int) (q:quad32)
  =
  ()
*)
