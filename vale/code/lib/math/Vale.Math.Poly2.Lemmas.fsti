module Vale.Math.Poly2.Lemmas
open FStar.Mul
open Vale.Math.Poly2_s
open Vale.Math.Poly2
open FStar.Seq
module List = FStar.List.Tot

// Derived lemmas (see Vale.Math.Poly2_i for fundamental lemmas)

val lemma_pointwise_equal (a b:poly) (pf:(i:int -> Lemma (a.[i] == b.[i]))) : Lemma
  (a == b)

val lemma_index (a:poly) : Lemma (forall (i:int).{:pattern a.[i]} a.[i] ==> 0 <= i /\ i <= degree a)
val lemma_index_all (_:unit) : Lemma
  (forall (a:poly) (i:int).{:pattern a.[i]} a.[i] ==> 0 <= i /\ i <= degree a)

val lemma_zero_define (_:unit) : Lemma (forall (i:int).{:pattern zero.[i]} not zero.[i])
val lemma_one_define (_:unit) : Lemma (forall (i:int).{:pattern one.[i]} one.[i] == (i = 0))
val lemma_monomial_define (n:nat) : Lemma
  (forall (i:int).{:pattern (monomial n).[i]} (monomial n).[i] == (i = n))
val lemma_monomial_define_all (_:unit) : Lemma
  (forall (n:nat) (i:int).{:pattern (monomial n).[i]} (monomial n).[i] == (i = n))
val lemma_ones_define (n:nat) : Lemma
  (forall (i:int).{:pattern (ones n).[i]} (ones n).[i] == (0 <= i && i < n))
val lemma_ones_define_all (_:unit) : Lemma
  (forall (n:nat) (i:int).{:pattern (ones n).[i]} (ones n).[i] == (0 <= i && i < n))
val lemma_shift_define (p:poly) (n:int) : Lemma
  (forall (i:int).{:pattern (shift p n).[i]} (shift p n).[i] == (p.[i - n] && i >= 0))
val lemma_shift_define_forward (p:poly) (n:int) : Lemma
  (forall (i:int).{:pattern p.[i]} (shift p n).[i + n] == (p.[i] && i + n >= 0))
val lemma_shift_define_all (_:unit) : Lemma
  (forall (p:poly) (n:int) (i:int).{:pattern (shift p n).[i]} (shift p n).[i] == (p.[i - n] && i >= 0))
val lemma_and_define (a b:poly) : Lemma
  (forall (i:int).{:pattern (poly_and a b).[i] \/ a.[i] \/ b.[i]} (poly_and a b).[i] == (a.[i] && b.[i]))
val lemma_and_define_all (_:unit) : Lemma
  (forall (a b:poly).{:pattern (poly_and a b)}
    forall (i:int).{:pattern (poly_and a b).[i] \/ a.[i] \/ b.[i]} (poly_and a b).[i] == (a.[i] && b.[i]))
val lemma_or_define (a b:poly) : Lemma
  (forall (i:int).{:pattern (poly_or a b).[i] \/ a.[i] \/ b.[i]} (poly_or a b).[i] == (a.[i] || b.[i]))
val lemma_or_define_all (_:unit) : Lemma
  (forall (a b:poly).{:pattern (poly_or a b)}
    forall (i:int).{:pattern (poly_or a b).[i] \/ a.[i] \/ b.[i]} (poly_or a b).[i] == (a.[i] || b.[i]))
val lemma_mask_define (p:poly) (n:nat) : Lemma
  (forall (i:int).{:pattern p.[i] \/ (mask p n).[i]} (mask p n).[i] == (p.[i] && i < n))
val lemma_mask_define_all (_:unit) : Lemma
  (forall (p:poly) (n:nat) (i:int).{:pattern (mask p n).[i]} (mask p n).[i] == (p.[i] && i < n))
val lemma_reverse_define (a:poly) (n:nat) : Lemma
  (forall (i:int).{:pattern (reverse a n).[i]} (reverse a n).[i] == (a.[n - i] && i >= 0))
val lemma_reverse_define_all (_:unit) : Lemma
  (forall (a:poly) (n:nat).{:pattern (reverse a n)}
    (forall (i:int).{:pattern (reverse a n).[i]} (reverse a n).[i] == (a.[n - i] && i >= 0)))

val lemma_degree_negative (a:poly) : Lemma (requires degree a < 0) (ensures a == zero)

val lemma_degree_is (a:poly) (n:int) : Lemma
  (requires (n >= 0 ==> a.[n]) /\ (forall (i:int).{:pattern a.[i]} i > n ==> not a.[i]))
  (ensures degree a == (if n < 0 then -1 else n))

val lemma_zero_degree : (_:unit{degree zero == -1})
val lemma_one_degree : (_:unit{degree one == 0})

val lemma_monomial_degree (n:nat) : Lemma
  (degree (monomial n) == n)
  [SMTPat (degree (monomial n))]

val lemma_ones_degree (n:nat) : Lemma
  (degree (ones n) == n - 1)
  [SMTPat (degree (ones n))]

val lemma_shift_degree (a:poly) (n:int) : Lemma
  (degree (shift a n) == (if degree a < 0 || degree a + n < 0 then -1 else degree a + n))
  [SMTPat (degree (shift a n))]

val lemma_and_degree (a b:poly) : Lemma
  (degree (poly_and a b) <= degree a /\ degree (poly_and a b) <= degree b)
  [SMTPat (degree (poly_and a b))]

val lemma_or_degree (a b:poly) : Lemma
  (ensures (
    let d = degree (poly_or a b) in
    d >= degree a /\
    d >= degree b /\
    (d == degree a \/ d == degree b)
  ))
  [SMTPat (degree (poly_or a b))]

val lemma_mask_degree (a:poly) (n:nat) : Lemma
  (degree (mask a n) < n)
  [SMTPat (degree (mask a n))]

val lemma_reverse_degree (a:poly) (n:nat) : Lemma
  (degree (reverse a n) <= n)
  [SMTPat (degree (reverse a n))]

val lemma_of_list_degree (l:list bool) : Lemma
  (requires (
    let len = List.length l in
    len == 0 \/ normalize (b2t (List.index l (len - 1)))
  ))
  (ensures (
    let len = normalize_term (List.length l) in
    let a = of_seq (seq_of_list l) in
    degree a == len - 1 /\
    (forall (i:int).{:pattern a.[i]} a.[i] ==> (0 <= i && i < len))
  ))

val lemma_add_define (a b:poly) : Lemma
  (forall (i:int).{:pattern (a +. b).[i] \/ a.[i] \/ b.[i]} (a +. b).[i] == (a.[i] <> b.[i]))

val lemma_add_define_all (_:unit) : Lemma
  (forall (a b:poly).{:pattern (a +. b)}
    (forall (i:int).{:pattern (a +. b).[i] \/ a.[i] \/ b.[i]} (a +. b).[i] == (a.[i] <> b.[i])))

val lemma_add_zero_right (a:poly) : Lemma ((a +. zero) == a)
val lemma_add_zero_left (a:poly) : Lemma ((zero +. a) == a)

val lemma_add_all (_:unit) : Lemma
  (ensures
    (forall (a:poly).{:pattern (a +. zero)} (a +. zero) == a) /\
    (forall (a:poly).{:pattern (a +. a)} (a +. a) == zero) /\
    (forall (a b:poly).{:pattern (a +. b)} a +. b == b +. a) /\
    (forall (a b c:poly).{:pattern (a +. (b +. c)) \/ ((a +. b) +. c)} a +. (b +. c) == (a +. b) +. c)
  )

val lemma_bitwise_all (_:unit) : Lemma
  (ensures
    (forall (a:poly) (i:int).{:pattern a.[i]} a.[i] ==> 0 <= i /\ i <= degree a) /\
    (forall (i:int).{:pattern zero.[i]} not zero.[i]) /\
    (forall (i:int).{:pattern one.[i]} one.[i] == (i = 0)) /\
    (forall (n:nat) (i:int).{:pattern (monomial n).[i]} (monomial n).[i] == (i = n)) /\
    (forall (n:nat) (i:int).{:pattern (ones n).[i]} (ones n).[i] == (0 <= i && i < n)) /\
    (forall (p:poly) (n:int) (i:int).{:pattern (shift p n).[i]} (shift p n).[i] == (p.[i - n] && i >= 0)) /\
    (forall (a b:poly) (i:int).{:pattern (poly_and a b).[i]} (poly_and a b).[i] == (a.[i] && b.[i])) /\
    (forall (a b:poly) (i:int).{:pattern (poly_or a b).[i]} (poly_or a b).[i] == (a.[i] || b.[i])) /\
    (forall (p:poly) (n:nat) (i:int).{:pattern (mask p n).[i]} (mask p n).[i] == (p.[i] && i < n)) /\
    (forall (a:poly) (n:nat) (i:int).{:pattern (reverse a n).[i]} (reverse a n).[i] == (a.[n - i] && i >= 0)) /\
    (forall (a b:poly) (i:int).{:pattern (a +. b).[i]} (a +. b).[i] == (a.[i] <> b.[i]))
  )

val lemma_monomial_add_degree (n:nat) (a:poly) : Lemma
  (requires degree a < n)
  (ensures degree (monomial n +. a) == n /\ degree (a +. monomial n) == n)

val lemma_and_zero (a:poly) : Lemma
  (poly_and a zero == zero /\ poly_and zero a == zero)

val lemma_and_ones (a:poly) (n:nat) : Lemma
  (requires degree a < n)
  (ensures poly_and a (ones n) == a /\ poly_and (ones n) a == a)

val lemma_and_consts (_:unit) : Lemma
  (ensures
    (forall (a:poly).{:pattern (poly_and a zero)} poly_and a zero == zero) /\
    (forall (a:poly).{:pattern (poly_and zero a)} poly_and zero a == zero) /\
    (forall (a:poly) (n:nat).{:pattern (poly_and a (ones n))} degree a < n ==> poly_and a (ones n) == a) /\
    (forall (a:poly) (n:nat).{:pattern (poly_and (ones n) a)} degree a < n ==> poly_and (ones n) a == a)
  )

val lemma_or_zero (a:poly) : Lemma
  (poly_or a zero == a /\ poly_or zero a == a)

val lemma_or_ones (a:poly) (n:nat) : Lemma
  (requires degree a < n)
  (ensures poly_or a (ones n) == ones n /\ poly_or (ones n) a == ones n)

val lemma_or_consts (_:unit) : Lemma
  (ensures
    (forall (a:poly).{:pattern (poly_or a zero)} poly_or a zero == a) /\
    (forall (a:poly).{:pattern (poly_or zero a)} poly_or zero a == a) /\
    (forall (a:poly) (n:nat).{:pattern (poly_or a (ones n))} degree a < n ==> poly_or a (ones n) == ones n) /\
    (forall (a:poly) (n:nat).{:pattern (poly_or (ones n) a)} degree a < n ==> poly_or (ones n) a == ones n)
  )

val lemma_mul_distribute_left (a b c:poly) : Lemma ((a +. b) *. c == (a *. c) +. (b *. c))
val lemma_mul_distribute_right (a b c:poly) : Lemma (a *. (b +. c) == (a *. b) +. (a *. c))

val lemma_mul_smaller_is_zero (a b:poly) : Lemma
  (requires degree b > degree (a *. b))
  (ensures a == zero /\ a *. b == zero)

val lemma_mul_monomials (m n:nat) : Lemma
  (monomial (m + n) == monomial m *. monomial n)

val lemma_add_reverse (a b:poly) (n:nat) : Lemma
  (reverse (a +. b) n == reverse a n +. reverse b n)

val lemma_mul_reverse_shift_1 (a b:poly) (n:nat) : Lemma
  (requires degree a <= n /\ degree b <= n)
  (ensures reverse (a *. b) (n + n + 1) == shift (reverse a n *. reverse b n) 1)

val lemma_shift_is_mul_right (a:poly) (n:nat) : Lemma (shift a n == a *. monomial n)
val lemma_shift_is_mul_left (a:poly) (n:nat) : Lemma (shift a n == monomial n *. a)

val lemma_shift_shift (a:poly) (m n:int) : Lemma
  (requires m >= 0 \/ n <= 0)
  (ensures shift a (m + n) == shift (shift a m) n)

val lemma_mul_all (_:unit) : Lemma
  (ensures
    (forall (a:poly).{:pattern (a *. zero)} (a *. zero) == zero) /\
    (forall (a:poly).{:pattern (a *. one)} (a *. one) == a) /\
    (forall (a b:poly).{:pattern (a *. b)} a *. b == b *. a) /\
    (forall (a b c:poly).{:pattern (a *. (b *. c)) \/ ((a *. b) *. c)} a *. (b *. c) == (a *. b) *. c)
  )

val lemma_mod_distribute (a b c:poly) : Lemma
  (requires degree c >= 0)
  (ensures (a +. b) %. c == (a %. c) +. (b %. c))

val lemma_div_mod_unique (a b x y:poly) : Lemma
  (requires
    degree b >= 0 /\
    degree y < degree b /\
    a == x *. b +. y
  )
  (ensures
    x == a /. b /\
    y == a %. b
  )

val lemma_div_mod_exact (a b:poly) : Lemma
  (requires degree b >= 0)
  (ensures (a *. b) /. b == a /\ (a *. b) %. b == zero)

val lemma_mod_small (a b:poly) : Lemma
  (requires degree b >= 0 /\ degree a < degree b)
  (ensures a %. b == a)

val lemma_mod_mod (a b:poly) : Lemma
  (requires degree b >= 0)
  (ensures (a %. b) %. b == a %. b)

val lemma_mod_cancel (a:poly) : Lemma
  (requires degree a >= 0)
  (ensures a %. a == zero)

// TODO: rename to lemma_mod_mul_mod_left and switch b and c
val lemma_mod_mul_mod (a b c:poly) : Lemma
  (requires degree b >= 0)
  (ensures ((a %. b) *. c) %. b == (a *. c) %. b)

val lemma_mod_mul_mod_right (a b c:poly) : Lemma
  (requires degree c >= 0)
  (ensures (a *. (b %. c)) %. c == (a *. b) %. c)

val lemma_shift_mod (a b:poly) (n:nat) : Lemma
  (requires degree b >= 0)
  (ensures shift (a %. b) n %. b == shift a n %. b)

val lemma_mod_reduce (a b c:poly) : Lemma
  (requires degree (b +. c) >= 0)
  (ensures (a *. b) %. (b +. c) == (a *. c) %. (b +. c))

val lemma_split_define (a:poly) (n:nat) : Lemma
  (ensures (
    let b = monomial n in
    a == (a /. b) *. b +. (a %. b) /\
    shift (a /. b) n == (a /. b) *. b /\
    (forall (i:int).{:pattern a.[i] \/ (a %. b).[i]} a.[i] == (if i < n then (a %. b).[i] else (a /. b).[i - n]))
  ))

val lemma_split_define_forward (a:poly) (n:nat) : Lemma
  (ensures (
    let b = monomial n in
    a == (a /. b) *. b +. (a %. b) /\
    shift (a /. b) n == (a /. b) *. b /\
    (forall (i:int).{:pattern (a %. b).[i]} i < n ==> (a %. b).[i] == a.[i]) /\
    (forall (i:nat).{:pattern (a /. b).[i]} (a /. b).[i] == a.[i + n])
  ))

val lemma_combine_define (a b:poly) (n:nat) : Lemma
  (requires degree b < n)
  (ensures (
    let m = monomial n in
    let ab = a *. m +. b in
    a == ab /. m /\
    b == ab %. m /\
    shift a n == a *. m /\
    (forall (i:int).{:pattern ab.[i] \/ b.[i]} ab.[i] == (if i < n then b.[i] else a.[i - n]))
  ))

val lemma_mask_is_mod (a:poly) (n:nat) : Lemma
  (mask a n == a %. monomial n)

val lemma_shift_is_div (a:poly) (n:nat) : Lemma
  (shift a (-n) == a /. monomial n)

val lemma_mod_monomial (a:poly) (n:nat) : Lemma
  (forall (i:int).{:pattern (a %. monomial n).[i]} (a %. monomial n).[i] <==> i < n && a.[i])

