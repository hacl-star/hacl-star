module Vale.Math.Poly2.Defs
open FStar.Mul
open Vale.Def.Prop_s
open FStar.Seq
open Vale.Math.Poly2.Defs_s
unfold let max = FStar.Math.Lib.max

#reset-options "--z3rlimit 10"

let poly_equal (a b:poly) : prop0 =
  (forall (i:nat).{:pattern a.[i] \/ b.[i]} a.[i] == b.[i])

unfold let ( =. ) = poly_equal
unfold let ( +. ) = add
unfold let ( *. ) = mul
unfold let ( /. ) = div
unfold let ( %. ) = mod

let lemma_poly_equal_elim (a b:poly) : Lemma
  (requires a =. b)
  (ensures a == b)
  (decreases (length a + length b))
  [SMTPat (poly_equal a b)]
  =
  let len = max (length a) (length b) in
  assert (len > 0 ==> a.[len - 1] == b.[len - 1]);
  assert (length a == length b);
  assert (forall (i:nat).{:pattern (index a i) \/ (index b i)} a.[i] == b.[i]);
  assert (equal a b)

let lemma_pointwise_equal (a b:poly) (pf:(i:int -> Lemma (a.[i] == b.[i]))) : Lemma (a == b) =
  FStar.Classical.forall_intro pf;
  lemma_poly_equal_elim a b


// ADDITION

let lemma_add_zero (a:poly) : Lemma ((a +. zero) =. a) = ()
let lemma_add_cancel (a:poly) : Lemma ((a +. a) =. zero) = ()
let lemma_add_cancel_eq (a b:poly) : Lemma (requires (a +. b) == zero) (ensures a =. b) = ()
let lemma_add_commute (a b:poly) : Lemma ((a +. b) =. (b +. a)) = ()
let lemma_add_associate (a b c:poly) : Lemma ((a +. (b +. c)) =. ((a +. b) +. c)) = ()

let lemma_add_move (a b:poly) : Lemma (ensures a == (a +. b) +. b) =
  lemma_add_associate a b b;
  lemma_add_cancel b;
  lemma_add_zero a


// SUMMATION

let lemma_sum_empty (j:int) (f:int -> bool) : Lemma
  (requires True)
  (ensures not (sum_of_bools j j f))
  [SMTPat (sum_of_bools j j f)]
  =
  ()

let rec lemma_sum_of_zero (j k:int) (f:int -> bool) : Lemma
  (requires (forall (i:int).{:pattern (f i)} j <= i /\ i < k ==> not (f i)))
  (ensures not (sum_of_bools j k f))
  (decreases (k - j))
  =
  if j < k then lemma_sum_of_zero j (k - 1) f

let rec lemma_sum_join (i j k:int) (f:int -> bool) : Lemma
  (requires i <= j /\ j <= k)
  (ensures sum_of_bools i k f == (sum_of_bools i j f <> sum_of_bools j k f))
  (decreases (k - j))
  =
  if j < k then lemma_sum_join i j (k - 1) f

let lemma_sum_extend (j' j k k':int) (f:int -> bool) : Lemma
  (requires
    j' <= j /\ j <= k /\ k <= k' /\
    (forall (i:int).{:pattern (f i)} j' <= i /\ i < j ==> not (f i)) /\
    (forall (i:int).{:pattern (f i)} k <= i /\ i < k' ==> not (f i))
  )
  (ensures sum_of_bools j' k' f == sum_of_bools j k f)
  =
  lemma_sum_of_zero j' j f;
  lemma_sum_of_zero k k' f;
  lemma_sum_join j' j k f;
  lemma_sum_join j' k k' f

let rec lemma_sum_of_pairs (j k:int) (f g h:int -> bool) : Lemma
  (requires (forall (i:int).{:pattern (f i)} j <= i /\ i < k ==> f i == (g i <> h i)))
  (ensures sum_of_bools j k f == (sum_of_bools j k g <> sum_of_bools j k h))
  (decreases (k - j))
  =
  if j < k then lemma_sum_of_pairs j (k - 1) f g h

let rec lemma_sum_shift (j k:int) (shift:int) (f g:int -> bool) : Lemma
  (requires (forall (i:int).{:pattern (f i)} j <= i /\ i < k ==> f i == g (i + shift)))
  (ensures sum_of_bools j k f == sum_of_bools (j + shift) (k + shift) g)
  (decreases (k - j))
  =
  if j < k then lemma_sum_shift j (k - 1) shift f g

let rec lemma_sum_invert_rec (j m k:int) (f g:int -> bool) : Lemma
  (requires
    j <= m /\ m <= k /\
    sum_of_bools j k f == (sum_of_bools j m f <> sum_of_bools (1 - k) (1 - m) g) /\
    (forall (i:int).{:pattern (f i)} j <= i /\ i < k ==> f i == g (-i))
  )
  (ensures sum_of_bools j k f == sum_of_bools (1 - k) (1 - j) g)
  (decreases (m - j))
  =
  if j < m then lemma_sum_invert_rec j (m - 1) k f g

let lemma_sum_invert (j k:int) (f g:int -> bool) : Lemma
  (requires (forall (i:int).{:pattern (f i)} j <= i /\ i < k ==> f i == g (-i)))
  (ensures sum_of_bools j k f == sum_of_bools (1 - k) (1 - j) g)
  =
  if j < k then lemma_sum_invert_rec j k k f g

let lemma_sum_reverse (j k:int) (f g:int -> bool) : Lemma
  (requires (forall (i:int).{:pattern (f i)} j <= i /\ i < k ==> f i == g (k + j - i - 1)))
  (ensures sum_of_bools j k f == sum_of_bools j k g)
  =
  let f' (i:int) = f (-i) in
  lemma_sum_invert j k f f';
  lemma_sum_shift j k (1 - (k + j)) g f'

let rec lemma_sum_mul (j k:int) (b:bool) (f g:int -> bool) : Lemma
  (requires (forall (i:int).{:pattern (f i)} j <= i /\ i < k ==> f i == (b && g i)))
  (ensures sum_of_bools j k f == (b && sum_of_bools j k g))
  (decreases (k - j))
  =
  if j < k then lemma_sum_mul j (k - 1) b f g

let rec lemma_sum_swap (j k:int) (ff gg:int -> int -> bool) (f g:int -> bool) : Lemma
  (requires
    (forall (x:int).{:pattern (f x)} j <= x /\ x < k ==> f x == sum_of_bools j (j + k - x) (ff x)) /\
    (forall (y:int).{:pattern (g y)} j <= y /\ y < k ==> g y == sum_of_bools j (j + k - y) (gg y)) /\
    (forall (x y:int).{:pattern (ff x y)} ff x y == gg y x)
  )
  (ensures sum_of_bools j k f == sum_of_bools j k g)
  (decreases (k - j))
  =
  if (j < k) then
  (
    let k1 = k - 1 in
    let f1 x = sum_of_bools j (j + k1 - x) (ff x) in
    let g1 y = sum_of_bools j (j + k1 - y) (gg y) in
    let f' x = ff x (j + k1 - x) in
    let g' y = gg y (j + k1 - y) in
    lemma_sum_reverse j k f' g'; // summing f' and g' gives same answer, computed in reverse order
    // sum_of_bools j k f' == sum_of_bools j k g'
    // sum_of_bools j k1 f' + ff k1 j == sum_of_bools j k1 g' + gg k1 j
    lemma_sum_swap j k1 ff gg f1 g1; // by induction: sum_of_bools j k1 f1 == sum_of_bools j k1 g1
    // sum_of_bools j k1 f1 + (sum_of_bools j k1 f' + ff k1 j) == sum_of_bools j k1 g1 + (sum_of_bools j k1 g' + gg k1 j)
    // (sum_of_bools j k1 f1 + sum_of_bools j k1 f') + ff k1 j == (sum_of_bools j k1 g1 + sum_of_bools j k1 g') + gg k1 j
    lemma_sum_of_pairs j k1 f f1 f'; // sum_of_bools j k1 f1 + sum_of_bools j k1 f' == sum_of_bools j k1 f
    lemma_sum_of_pairs j k1 g g1 g'  // sum_of_bools j k1 g1 + sum_of_bools j k1 g' == sum_of_bools j k1 g
    // sum_of_bools j k1 f + ff k1 j == sum_of_bools j k1 g + gg k1 j
    // sum_of_bools j k f == sum_of_bools j k g
  )

// Corollary for lemma_mul_associate
let rec lemma_sum_swap_mul_associate (k:int) (ff gg:int -> int -> bool) (f g:int -> bool) : Lemma
  (requires
    k > 0 /\
    (forall (x:nat).{:pattern (f x)} f x == sum_of_bools 0 (x + 1) (ff x)) /\
    (forall (y:nat).{:pattern (g y)} g y == sum_of_bools y k (gg y)) /\
    (forall (x y:int).{:pattern (ff x y)} ff x y ==> 0 <= x /\ x < k /\ 0 <= y /\ y <= x) /\
    (forall (x y:int).{:pattern (ff x y) \/ (gg y x)} ff x y == gg y x)
  )
  (ensures sum_of_bools 0 k f == sum_of_bools 0 k g)
  =
  // Example: k = 3, k' = 5, '#' shows non-zero elements of ff, '0'/'#' shows input to lemma_sum_swap:
  //     0
  //     00
  // /|\ 00#
  //  |  0##0
  //  y  ###00
  //
  //     x -->
  let k' = k + k - 1 in
  let lemma_f (x:nat) : Lemma
    (ensures
      (k <= x ==> not (f x)) /\
      (x < k' ==> f x == sum_of_bools 0 (k' - x) (ff x))
    )
    =
    (if k <= x then lemma_sum_of_zero 0 (x + 1) (ff x));
    lemma_sum_of_zero (if x < k then x + 1 else 0) (k' - x) (ff x);
    (if x < k then lemma_sum_join 0 (x + 1) (k' - x) (ff x));
    ()
    in
  let lemma_g (y:nat) : Lemma
    (ensures
      (k <= y ==> not (g y)) /\
      (y < k' ==> g y == sum_of_bools 0 (k' - y) (gg y))
    )
    =
    (if k <= y then lemma_sum_of_zero 0 (y + 1) (gg y));
    (if y < k then lemma_sum_of_zero 0 y (gg y));
    lemma_sum_of_zero (if y < k then k else 0) (k' - y) (gg y);
    (if y < k then lemma_sum_extend 0 y k (k' - y) (gg y));
    ()
    in
  FStar.Classical.forall_intro lemma_f;
  FStar.Classical.forall_intro lemma_g;
  lemma_sum_swap 0 k' ff gg f g;
  lemma_sum_extend 0 0 k k' f;
  lemma_sum_extend 0 0 k k' g;
  ()

let rec lemma_sum_pointwise_equal (j k:int) (f g:int -> bool) (pf:(i:int -> Lemma (f i == g i))) : Lemma
  (ensures sum_of_bools j k f == sum_of_bools j k g)
  (decreases (k - j))
  =
  if j < k then
  (
    pf (k - 1);
    lemma_sum_pointwise_equal j (k - 1) f g pf
  )


// MULTIPLICATION

let lemma_mul_element (a b:poly) (k:int) : Lemma
  (requires True)
  (ensures (a *. b).[k] == mul_element a b k)
  [SMTPat (a *. b).[k]]
  =
  if k >= length a + length b then lemma_sum_of_zero 0 (k + 1) (mul_element_fun a b k)

let lemma_mul_zero (a:poly) : Lemma ((a *. zero) =. zero) =
  let f (k:nat) : Lemma (not (mul_element a zero k)) =
    lemma_sum_of_zero 0 (k + 1) (mul_element_fun a zero k)
    in
  FStar.Classical.forall_intro f

let lemma_mul_one (a:poly) : Lemma ((a *. one) =. a) =
  let f (k:nat) : Lemma (mul_element a one k == a.[k]) =
    lemma_sum_of_zero 0 k (mul_element_fun a one k)
    in
  FStar.Classical.forall_intro f

let lemma_mul_commute (a b:poly) : Lemma ((a *. b) =. (b *. a)) =
  let f (k:nat) : Lemma (mul_element a b k == mul_element b a k) =
    lemma_sum_reverse 0 (k + 1) (mul_element_fun a b k) (mul_element_fun b a k)
    in
  FStar.Classical.forall_intro f

let lemma_mul_associate (a b c:poly) : Lemma (a *. (b *. c) =. (a *. b) *. c) =
  let f (k:nat) : Lemma (mul_element a (b *. c) k == mul_element (a *. b) c k) =
    let abc1 (i:int) (j:int) = a.[j] && b.[i - j] && c.[k - i] in
    let abc2 (j:int) (i:int) = a.[j] && b.[i - j] && c.[k - i] in
    let abc3 (j:int) (i:int) = a.[j] && b.[i] && c.[k - j - i] in
    let sum_abc1 (i:int) = sum_of_bools 0 (i + 1) (abc1 i) in
    let sum_abc2 (j:int) = sum_of_bools j (k + 1) (abc2 j) in
    let sum_abc3 (j:int) = sum_of_bools 0 (k + 1 - j) (abc3 j) in
    let l1 (i:int) : Lemma (mul_element_fun (a *. b) c k i == sum_abc1 i) =
      lemma_sum_mul 0 (i + 1) c.[k - i] (abc1 i) (mul_element_fun a b i)
      in
    let l2 (j:int) : Lemma (sum_abc2 j == sum_abc3 j) =
      lemma_sum_shift 0 (k + 1 - j) j (abc3 j) (abc2 j)
      in
    let l3 (j:int) : Lemma (mul_element_fun a (b *. c) k j == sum_abc3 j) =
      lemma_sum_mul 0 (k + 1 - j) a.[j] (abc3 j) (mul_element_fun b c (k - j))
      in
    // mul_element (a *. b) c k
    // sum[0 <= i <= k] (a *. b)[i] * c[k - i]
    // sum[0 <= i <= k] (sum[0 <= j <= i] a[j] * b[i - j]) * c[k - i])
    lemma_sum_pointwise_equal 0 (k + 1) (mul_element_fun (a *. b) c k) sum_abc1 l1;
    // sum[0 <= i <= k] sum[0 <= j <= i] a[j] * b[i - j] * c[k - i]
    lemma_sum_swap_mul_associate (k + 1) abc1 abc2 sum_abc1 sum_abc2;
    // sum[0 <= j <= k] sum[j <= i <= k] a[j] * b[i - j] * c[k - i]
    lemma_sum_pointwise_equal 0 (k + 1) sum_abc2 sum_abc3 l2;
    // sum[0 <= j <= k] sum[0 <= i <= k - j] a[j] * b[i] * c[k - j - i]
    lemma_sum_pointwise_equal 0 (k + 1) (mul_element_fun a (b *. c) k) sum_abc3 l3;
    // sum[0 <= j <= k] a[j] * (sum[0 <= i <= k - j] b[i] * c[k - j - i])
    // sum[0 <= j <= k] (a[j] * (b *. c)[k - j])
    // mul_element a (b *. c) k
    ()
    in
  FStar.Classical.forall_intro f

let lemma_mul_distribute (a b c:poly) : Lemma (a *. (b +. c) =. (a *. b) +. (a *. c)) =
  let f (k:nat) : Lemma
    (ensures mul_element a (b +. c) k == (mul_element a b k <> mul_element a c k))
    =
    lemma_sum_of_pairs 0 (k + 1)
      (mul_element_fun a (b +. c) k)
      (mul_element_fun a b k)
      (mul_element_fun a c k)
    in
  FStar.Classical.forall_intro f

let lemma_mul_distribute_left (a b c:poly) : Lemma ((a +. b) *. c =. (a *. c) +. (b *. c)) =
  lemma_mul_commute (a +. b) c;
  lemma_mul_commute a c;
  lemma_mul_commute b c;
  lemma_mul_distribute c a b

let rec lemma_shift_is_mul (a:poly) (n:nat) : Lemma (shift a n =. a *. (monomial n)) =
  let an = shift a n in
  let b = monomial n in
  let lem (k:nat) : Lemma (an.[k] == mul_element a b k) =
    if k < n then
      lemma_sum_of_zero 0 k (mul_element_fun a b k)
    else
      lemma_sum_extend 0 (k - n) (k - n + 1) (k + 1) (mul_element_fun a b k)
    in
  FStar.Classical.forall_intro lem

let lemma_mul_degree (a b:poly) : Lemma
  (degree (a *. b) == (if degree a >= 0 && degree b >= 0 then degree a + degree b else -1))
  =
  if degree a >= 0 && degree b >= 0 then
  (
    let len = length a + length b in
    lemma_sum_of_zero 0 len (mul_element_fun a b (len - 1));
    lemma_sum_extend 0 (length a - 1) (length a) (len - 1) (mul_element_fun a b (len - 2));
    assert (not (a *. b).[len - 1]);
    assert ((a *. b).[len - 2]);
    ()
  )
  else if degree a < 0 then
  (
    assert (a =. zero);
    lemma_mul_zero b;
    lemma_mul_commute b zero;
    ()
  )
  else
  (
    assert (b =. zero);
    lemma_mul_zero a;
    ()
  )

let lemma_mul_reverse (a b:poly) (n:nat) : Lemma
  (requires degree a <= n /\ degree b <= n)
  (ensures reverse (a *. b) (n + n) =. reverse a n *. reverse b n)
  =
  let ab = a *. b in
  let rab = reverse ab (n + n) in
  let ra = reverse a n in
  let rb = reverse b n in
  lemma_mul_degree a b;
  lemma_mul_degree ra rb;
  let f (k:int) : Lemma (rab.[k] == (ra *. rb).[k]) =
    if 0 <= k && k <= n + n then
    (
      let f0 = mul_element_fun ra rb k in
      let f1 (i:int) : bool = a.[n + i] && b.[n - k - i] in
      let f2 = mul_element_fun a b (n + n - k) in
      // mul_element a b (n + n - k) == sum_of_bools 0 (n + n + 1 - k) f2

      // mul_element ra rb k == sum_of_bools 0 (k + 1) f0
      lemma_sum_invert 0 (k + 1) f0 f1;
      // mul_element ra rb k == sum_of_bools (-k) 1 f1
      lemma_sum_shift (-k) 1 n f1 f2;
      // mul_element ra rb k == sum_of_bools (n - k) (n + 1) f2

      let lo = min (n - k) 0 in
      let hi = max (n + 1) (n + n + 1 - k) in
      lemma_sum_extend lo 0 (n + n + 1 - k) hi f2;
      lemma_sum_extend lo (n - k) (n + 1) hi f2;
      ()
    )
    in
  lemma_pointwise_equal rab (ra *. rb) f



// DIVISION, MOD

let rec lemma_div_mod (a b:poly) : Lemma
  (requires length b > 0)
  (ensures a =. (a /. b) *. b +. (a %. b))
  (decreases (length a))
  =
  if length a < length b then
  (
    lemma_mul_zero b;
    lemma_mul_commute b zero;
    ()
  )
  else
  (
    let _ = assert (a.[length a - 1]) in
    let n = length a - length b in
    let a' = a +. (shift b n) in
    let xn = monomial n in
    lemma_shift_is_mul b n;
    lemma_mul_commute b xn;
    // a' == a +. xn *. b
    // (a /. b == a' /. b +. xn);
    lemma_add_move (a' /. b) xn;
    // (a' /. b == a /. b +. xn);
    lemma_div_mod a' b;
    // a' == (a' /. b) *. b +. (a' %. b)
    // a +. xn * b == (a /. b + xn) *. b +. (a %. b))
    lemma_mul_distribute_left (a /. b) xn b;
    // a +. xn *. b == (a /. b) *. b +. xn *. b +. (a %. b)
    // a == (a /. b) *. b +. (a %. b)
    ()
  )

let rec lemma_div_degree (a b:poly) : Lemma
  (requires length b > 0)
  (ensures degree (a /. b) == (if degree a < degree b then -1 else degree a - degree b))
  (decreases (length a))
  =
  if length a >= length b then
  (
    let _ = assert (a.[length a - 1]) in
    let n = length a - length b in
    let a' = add a (shift b n) in
    lemma_div_degree a' b;
    assert ((a /. b).[degree a - degree b]);
    ()
  )

let rec lemma_mod_degree (a b:poly) : Lemma
  (requires length b > 0)
  (ensures degree (a %. b) < degree b)
  (decreases (length a))
  =
  if length a >= length b then
  (
    let _ = assert (a.[length a - 1]) in
    let n = length a - length b in
    let a' = add a (shift b n) in
    lemma_mod_degree a' b
  )

