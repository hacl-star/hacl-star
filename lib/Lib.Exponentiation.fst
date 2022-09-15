module Lib.Exponentiation

open FStar.Mul

module Loops = Lib.LoopCombinators

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

//--------------------

let lemma_inverse_one #t k =
  lemma_inverse k.cm.one;
  assert (k.cm.mul (inverse cm.one) cm.one == cm.one);
  k.cm.lemma_one (inverse cm.one);
  assert (inverse k.cm.one == cm.one)


val lemma_mul_cancel_inverse: #t:Type -> k:abelian_group t -> a:t -> b:t ->
  Lemma (cm.mul (inverse a) (cm.mul a b) == b)

let lemma_mul_cancel_inverse #t k a b =
  calc (==) {
    cm.mul (inverse a) (cm.mul a b);
    (==) { cm.lemma_mul_assoc (inverse a) a b }
    cm.mul (cm.mul (inverse a) a) b;
    (==) { lemma_inverse a }
    cm.mul cm.one b;
    (==) { cm.lemma_mul_comm cm.one b }
    cm.mul b cm.one;
    (==) { cm.lemma_one b }
    b;
  }

val lemma_cancellation: #t:Type -> k:abelian_group t -> a:t -> b:t -> c:t -> Lemma
  (requires cm.mul a b == cm.mul a c)
  (ensures  b == c)

let lemma_cancellation #t k a b c =
  assert (cm.mul (inverse a) (cm.mul a b) == cm.mul (inverse a) (cm.mul a c));
  lemma_mul_cancel_inverse #t k a b;
  lemma_mul_cancel_inverse #t k a c


let lemma_inverse_id #t k a =
  lemma_inverse a;
  lemma_inverse (inverse a);
  assert (cm.mul (inverse a) a == cm.one);
  assert (cm.mul (inverse (inverse a)) (inverse a) == cm.one);
  cm.lemma_mul_comm (inverse (inverse a)) (inverse a);
  lemma_cancellation k (inverse a) a (inverse (inverse a));
  assert (a == (inverse (inverse a)))


let lemma_inverse_mul #t k a b =
  lemma_inverse (cm.mul a b);
  cm.lemma_mul_comm (inverse (cm.mul a b)) (cm.mul a b);
  assert (cm.mul (cm.mul a b) (inverse (cm.mul a b)) == cm.one);
  calc (==) {
    cm.mul (cm.mul a b) (cm.mul (inverse a) (inverse b));
    (==) { cm.lemma_mul_assoc (cm.mul a b) (inverse a) (inverse b) }
    cm.mul (cm.mul (cm.mul a b) (inverse a)) (inverse b);
    (==) { cm.lemma_mul_comm (cm.mul a b) (inverse a) }
    cm.mul (cm.mul (inverse a) (cm.mul a b)) (inverse b);
    (==) { lemma_mul_cancel_inverse k a b }
    cm.mul b (inverse b);
    (==) { cm.lemma_mul_comm b (inverse b) }
    cm.mul (inverse b) b;
    (==) { lemma_inverse b }
    cm.one;
  };

  assert (cm.mul (cm.mul a b) (inverse (cm.mul a b)) ==
    cm.mul (cm.mul a b) (cm.mul (inverse a) (inverse b)));
  lemma_cancellation k (cm.mul a b) (inverse (cm.mul a b))
    (cm.mul (inverse a) (inverse b))

//---------------------

#push-options "--fuel 2"
let lemma_pow0 #t k x = ()

let lemma_pow1 #t k x = lemma_one x

let lemma_pow_unfold #t k x n = ()
#pop-options

let rec lemma_pow_one #t k n =
  if n = 0 then
    lemma_pow0 k one
  else begin
    lemma_pow_unfold k one n;
    //assert (pow k one n == mul one (pow k one (n - 1)));
    lemma_pow_one k (n - 1);
    //assert (pow k one n == mul one one);
    lemma_one k.one;
    () end


let rec lemma_pow_add #t k x n m =
  if n = 0 then begin
    calc (==) {
      mul (pow k x n) (pow k x m);
      (==) { lemma_pow0 k x }
      mul one (pow k x m);
      (==) { lemma_mul_comm one (pow k x m) }
      mul (pow k x m) one;
      (==) { lemma_one (pow k x m) }
      pow k x m;
      }; () end
  else begin
    calc (==) {
      mul (pow k x n) (pow k x m);
      (==) { lemma_pow_unfold k x n }
      mul (mul x (pow k x (n - 1))) (pow k x m);
      (==) { lemma_mul_assoc x (pow k x (n - 1)) (pow k x m) }
      mul x (mul (pow k x (n - 1)) (pow k x m));
      (==) { lemma_pow_add #t k x (n - 1) m }
      mul x (pow k x (n - 1 + m));
      (==) { lemma_pow_unfold k x (n + m) }
      pow k x (n + m);
      }; () end


let rec lemma_pow_mul #t k x n m =
  if m = 0 then begin
    lemma_pow0 k (pow k x n);
    lemma_pow0 k x;
    () end
  else begin
    calc (==) {
      pow k (pow k x n) m;
      (==) { lemma_pow_unfold k (pow k x n) m }
      mul (pow k x n) (pow k (pow k x n) (m - 1));
      (==) { lemma_pow_mul k x n (m - 1) }
      mul (pow k x n) (pow k x (n * (m - 1)));
      (==) { lemma_pow_add k x n (n * (m - 1)) }
      pow k x (n * m);
    }; () end


let rec lemma_pow_mul_base #t k a b n =
  if n = 0 then begin
    lemma_pow0 k a;
    lemma_pow0 k b;
    lemma_one k.one;
    lemma_pow0 k (mul a b) end
  else begin
    calc (==) {
      mul (pow k a n) (pow k b n);
      (==) { lemma_pow_unfold k a n; lemma_pow_unfold k b n }
      mul (mul a (pow k a (n - 1))) (mul b (pow k b (n - 1)));
      (==) { lemma_mul_comm b (pow k b (n - 1));
       lemma_mul_assoc a (pow k a (n - 1)) (mul (pow k b (n - 1)) b) }
      mul a (mul (pow k a (n - 1)) (mul (pow k b (n - 1)) b));
      (==) { lemma_mul_assoc (pow k a (n - 1)) (pow k b (n - 1)) b }
      mul a (mul (mul (pow k a (n - 1)) (pow k b (n - 1))) b);
      (==) { lemma_pow_mul_base #t k a b (n - 1) }
      mul a (mul (pow k (mul a b) (n - 1)) b);
      (==) { lemma_mul_comm (pow k (mul a b) (n - 1)) b;
	lemma_mul_assoc a b (pow k (mul a b) (n - 1)) }
      mul (mul a b) (pow k (mul a b) (n - 1));
      (==) { lemma_pow_unfold k (mul a b) n }
      pow k (mul a b) n;
    }; () end


let lemma_pow_double #t k x b =
  calc (==) {
    pow k (mul x x) b;
    (==) { lemma_pow_mul_base k x x b}
    mul (pow k x b) (pow k x b);
    (==) { lemma_pow_add k x b b }
    pow k x (b + b);
    }


let rec lemma_inverse_pow #t k x n =
  if n = 0 then begin
    lemma_pow0 cm x;
    assert (inverse (pow cm x n) == inverse cm.one);
    lemma_pow0 cm (inverse x);
    assert (pow cm (inverse x) n == cm.one);
    lemma_inverse_one k end
  else begin
    calc (==) {
      k.inverse (pow k.cm x n);
      (==) { lemma_pow_unfold k.cm x n }
      k.inverse (k.cm.mul x (pow k.cm x (n - 1)));
      (==) { lemma_inverse_mul k x (pow k.cm x (n - 1)) }
      k.cm.mul (k.inverse x) (k.inverse (pow k.cm x (n - 1)));
      (==) { lemma_inverse_pow k x (n - 1) }
      k.cm.mul (k.inverse x) (pow k.cm (k.inverse x) (n - 1));
      (==) { lemma_pow_unfold k.cm (inverse x) n }
      pow k.cm (k.inverse x) n;
    } end


let lemma_pow_neg_one #t k n =
  if n >= 0 then lemma_pow_one k.cm n
  else begin
    lemma_pow_one k.cm (- n);
    lemma_inverse_one k end


val lemma_pow_neg_add_aux: #t:Type -> k:abelian_group t -> x:t -> n:int -> m:int -> Lemma
  (requires n < 0 && m >= 0)
  (ensures  cm.mul (pow_neg k x n) (pow_neg k x m) == pow_neg k x (n + m))

let lemma_pow_neg_add_aux #t k x n m =
  assert (cm.mul (pow_neg k x n) (pow_neg k x m) ==
    cm.mul (k.inverse (pow k.cm x (-n))) (pow k.cm x m));

  if -n <= m then begin
  calc (==) {
    k.cm.mul (k.inverse (pow k.cm x (-n))) (pow k.cm x m);
    (==) { lemma_pow_add k.cm x (-n) (m + n) }
    k.cm.mul (k.inverse (pow k.cm x (-n))) (k.cm.mul (pow k.cm x (-n)) (pow k.cm x (m + n)));
    (==) { k.cm.lemma_mul_assoc
      (k.inverse (pow k.cm x (-n))) (pow k.cm x (-n)) (pow k.cm x (m + n)) }
    k.cm.mul (k.cm.mul (k.inverse (pow k.cm x (- n))) (pow k.cm x (-n))) (pow k.cm x (m + n));
    (==) { k.lemma_inverse (pow k.cm x (- n)) }
    k.cm.mul k.cm.one (pow k.cm x (m + n));
    (==) { k.cm.lemma_mul_comm k.cm.one (pow k.cm x (m + n)) }
    k.cm.mul (pow k.cm x (m + n)) k.cm.one;
    (==) { k.cm.lemma_one (pow k.cm x (m + n)) }
    pow k.cm x (m + n);
  } end
  else begin
  calc (==) {
    k.cm.mul (k.inverse (pow k.cm x (-n))) (pow k.cm x m);
    (==) { lemma_pow_add k.cm x (-n-m) m }
    k.cm.mul (k.inverse (k.cm.mul (pow k.cm x (-n-m)) (pow k.cm x m))) (pow k.cm x m);
    (==) { lemma_inverse_mul k (pow k.cm x (-n-m)) (pow k.cm x m) }
    k.cm.mul (k.cm.mul (k.inverse (pow k.cm x (-n-m))) (k.inverse (pow k.cm x m))) (pow k.cm x m);
    (==) { k.cm.lemma_mul_assoc
      (k.inverse (pow k.cm x (-n-m))) (k.inverse (pow k.cm x m)) (pow k.cm x m) }
    k.cm.mul (k.inverse (pow k.cm x (-n-m))) (k.cm.mul (k.inverse (pow k.cm x m)) (pow k.cm x m));
    (==) { k.lemma_inverse (pow k.cm x m) }
    k.cm.mul (k.inverse (pow k.cm x (-n-m))) k.cm.one;
    (==) { k.cm.lemma_one (k.inverse (pow k.cm x (-n-m))) }
    k.inverse (pow k.cm x (-n-m));
  } end


let lemma_pow_neg_add #t k x n m =
  if n >= 0 && m >= 0 then
    lemma_pow_add k.cm x n m
  else begin
    if n < 0 && m < 0 then begin
      calc (==) {
        k.cm.mul (pow_neg k x n) (pow_neg k x m);
        (==) { }
        k.cm.mul (k.inverse (pow k.cm x (- n))) (k.inverse (pow k.cm x (- m)));
        (==) { lemma_inverse_mul k (pow k.cm x (- n)) (pow k.cm x (- m)) }
        k.inverse (k.cm.mul (pow k.cm x (- n)) (pow k.cm x (- m)));
        (==) { lemma_pow_add k.cm x (- n) (- m) }
        k.inverse (pow k.cm x (- n - m));
      } end
    else begin
      if n < 0 && m >= 0 then
        lemma_pow_neg_add_aux k x n m
      else begin
        k.cm.lemma_mul_comm (pow_neg k x n) (pow_neg k x m);
        lemma_pow_neg_add_aux k x m n end
    end
  end


val lemma_pow_neg_mul_mzero: #t:Type -> k:abelian_group t -> x:t -> n:int -> m:int -> Lemma
  (requires n < 0 && m = 0)
  (ensures  pow_neg k (pow_neg k x n) m == pow_neg k x (n * m))

let lemma_pow_neg_mul_mzero #t k x n m =
  assert (pow_neg k (pow_neg k x n) m ==
    pow k.cm (k.inverse (pow k.cm x (-n))) m);
  assert (pow_neg k x (n * m) == pow k.cm x 0);
  lemma_pow0 k.cm x;
  lemma_pow0 k.cm (k.inverse (pow k.cm x (-n)))


val lemma_pow_neg_mul_nzero: #t:Type -> k:abelian_group t -> x:t -> n:int -> m:int -> Lemma
  (requires m < 0 && n = 0)
  (ensures  pow_neg k (pow_neg k x n) m == pow_neg k x (n * m))

let lemma_pow_neg_mul_nzero #t k x n m =
  assert (pow_neg k (pow_neg k x n) m ==
    k.inverse (pow k.cm (pow k.cm x 0) (-m)));
  assert (pow_neg k x (n * m) == pow k.cm x 0);
  lemma_pow0 k.cm x;
  lemma_pow_neg_one #t k m


val lemma_pow_neg_mul_nneg: #t:Type -> k:abelian_group t -> x:t -> n:int -> m:int -> Lemma
  (requires n < 0 && m > 0)
  (ensures  pow_neg k (pow_neg k x n) m == pow_neg k x (n * m))

let lemma_pow_neg_mul_nneg #t k x n m =
  calc (==) {
    pow_neg k (pow_neg k x n) m;
    (==) { }
    pow k.cm (k.inverse (pow k.cm x (-n))) m;
    (==) { lemma_inverse_pow k (pow k.cm x (-n)) m }
    k.inverse (pow k.cm (pow k.cm x (-n)) m);
    (==) { lemma_pow_mul k.cm x (-n) m }
    k.inverse (pow k.cm x (-n * m));
  }


val lemma_pow_neg_mul_mneg: #t:Type -> k:abelian_group t -> x:t -> n:int -> m:int -> Lemma
  (requires n > 0 && m < 0)
  (ensures  pow_neg k (pow_neg k x n) m == pow_neg k x (n * m))

let lemma_pow_neg_mul_mneg #t k x n m =
  calc (==) {
    pow_neg k (pow_neg k x n) m;
    (==) { }
    k.inverse (pow k.cm (pow k.cm x n) (-m));
    (==) { lemma_pow_mul k.cm x n (-m) }
    k.inverse (pow k.cm x (-n * m));
  }


let lemma_pow_neg_mul #t k x n m =
  if n >= 0 && m >= 0 then
    lemma_pow_mul k.cm x n m
  else begin
    if n < 0 && m < 0 then
    calc (==) {
      pow_neg k (pow_neg k x n) m;
      (==) { }
      k.inverse (pow k.cm (k.inverse (pow k.cm x (-n))) (-m));
      (==) { lemma_inverse_pow k (pow k.cm x (-n)) (-m) }
      k.inverse (k.inverse (pow k.cm (pow k.cm x (-n)) (-m)));
      (==) { lemma_inverse_id k (pow k.cm (pow k.cm x (-n)) (-m)) }
      pow k.cm (pow k.cm x (-n)) (-m);
      (==) { lemma_pow_mul k.cm x (-n) (-m) }
      pow k.cm x (n * m);
    }
    else begin
      if n < 0 && m >= 0 then begin
        if m = 0 then lemma_pow_neg_mul_mzero k x n m
        else lemma_pow_neg_mul_nneg k x n m end
      else begin
        if n = 0 then lemma_pow_neg_mul_nzero k x n m
        else lemma_pow_neg_mul_mneg k x n m end
      end
  end


let lemma_pow_neg_mul_base #t k a b n =
  if n >= 0 then lemma_pow_mul_base k.cm a b n
  else begin
    calc (==) {
      k.cm.mul (pow_neg k a n) (pow_neg k b n);
      (==) { }
      k.cm.mul (k.inverse (pow k.cm a (-n))) (k.inverse (pow k.cm b (-n)));
      (==) { lemma_inverse_mul k (pow k.cm a (-n)) (pow k.cm b (-n)) }
      k.inverse (k.cm.mul (pow k.cm a (-n)) (pow k.cm b (-n)));
      (==) { lemma_pow_mul_base k.cm a b (- n) }
      k.inverse (pow k.cm (k.cm.mul a b) (-n));
     } end


let lemma_pow_neg_double #t k x b =
  calc (==) {
    pow_neg k (k.cm.mul x x) b;
    (==) { lemma_pow_neg_mul_base k x x b}
    k.cm.mul (pow_neg k x b) (pow_neg k x b);
    (==) { lemma_pow_neg_add k x b b }
    pow_neg k x (b + b);
  }

//---------------------------

val lemma_b_mod_pow2i: bBits:nat -> b:nat{b < pow2 bBits} -> i:pos{i <= bBits} ->
  Lemma (b % pow2 i == b / pow2 (i - 1) % 2 * pow2 (i - 1) + b % pow2 (i - 1))
let lemma_b_mod_pow2i bBits b i =
  calc (==) {
    b % pow2 i;
    (==) { Math.Lemmas.euclidean_division_definition (b % pow2 i) (pow2 (i - 1)) }
    b % pow2 i / pow2 (i - 1) * pow2 (i - 1) + b % pow2 i % pow2 (i - 1);
    (==) { Math.Lemmas.pow2_modulo_modulo_lemma_1 b (i - 1) i }
    b % pow2 i / pow2 (i - 1) * pow2 (i - 1) + b % pow2 (i - 1);
    (==) { Math.Lemmas.pow2_modulo_division_lemma_1 b (i - 1) i; assert_norm (pow2 1 = 2) }
    b / pow2 (i - 1) % 2 * pow2 (i - 1) + b % pow2 (i - 1);
  }


val lemma_b_div_pow2ki: bBits:nat -> b:nat{b < pow2 bBits} -> k:pos -> i:pos{k * i <= bBits - bBits % k} ->
  Lemma (let bk = bBits - bBits % k in
    b / pow2 (bk - k * (i - 1)) * pow2 k + b / pow2 (bk - k * (i - 1) - k) % pow2 k == b / pow2 (bk - k * i))
let lemma_b_div_pow2ki bBits b k i =
  let bk = bBits - bBits % k in
  let c = b / pow2 (bk - k * i) in
  calc (==) {
    b / pow2 (bk - k * i);
    (==) { Math.Lemmas.euclidean_division_definition c (pow2 k) }
    c / pow2 k * pow2 k + c % pow2 k;
    (==) { Math.Lemmas.division_multiplication_lemma b (pow2 (bk - k * i)) (pow2 k) }
    b / (pow2 (bk - k * i) * pow2 k) * pow2 k + c % pow2 k;
    (==) { Math.Lemmas.pow2_plus (bk - k * i) k }
    b / pow2 (bk - k * i + k) * pow2 k + c % pow2 k;
    (==) { Math.Lemmas.distributivity_sub_right k i 1 }
    b / pow2 (bk - k * (i - 1)) * pow2 k + c % pow2 k;
    }


val lemma_b_div_pow2i: bBits:nat -> b:nat{b < pow2 bBits} -> i:pos{i <= bBits} ->
  Lemma (b / pow2 (bBits - i) == b / pow2 (bBits - i + 1) * 2 + b / pow2 (bBits - i) % 2)
let lemma_b_div_pow2i bBits b i =
  assert_norm (pow2 1 = 2);
  lemma_b_div_pow2ki bBits b 1 i


val exp_rl_lemma_loop:
    #t:Type -> k:comm_monoid t
  -> bBits:nat -> b:nat{b < pow2 bBits}
  -> i:nat{i <= bBits}
  -> a:t ->
  Lemma (let (acc, c) = Loops.repeati i (exp_rl_f k bBits b) (one, a) in
    acc == pow k a (b % pow2 i) /\ c == pow k a (pow2 i))

let rec exp_rl_lemma_loop #t k bBits b i a =
  let (acc, c) = Loops.repeati i (exp_rl_f k bBits b) (one, a) in

  if i = 0 then begin
    Loops.eq_repeati0 i (exp_rl_f k bBits b) (one, a);
    assert_norm (pow2 0 = 1);
    lemma_pow0 k a;
    lemma_pow1 k a;
    () end
  else begin
    let (acc1, c1) = Loops.repeati (i - 1) (exp_rl_f k bBits b) (one, a) in
    Loops.unfold_repeati i (exp_rl_f k bBits b) (one, a) (i - 1);

    exp_rl_lemma_loop #t k bBits b (i - 1) a;
    assert (acc1 == pow k a (b % pow2 (i - 1)) /\ c1 == pow k a (pow2 (i - 1)));

    //assert (c == k.mul c1 c1);
    lemma_pow_add k a (pow2 (i - 1)) (pow2 (i - 1));
    Math.Lemmas.pow2_double_sum (i - 1);
    assert (c == pow k a (pow2 i));

    lemma_b_mod_pow2i bBits b i;
    assert (b % pow2 i == b / pow2 (i - 1) % 2 * pow2 (i - 1) + b % pow2 (i - 1));

    if (b / pow2 (i - 1) % 2 = 1) then begin
      //assert (acc == acc1 * a1);
      assert (acc == mul (pow k a (b % pow2 (i - 1))) (pow k a (pow2 (i - 1))));
      lemma_pow_add k a (b % pow2 (i - 1)) (pow2 (i - 1));
      assert (acc == pow k a (b % pow2 i));
      () end
    else () end


let exp_rl_lemma #t k a bBits b =
  let (acc, c) = Loops.repeati bBits (exp_rl_f k bBits b) (one, a) in
  exp_rl_lemma_loop k bBits b bBits a;
  assert (acc == pow k a (b % pow2 bBits));
  Math.Lemmas.small_mod b (pow2 bBits)


val exp_lr_lemma_step:
   #t:Type -> k:comm_monoid t
  -> a:t -> bBits:nat -> b:nat{b < pow2 bBits}
  -> i:nat{i < bBits}
  -> acc1:t -> Lemma
  (requires acc1 == pow k a (b / pow2 (bBits - i)))
  (ensures  exp_lr_f k a bBits b i acc1 == pow k a (b / pow2 (bBits - i - 1)))

let exp_lr_lemma_step #t k a bBits b i acc1 =
  let acc = exp_lr_f k a bBits b i acc1 in
  lemma_b_div_pow2i bBits b (i + 1);
  assert (b / pow2 (bBits - i - 1) == b / pow2 (bBits - i) * 2 + b / pow2 (bBits - i - 1) % 2);
  lemma_pow_add k a (b / pow2 (bBits - i)) (b / pow2 (bBits - i));
  assert (mul acc1 acc1 == pow k a (b / pow2 (bBits - i) * 2));

  if (b / pow2 (bBits - i - 1) % 2 = 0) then ()
  else begin
    assert (acc == mul (pow k a (b / pow2 (bBits - i) * 2)) a);
    lemma_pow1 k a;
    lemma_pow_add k a (b / pow2 (bBits - i) * 2) 1;
    () end


val exp_lr_lemma_loop:
    #t:Type -> k:comm_monoid t
  -> a:t -> bBits:nat -> b:nat{b < pow2 bBits}
  -> i:nat{i <= bBits} ->
  Lemma (let acc = Loops.repeati i (exp_lr_f k a bBits b) one in
    acc == pow k a (b / pow2 (bBits - i)))

let rec exp_lr_lemma_loop #t k a bBits b i =
  let acc = Loops.repeati i (exp_lr_f k a bBits b) one in
  if i = 0 then begin
    Loops.eq_repeati0 i (exp_lr_f k a bBits b) one;
    lemma_pow0 k a;
    () end
  else begin
    let acc1 = Loops.repeati (i - 1) (exp_lr_f k a bBits b) one in
    Loops.unfold_repeati i (exp_lr_f k a bBits b) one (i - 1);
    //assert (acc == exp_lr_f k a bBits b (i - 1) acc1);
    exp_lr_lemma_loop k a bBits b (i - 1);
    //assert (acc1 == pow k a (b / pow2 (bBits - i + 1)));
    exp_lr_lemma_step #t k a bBits b (i - 1) acc1;
    //assert (acc == pow k a (b / pow2 (bBits - i)));
    () end


let exp_lr_lemma #t k a bBits b =
  let acc = Loops.repeati bBits (exp_lr_f k a bBits b) one in
  exp_lr_lemma_loop #t k a bBits b bBits;
  assert (acc == pow k a (b / pow2 0));
  assert_norm (pow2 0 = 1)


val exp_mont_ladder_lemma_step:
    #t:Type -> k:comm_monoid t
  -> bBits:nat -> b:nat{b < pow2 bBits}
  -> a:t -> r0:t -> r1:t
  -> i:nat{i < bBits} -> Lemma
  (requires
    r1 == mul r0 a /\ r0 == pow k a (b / pow2 (bBits - i)))
  (ensures
   (let (r0', r1') = exp_mont_ladder_f k bBits b i (r0, r1) in
    r1' == mul r0' a /\ r0' == pow k a (b / pow2 (bBits - i - 1))))

let exp_mont_ladder_lemma_step #t k bBits b a r0 r1 i =
  let (r0', r1') = exp_mont_ladder_f k bBits b i (r0, r1) in
  lemma_b_div_pow2i bBits b (i + 1);
  assert (b / pow2 (bBits - i - 1) == b / pow2 (bBits - i) * 2 + b / pow2 (bBits - i - 1) % 2);
  lemma_pow_add k a (b / pow2 (bBits - i)) (b / pow2 (bBits - i));
  assert (mul r0 r0 == pow k a (b / pow2 (bBits - i) * 2));

  if (b / pow2 (bBits - i - 1) % 2 = 0) then begin
    assert (r0' == pow k a (b / pow2 (bBits - i - 1)));
    //assert (r1' == mul r1 r0);
    assert (r1' == mul (mul r0 a) r0);
    lemma_mul_comm r0 a;
    lemma_mul_assoc a r0 r0;
    assert (r1' == mul a r0');
    lemma_mul_comm a r0';
    () end
  else begin
    //assert (r0' == mul r0 r1);
    assert (r0' == mul r0 (mul r0 a));
    lemma_mul_assoc r0 r0 a;
    lemma_pow1 k a;
    lemma_pow_add k a (b / pow2 (bBits - i) * 2) 1;
    assert (r0' == pow k a (b / pow2 (bBits - i - 1)));
    //assert (r1' == mul r1 r1);
    assert (r1' == mul (mul r0 a) (mul r0 a));
    lemma_mul_comm r0 a;
    lemma_mul_assoc a r0 (mul r0 a);
    assert (r1' == mul a r0');
    lemma_mul_comm a r0';
    () end


val exp_mont_ladder_lemma_loop:
    #t:Type -> k:comm_monoid t
  -> bBits:nat -> b:nat{b < pow2 bBits}
  -> a:t -> i:nat{i <= bBits} ->
  Lemma (let (r0, r1) = Loops.repeati i (exp_mont_ladder_f k bBits b) (one, a) in
    r1 == mul r0 a /\ r0 == pow k a (b / pow2 (bBits - i)))

let rec exp_mont_ladder_lemma_loop #t k bBits b a i =
  let (r0, r1) = Loops.repeati i (exp_mont_ladder_f k bBits b) (one, a) in
  if i = 0 then begin
    Loops.eq_repeati0 i (exp_mont_ladder_f k bBits b) (one, a);
    Math.Lemmas.small_div b (pow2 bBits);
    lemma_pow0 k a;
    lemma_one a;
    lemma_mul_comm a one; //mul one r1 == r1
    () end
  else begin
    let (r0', r1') = Loops.repeati (i - 1) (exp_mont_ladder_f k bBits b) (one, a) in
    Loops.unfold_repeati i (exp_mont_ladder_f k bBits b) (one, a) (i - 1);
    exp_mont_ladder_lemma_loop k bBits b a (i - 1);
    exp_mont_ladder_lemma_step #t k bBits b a r0' r1' (i - 1);
    () end


let exp_mont_ladder_lemma # t k a bBits b =
  let (r0, r1) = Loops.repeati bBits (exp_mont_ladder_f k bBits b) (one, a) in
  exp_mont_ladder_lemma_loop #t k bBits b a bBits;
  assert_norm (pow2 0 = 1)


val exp_mont_ladder_swap2_lemma_loop:
    #t:Type -> k:comm_monoid t
  -> a:t -> bBits:nat -> b:nat{b < pow2 bBits}
  -> i:nat{i <= bBits} ->
  Lemma
  (let (r0, r1) = Loops.repeati i (exp_mont_ladder_swap2_f k bBits b) (one, a) in
   let (r3, r4) = Loops.repeati i (exp_mont_ladder_f k bBits b) (one, a) in
   r0 == r3 /\ r1 == r4)

let rec exp_mont_ladder_swap2_lemma_loop #t k a bBits b i =
  if i = 0 then begin
    Loops.eq_repeati0 i (exp_mont_ladder_swap2_f k bBits b) (one, a);
    Loops.eq_repeati0 i (exp_mont_ladder_f k bBits b) (one, a);
    () end
  else begin
    Loops.unfold_repeati i (exp_mont_ladder_swap2_f k bBits b) (one, a) (i - 1);
    Loops.unfold_repeati i (exp_mont_ladder_f k bBits b) (one, a) (i - 1);
    exp_mont_ladder_swap2_lemma_loop k a bBits b (i - 1);
    () end


let exp_mont_ladder_swap2_lemma #t k a bBits b =
  exp_mont_ladder_swap2_lemma_loop #t k a bBits b bBits


val exp_mont_ladder_swap_lemma_loop:
    #t:Type -> k:comm_monoid t
  -> a:t -> bBits:nat -> b:nat{b < pow2 bBits}
  -> sw0:nat{sw0 == b / pow2 bBits % 2}
  -> i:nat{i <= bBits} ->
  Lemma
  (let (r0, r1, sw) = Loops.repeati i (exp_mont_ladder_swap_f k bBits b) (one, a, sw0) in
   let (r3, r4) = Loops.repeati i (exp_mont_ladder_f k bBits b) (cswap sw0 one a) in
   let bit = b / pow2 (bBits - i) % 2 in
   sw == bit /\ cswap bit r0 r1 == (r3, r4))

let rec exp_mont_ladder_swap_lemma_loop #t k a bBits b sw0 i =
  if i = 0 then begin
    Loops.eq_repeati0 i (exp_mont_ladder_swap_f k bBits b) (one, a, sw0);
    Loops.eq_repeati0 i (exp_mont_ladder_f k bBits b) (cswap sw0 one a);
    () end
  else begin
    Loops.unfold_repeati i (exp_mont_ladder_swap_f k bBits b) (one, a, sw0) (i - 1);
    Loops.unfold_repeati i (exp_mont_ladder_f k bBits b) (cswap sw0 one a) (i - 1);
    exp_mont_ladder_swap_lemma_loop k a bBits b sw0 (i - 1);
    () end


let exp_mont_ladder_swap_lemma #t k a bBits b =
  exp_mont_ladder_swap_lemma_loop #t k a bBits b 0 bBits


val exp_pow2_loop_lemma: #t:Type -> k:comm_monoid t -> a:t -> b:nat -> i:nat{i <= b} ->
  Lemma (Loops.repeat i (sqr k) a == pow k a (pow2 i))
let rec exp_pow2_loop_lemma #t k a b i =
  if i = 0 then begin
    Loops.eq_repeat0 (sqr k) a;
    assert_norm (pow2 0 = 1);
    lemma_pow1 k a end
  else begin
    Loops.unfold_repeat b (sqr k) a (i - 1);
    exp_pow2_loop_lemma k a b (i - 1);
    lemma_pow_add k a (pow2 (i - 1)) (pow2 (i - 1));
    Math.Lemmas.pow2_double_sum (i - 1);
    () end

let exp_pow2_lemma #t k a b = exp_pow2_loop_lemma k a b b


val exp_fw_lemma_step:
    #t:Type -> k:comm_monoid t
  -> a:t
  -> bBits:nat -> b:nat{b < pow2 bBits}
  -> l:pos
  -> i:pos{i <= bBits / l}
  -> acc1:t -> Lemma
  (requires
    acc1 == pow k a (b / pow2 (bBits - bBits % l - l * (i - 1))))
  (ensures
    exp_fw_f k a bBits b l (i - 1) acc1 == pow k a (b / pow2 (bBits - bBits % l - l * i)))

let exp_fw_lemma_step #t k a bBits b l i acc1 =
  let bk = bBits - bBits % l in
  let acc = exp_fw_f k a bBits b l (i - 1) acc1 in
  exp_pow2_lemma k acc1 l;
  assert (acc == k.mul (pow k acc1 (pow2 l)) (pow k a (b / pow2 (bk - l * (i - 1) - l) % pow2 l)));

  let r1 = pow k a (b / pow2 (bk - l * (i - 1)) * pow2 l) in
  let r2 = pow k a (b / pow2 (bk - l * (i - 1) - l) % pow2 l) in

  calc (==) {
    mul (pow k acc1 (pow2 l)) r2;
    (==) { }
    mul (pow k (pow k a (b / pow2 (bk - l * (i - 1)))) (pow2 l)) r2;
    (==) { lemma_pow_mul k a (b / pow2 (bk - l * (i - 1))) (pow2 l) }
    mul r1 r2;
    (==) { lemma_pow_add k a (b / pow2 (bk - l * (i - 1)) * pow2 l) (b / pow2 (bk - l * (i - 1) - l) % pow2 l) }
    pow k a (b / pow2 (bk - l * (i - 1)) * pow2 l + b / pow2 (bk - l * (i - 1) - l) % pow2 l);
    (==) { lemma_b_div_pow2ki bBits b l i }
    pow k a (b / pow2 (bk - l * i));
    }


val exp_fw_lemma_loop:
    #t:Type -> k:comm_monoid t
  -> a:t
  -> bBits:nat -> b:nat{b < pow2 bBits}
  -> l:pos
  -> i:nat{i <= bBits / l} ->
  Lemma (
    let bk = bBits - bBits % l in
    let acc0 = pow k a (b / pow2 bk) in
    let acc = Loops.repeati i (exp_fw_f k a bBits b l) acc0 in
    acc == pow k a (b / pow2 (bk - l * i)))

let rec exp_fw_lemma_loop #t k a bBits b l i =
  let bk = bBits - bBits % l in
  let acc0 = pow k a (b / pow2 bk) in
  let acc = Loops.repeati i (exp_fw_f k a bBits b l) acc0 in
  if i = 0 then
    Loops.eq_repeati0 i (exp_fw_f k a bBits b l) acc0
  else begin
    Loops.unfold_repeati i (exp_fw_f k a bBits b l) acc0 (i - 1);
    let acc1 = Loops.repeati (i - 1) (exp_fw_f k a bBits b l) acc0 in
    assert (acc == exp_fw_f k a bBits b l (i - 1) acc1);
    exp_fw_lemma_loop k a bBits b l (i - 1);
    assert (acc1 == pow k a (b / pow2 (bk - l * (i - 1))));
    exp_fw_lemma_step k a bBits b l i acc1;
    assert (acc == pow k a (b / pow2 (bk - l * i)));
    () end


val exp_fw_acc0_lemma: #t:Type -> k:comm_monoid t -> a:t -> bBits:nat -> b:nat{b < pow2 bBits} -> l:pos{bBits % l <> 0} ->
  Lemma (exp_fw_acc0 k a bBits b l == pow k a (b / pow2 (bBits / l * l)))
let exp_fw_acc0_lemma #t k a bBits b l =
  let bits_c = get_ith_lbits bBits b (bBits / l * l) l in
  let acc = pow k a bits_c in
  assert (bits_c == b / pow2 (bBits / l * l) % pow2 l);
  Math.Lemmas.lemma_div_lt_nat b bBits (bBits / l * l);
  assert (b / pow2 (bBits / l * l) < pow2 (bBits % l));
  Math.Lemmas.pow2_lt_compat l (bBits % l);
  Math.Lemmas.small_mod (b / pow2 (bBits / l * l)) (pow2 l);
  assert (bits_c == b / pow2 (bBits / l * l));
  assert (acc == pow k a (b / pow2 (bBits / l * l)));
  ()


val exp_fw_acc0_aux_lemma: #t:Type -> k:comm_monoid t -> a:t -> bBits:nat -> b:nat{b < pow2 bBits} -> l:pos ->
  Lemma (let acc0 = if bBits % l = 0 then one else exp_fw_acc0 k a bBits b l in
    acc0 == pow k a (b / pow2 (bBits / l * l)))
let exp_fw_acc0_aux_lemma #t k a bBits b l =
  if bBits % l = 0 then begin
    let acc = one in
    assert (bBits / l * l == bBits);
    Math.Lemmas.small_div b (pow2 bBits);
    assert (b / pow2 (bBits / l * l) == 0);
    lemma_pow0 k a;
    assert (acc == pow k a (b / pow2 (bBits / l * l)));
    () end
  else
    exp_fw_acc0_lemma #t k a bBits b l


let exp_fw_lemma #t k a bBits b l =
  let bk = bBits - bBits % l in
  let acc0 = if bBits % l = 0 then one else exp_fw_acc0 k a bBits b l in
  exp_fw_acc0_aux_lemma k a bBits b l;
  assert (acc0 == pow k a (b / pow2 bk));

  let res = Loops.repeati (bBits / l) (exp_fw_f k a bBits b l) acc0 in
  exp_fw_lemma_loop k a bBits b l (bBits / l);
  //assert (res == pow k a (b / pow2 (bk - l * (bBits / l))));
  //assert (res == pow k a (b / pow2 0));
  assert_norm (pow2 0 = 1)


val exp_double_fw_lemma_step:
    #t:Type -> k:comm_monoid t
  -> a1:t -> bBits:nat -> b1:nat{b1 < pow2 bBits}
  -> a2:t -> b2:nat{b2 < pow2 bBits}
  -> l:pos
  -> i:pos{i <= bBits / l}
  -> acc:t -> Lemma
  (requires
   (let bk = bBits - bBits % l in
    acc == mul (pow k a1 (b1 / pow2 (bk - l * (i - 1)))) (pow k a2 (b2 / pow2 (bk - l * (i - 1))))))
  (ensures
   (let bk = bBits - bBits % l in
    exp_double_fw_f k a1 bBits b1 a2 b2 l (i - 1) acc ==
    mul (pow k a1 (b1 / pow2 (bk - l * i))) (pow k a2 (b2 / pow2 (bk - l * i)))))

let exp_double_fw_lemma_step #t k a1 bBits b1 a2 b2 l i acc =
  let bk = bBits - bBits % l in
  let acc1 = exp_pow2 k acc l in
  let r11 = b1 / pow2 (bk - l * (i - 1)) in
  let r12 = b1 / pow2 (bk - l * (i - 1) - l) % pow2 l in
  let r21 = b2 / pow2 (bk - l * (i - 1)) in
  let r22 = b2 / pow2 (bk - l * (i - 1) - l) % pow2 l in

  calc (==) {
    k.mul acc1 (pow k a1 r12);
    (==) { exp_pow2_lemma k acc l }
    k.mul (pow k acc (pow2 l)) (pow k a1 r12);
    (==) { }
    k.mul (pow k (k.mul (pow k a1 r11) (pow k a2 r21)) (pow2 l)) (pow k a1 r12);
    (==) { lemma_pow_mul_base k (pow k a1 r11) (pow k a2 r21) (pow2 l) }
    k.mul (k.mul (pow k (pow k a1 r11) (pow2 l)) (pow k (pow k a2 r21) (pow2 l))) (pow k a1 r12);
    (==) { lemma_pow_mul k a1 r11 (pow2 l) }
    k.mul (k.mul (pow k a1 (r11 * pow2 l)) (pow k (pow k a2 r21) (pow2 l))) (pow k a1 r12);
    (==) { lemma_pow_mul k a2 r21 (pow2 l) }
    k.mul (k.mul (pow k a1 (r11 * pow2 l)) (pow k a2 (r21 * pow2 l))) (pow k a1 r12);
    (==) {
      k.lemma_mul_assoc (pow k a1 (r11 * pow2 l)) (pow k a2 (r21 * pow2 l)) (pow k a1 r12);
      k.lemma_mul_comm (pow k a2 (r21 * pow2 l)) (pow k a1 r12);
      k.lemma_mul_assoc (pow k a1 (r11 * pow2 l)) (pow k a1 r12) (pow k a2 (r21 * pow2 l)) }
    k.mul (k.mul (pow k a1 (r11 * pow2 l)) (pow k a1 r12)) (pow k a2 (r21 * pow2 l));
    (==) { lemma_pow_add k a1 (r11 * pow2 l) r12 }
    k.mul (pow k a1 (r11 * pow2 l + r12)) (pow k a2 (r21 * pow2 l));
    (==) { lemma_b_div_pow2ki bBits b1 l i }
    k.mul (pow k a1 (b1 / pow2 (bk - l * i))) (pow k a2 (r21 * pow2 l));
    };

  calc (==) {
    k.mul (k.mul acc1 (pow k a1 r12)) (pow k a2 r22);
    (==) { }
    k.mul (k.mul (pow k a1 (b1 / pow2 (bk - l * i))) (pow k a2 (r21 * pow2 l))) (pow k a2 r22);
    (==) { k.lemma_mul_assoc (pow k a1 (b1 / pow2 (bk - l * i))) (pow k a2 (r21 * pow2 l)) (pow k a2 r22)}
    k.mul (pow k a1 (b1 / pow2 (bk - l * i))) (k.mul (pow k a2 (r21 * pow2 l)) (pow k a2 r22));
    (==) { lemma_pow_add k a2 (r21 * pow2 l) r22 }
    k.mul (pow k a1 (b1 / pow2 (bk - l * i))) (pow k a2 (r21 * pow2 l + r22));
    (==) { lemma_b_div_pow2ki bBits b2 l i }
    k.mul (pow k a1 (b1 / pow2 (bk - l * i))) (pow k a2 (b2 / pow2 (bk - l * i)));
    }


val exp_double_fw_lemma_loop:
    #t:Type -> k:comm_monoid t
  -> a1:t -> bBits:nat -> b1:nat{b1 < pow2 bBits}
  -> a2:t -> b2:nat{b2 < pow2 bBits}
  -> l:pos
  -> i:nat{i <= bBits / l} ->
  Lemma (
    let bk = bBits - bBits % l in
    let acc0 = mul (pow k a1 (b1 / pow2 bk)) (pow k a2 (b2 / pow2 bk)) in
    let acc = Loops.repeati i (exp_double_fw_f k a1 bBits b1 a2 b2 l) acc0 in
    acc == mul (pow k a1 (b1 / pow2 (bk - l * i))) (pow k a2 (b2 / pow2 (bk - l * i))))

let rec exp_double_fw_lemma_loop #t k a1 bBits b1 a2 b2 l i =
  let bk = bBits - bBits % l in
  let acc0 = mul (pow k a1 (b1 / pow2 bk)) (pow k a2 (b2 / pow2 bk)) in
  let acc = Loops.repeati i (exp_double_fw_f k a1 bBits b1 a2 b2 l) acc0 in

  if i = 0 then
    Loops.eq_repeati0 i (exp_double_fw_f k a1 bBits b1 a2 b2 l) acc0
  else begin
    Loops.unfold_repeati i (exp_double_fw_f k a1 bBits b1 a2 b2 l) acc0 (i - 1);
    let acc1 = Loops.repeati (i - 1) (exp_double_fw_f k a1 bBits b1 a2 b2 l) acc0 in
    exp_double_fw_lemma_loop k a1 bBits b1 a2 b2 l (i - 1);
    exp_double_fw_lemma_step k a1 bBits b1 a2 b2 l i acc1;
    () end


val exp_double_fw_acc0_lemma: #t:Type -> k:comm_monoid t
  -> a1:t -> bBits:nat -> b1:nat{b1 < pow2 bBits}
  -> a2:t -> b2:nat{b2 < pow2 bBits} -> l:pos ->
  Lemma (let acc0 = if bBits % l = 0 then one else exp_double_fw_acc0 k a1 bBits b1 a2 b2 l in
    let bk = bBits - bBits % l in
    acc0 == mul (pow k a1 (b1 / pow2 bk)) (pow k a2 (b2 / pow2 bk)))

let exp_double_fw_acc0_lemma #t k a1 bBits b1 a2 b2 l =
  let bk = bBits - bBits % l in
  if bBits % l = 0 then begin
    let acc = one in
    assert (bBits / l * l == bBits);
    Math.Lemmas.small_div b1 (pow2 bBits);
    assert (b1 / pow2 (bBits / l * l) == 0);
    assert (b2 / pow2 (bBits / l * l) == 0);
    lemma_pow0 k a1;
    lemma_pow0 k a2;
    lemma_one k.one;
    assert (acc == mul (pow k a1 (b1 / pow2 bk)) (pow k a2 (b2 / pow2 bk)));
    () end
  else begin
    exp_fw_acc0_lemma #t k a1 bBits b1 l;
    exp_fw_acc0_lemma #t k a2 bBits b2 l end


let exp_double_fw_lemma #t k a1 bBits b1 a2 b2 l =
  let bk = bBits - bBits % l in
  let acc0 = if bBits % l = 0 then one else exp_double_fw_acc0 k a1 bBits b1 a2 b2 l in
  exp_double_fw_acc0_lemma #t k a1 bBits b1 a2 b2 l;
  assert (acc0 == mul (pow k a1 (b1 / pow2 bk)) (pow k a2 (b2 / pow2 bk)));

  let res = Loops.repeati (bBits / l) (exp_double_fw_f k a1 bBits b1 a2 b2 l) acc0 in
  exp_double_fw_lemma_loop k a1 bBits b1 a2 b2 l (bBits / l);
  //assert (res == mul (pow k a1 (b1 / pow2 (bk - l * (bBits / l)))) (pow k a2 (b2 / pow2 (bk - l * (bBits / l)))));
  //assert (res == mul (pow k a1 (b1 / pow2 0)) (pow k a2 (b2 / pow2 0)));
  assert_norm (pow2 0 = 1)
  //assert (res == mul (pow k a1 b1) (pow k a2 b2))
