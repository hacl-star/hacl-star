module Hacl.Spec.Bignum.Lib

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Definitions

module Loops = Lib.LoopCombinators


#set-options "--z3rlimit 50 --fuel 0 --ifuel 0 --z3cliopt smt.arith.nl=false"

///
///  Get and set i-th bit of a bignum
///

val limb_get_ith_bit: #t:limb_t -> a:limb t -> i:nat{i < bits t} -> limb t
let limb_get_ith_bit #t a i = (a >>. size i) &. uint #t 1

val limb_get_ith_bit_lemma: #t:limb_t -> a:limb t -> i:nat{i < bits t} ->
  Lemma (v (limb_get_ith_bit a i) == v a / pow2 i % 2)

let limb_get_ith_bit_lemma #t a i =
  let tmp1 = a >>. size i in
  let tmp2 = tmp1 &. uint #t 1 in
  calc (==) {
    v (limb_get_ith_bit a i);
    == { }
    v tmp2;
    == {
      shift_left_lemma #t #SEC (mk_int 1) 1ul;
      assert_norm (1 * pow2 1 == 2);
      FStar.Math.Lemmas.small_mod 2 (modulus t);
      sub_lemma (shift_left #t #SEC (mk_int 1) 1ul) (mk_int 1);
      assert (mod_mask #t #SEC 1ul == uint #t #SEC 1)
    }
    v (tmp1 `logand` mod_mask 1ul);
    == { mod_mask_lemma tmp1 1ul }
    v tmp1 % pow2 (v 1ul);
    == { }
    v a / pow2 i % 2;
  }

val bn_get_ith_bit: #t:limb_t -> #len:size_nat -> b:lbignum t len -> i:size_nat{i / bits t < len} -> limb t
let bn_get_ith_bit #t #len input ind =
  let i = ind / bits t in
  let j = ind % bits t in
  limb_get_ith_bit input.[i] j


val bn_get_ith_bit_aux_lemma: #t:limb_t -> #len:size_nat -> b:lbignum t len -> ind:size_nat{ind / bits t < len} ->
  Lemma (let i = ind / bits t in let j = ind % bits t in
    v (b.[i] >>. size j) == (bn_v b / pow2 ind) % pow2 (bits t - j))

let bn_get_ith_bit_aux_lemma #t #len b ind =
  let pbits = bits t in
  let i = ind / pbits in
  let j = ind % pbits in
  let res = b.[i] >>. size j in

  Math.Lemmas.nat_times_nat_is_nat pbits i;
  Math.Lemmas.pos_times_pos_is_pos (pow2 (pbits * i)) (pow2 j);
  Math.Lemmas.nat_over_pos_is_nat (bn_v b) (pow2 (pbits * i));

  calc (==) {
    v b.[i] / pow2 j;
    == { bn_eval_index b i }
    (bn_v b / pow2 (pbits * i) % pow2 pbits) / pow2 j;
    == { Math.Lemmas.pow2_modulo_division_lemma_1 (bn_v b / pow2 (pbits * i)) j pbits }
    (bn_v b / pow2 (pbits * i) / pow2 j) % pow2 (pbits - j);
    == { Math.Lemmas.division_multiplication_lemma (bn_v b) (pow2 (pbits * i)) (pow2 j) }
    (bn_v b / (pow2 (pbits * i) * pow2 j)) % pow2 (pbits - j);
    == { Math.Lemmas.pow2_plus (pbits * i) j }
    (bn_v b / pow2 (pbits * i + j)) % pow2 (pbits - j);
    == {
      Math.Lemmas.euclidean_division_definition ind pbits;
      Math.Lemmas.euclidean_div_axiom ind pbits }
    (bn_v b / pow2 ind) % pow2 (pbits - j);
    };

  assert (v res == (bn_v b / pow2 ind) % pow2 (pbits - j))


val bn_get_ith_bit_lemma: #t:limb_t -> #len:size_nat -> b:lbignum t len -> i:size_nat{i / bits t < len} ->
  Lemma (v (bn_get_ith_bit b i) == (bn_v b / pow2 i % 2))

let bn_get_ith_bit_lemma #t #len b ind =
  let pbits = bits t in
  let i = ind / pbits in
  let j = ind % pbits in
  let res = limb_get_ith_bit b.[i] j in
  limb_get_ith_bit_lemma b.[i] j;

  calc (==) {
    v b.[i] / pow2 j % 2;
    == { bn_get_ith_bit_aux_lemma b ind }
    (bn_v b / pow2 ind) % pow2 (pbits - j) % 2;
    == { assert_norm (pow2 1 = 2);
           Math.Lemmas.pow2_modulo_modulo_lemma_1 (bn_v b / pow2 ind) 1 (pbits - j) }
    (bn_v b / pow2 ind) % 2;
    };
  assert (v res == bn_v b / pow2 ind % 2)


val bn_set_ith_bit: #t:limb_t -> #len:size_nat -> b:lbignum t len -> i:size_nat{i / bits t < len} -> lbignum t len
let bn_set_ith_bit #t #len input ind =
  let i = ind / bits t in
  let j = ind % bits t in
  Math.Lemmas.nat_over_pos_is_nat ind (bits t);
  let inp = input.[i] <- input.[i] |. (uint #t 1 <<. size j) in
  inp


val bn_set_ith_bit_lemma_aux: a:nat -> b:nat -> c:nat -> d:nat -> Lemma
  (requires a + b * pow2 c < pow2 (c + d) /\ a < pow2 c)
  (ensures  b < pow2 d)

let bn_set_ith_bit_lemma_aux a b c d =
  Math.Lemmas.lemma_div_lt_nat (a + b * pow2 c) (c + d) c;
  assert ((a + b * pow2 c) / pow2 c < pow2 d);
  Math.Lemmas.lemma_div_plus a b (pow2 c);
  assert (a / pow2 c + b < pow2 d);
  Math.Lemmas.small_division_lemma_1 a (pow2 c)


val bn_lt_pow2_index_lemma: #t:limb_t -> #len:size_nat -> b:lbignum t len -> ind:size_nat{ind / bits t < len} -> Lemma
  (requires bn_v b < pow2 ind)
  (ensures (let i = ind / bits t in v b.[i] < pow2 (ind % bits t) /\
    (Math.Lemmas.nat_times_nat_is_nat i (bits t);
    bn_v b == bn_v (slice b 0 i) + pow2 (i * bits t) * v b.[i] /\
    bn_v (slice b (i + 1) len) = 0)))

let bn_lt_pow2_index_lemma #t #len b ind =
  let pbits = bits t in
  let i = ind / pbits in
  let j = ind % pbits in

  Math.Lemmas.euclidean_division_definition ind (pbits);
  assert (bn_v b < pow2 (i * pbits + j));
  Math.Lemmas.pow2_lt_compat (i * pbits + pbits) (i * pbits + j);
  assert (bn_v b < pow2 (i * pbits + pbits));
  calc (==) {
    i * pbits + pbits;
    == { }
    i * pbits + 1 * pbits;
    == {
      Math.Lemmas.distributivity_add_left i 1 pbits;
      Math.Lemmas.swap_mul pbits (i+1)
    }
    pbits * (i + 1);
  };

  Math.Lemmas.nat_over_pos_is_nat ind pbits;
  Math.Lemmas.nat_times_nat_is_nat pbits (i+1);
  bn_eval_split_i #t #len b (i + 1);
  bn_eval_bound (slice b 0 (i + 1)) (i + 1);
  Math.Lemmas.swap_mul (pow2 (pbits * (i + 1))) (bn_v (slice b (i+1) len));
  bn_set_ith_bit_lemma_aux (bn_v (slice b 0 (i + 1))) (bn_v (slice b (i + 1) len)) (pbits * (i + 1)) 0;
  assert (bn_v b == bn_v (slice b 0 (i + 1)));

  Math.Lemmas.nat_times_nat_is_nat pbits i;

  bn_eval_split_i #t #(i + 1) (slice b 0 (i + 1)) i;
  bn_eval1 (slice b i (i + 1));
  assert (bn_v b == bn_v (slice b 0 i) + pow2 (i * pbits) * v b.[i]);
  bn_eval_bound #t #i (slice b 0 i) i;

  Math.Lemmas.swap_mul (pow2 (i * pbits)) (v b.[i]);
  bn_set_ith_bit_lemma_aux (bn_v (slice b 0 i)) (v b.[i]) (i * pbits) j;
  assert (v b.[i] < pow2 j)


val bn_set_ith_bit_lemma: #t:limb_t -> #len:size_nat -> b:lbignum t len -> i:size_nat{i / bits t < len} -> Lemma
  (requires bn_v b < pow2 i)
  (ensures  bn_v (bn_set_ith_bit b i) == bn_v b + pow2 i)

let bn_set_ith_bit_lemma #t #len input ind =
  let pbits = bits t in
  let i = ind / pbits in
  let j = ind % pbits in
  bn_lt_pow2_index_lemma #t #len input ind;
  Math.Lemmas.nat_over_pos_is_nat ind pbits;
  assert (v input.[i] < pow2 j);

  let b = uint #t 1 <<. size j in
  let inp = input.[i] <- input.[i] |. b in
  FStar.Math.Lemmas.pow2_lt_compat pbits j;
  FStar.Math.Lemmas.modulo_lemma (pow2 j) (pow2 pbits);
  shift_left_lemma #t #SEC (uint #t 1) (size j);
  Math.Lemmas.mul_one_left_is_same (pow2 j);
  Math.Lemmas.small_mod (pow2 j) (modulus t);
  assert (v b == pow2 j);
  logor_disjoint (input.[i]) b j;
  assert (v inp.[i] == v input.[i] + v b);

  Math.Lemmas.nat_times_nat_is_nat i pbits;

  calc (==) {
    bn_v inp <: int;
    == {
      bn_eval_split_i #t #len inp (i + 1);
      bn_eval_split_i #t #len input (i + 1);
      bn_eval_extensionality_j (slice inp (i + 1) len) (slice input (i + 1) len) (len - i - 1)
    }
    bn_v (slice inp 0 (i + 1));
    == { bn_eval_split_i #t #(i + 1) (slice inp 0 (i + 1)) i }
    bn_v (slice inp 0 i) + pow2 (i * pbits) * bn_v (slice inp i (i + 1));
    == { bn_eval1 (slice inp i (i + 1)) }
    bn_v (slice inp 0 i) + pow2 (i * pbits) * v inp.[i];
    == { bn_eval_extensionality_j input inp i }
    bn_v (slice input 0 i) + pow2 (i * pbits) * v inp.[i];
    == { }
    bn_v (slice input 0 i) + pow2 (i * pbits) * (v input.[i] + v b);
    == { Math.Lemmas.distributivity_add_right (pow2 (i * pbits)) (v input.[i]) (v b) }
    bn_v (slice input 0 i) + pow2 (i * pbits) * v input.[i] + pow2 (i * pbits) * v b;
    == { Math.Lemmas.pow2_plus (i * pbits) j; Math.Lemmas.euclidean_division_definition ind pbits }
    bn_v (slice input 0 i) + pow2 (i * pbits) * v input.[i] + pow2 ind;
    == { }
    bn_v input + pow2 ind;
  }


///
///  % pow2 and / pow2
///

val bn_div_pow2: #t:limb_t -> #len:size_nat -> b:lbignum t len -> i:size_nat{i <= len} -> lbignum t (len - i)
let bn_div_pow2 #t #len b i =
  slice b i len


val bn_div_pow2_lemma: #t:limb_t -> #len:size_nat -> b:lbignum t len -> i:size_nat{i < len} ->
  Lemma (
    Math.Lemmas.nat_times_nat_is_nat (bits t) i;
    bn_v (bn_div_pow2 b i) == bn_v b / pow2 (bits t * i))
let bn_div_pow2_lemma #t #len c i =
  let pbits = bits t in
  Math.Lemmas.nat_times_nat_is_nat pbits i;
  calc (==) {
    bn_v c / pow2 (pbits * i);
    == { bn_eval_split_i c i }
    (bn_v (slice c 0 i) + pow2 (pbits * i) * bn_v (slice c i len)) / pow2 (pbits * i);
    == { Math.Lemmas.division_addition_lemma (bn_v (slice c 0 i)) (pow2 (pbits * i)) (bn_v (slice c i len)) }
    bn_v (slice c 0 i) / pow2 (pbits * i) + bn_v (slice c i len);
    == { bn_eval_bound (slice c 0 i) i; Math.Lemmas.small_division_lemma_1 (bn_v (slice c 0 i)) (pow2 (pbits * i)) }
    bn_v (slice c i len);
  };
  assert (bn_v (slice c i len) == bn_v c / pow2 (pbits * i))


val bn_mod_pow2: #t:limb_t -> #aLen:size_nat -> a:lbignum t aLen -> i:nat{i <= aLen} -> lbignum t i
let bn_mod_pow2 #t #aLen a i = sub a 0 i

val bn_mod_pow2_lemma: #t:limb_t -> #aLen:size_nat -> a:lbignum t aLen -> i:nat{i <= aLen} ->
  Lemma (
    Math.Lemmas.nat_times_nat_is_nat (bits t) i;
    bn_v (bn_mod_pow2 a i) == bn_v a % pow2 (bits t * i))
let bn_mod_pow2_lemma #t #aLen a i =
  let pbits = bits t in
  Math.Lemmas.nat_times_nat_is_nat pbits i;
  calc (==) {
    bn_v a % pow2 (pbits * i);
    == { bn_eval_split_i a i }
    (bn_v (slice a 0 i) + pow2 (pbits * i) * bn_v (slice a i aLen)) % pow2 (pbits * i);
    == { Math.Lemmas.modulo_addition_lemma (bn_v (slice a 0 i)) (pow2 (pbits * i)) (bn_v (slice a i aLen)) }
    (bn_v (slice a 0 i)) % pow2 (pbits * i);
    == { bn_eval_bound (slice a 0 i) i; Math.Lemmas.small_mod (bn_v (slice a 0 i)) (pow2 (pbits * i)) }
    bn_v (slice a 0 i);
    }

///
///  Conditional swap
///

//the same as in curve25519
val lemma_cswap2_step:
   #t:limb_t
  -> bit:limb t{v bit <= 1}
  -> p1:limb t
  -> p2:limb t ->
  Lemma
   (let mask = uint #t 0 -. bit in
    let dummy = mask &. (p1 ^. p2) in
    let p1' = p1 ^. dummy in
    let p2' = p2 ^. dummy in
    if v bit = 1 then p1' == p2 /\ p2' == p1 else p1' == p1 /\ p2' == p2)

let lemma_cswap2_step #t bit p1 p2 =
  let mask = uint #t 0 -. bit in
  assert (v mask == (- (v bit)) @%. t);
  Math.Lemmas.small_mod 0 (modulus t);
  assert (v bit == 0 ==> v mask == 0);
  Math.Lemmas.lemma_mod_sub_0 (modulus t);
  assert (v bit == 1 ==> v mask == pow2 (bits t) - 1);
  let dummy = mask &. (p1 ^. p2) in
  logand_lemma mask (p1 ^. p2);
  assert (v bit == 1 ==> v dummy == v (p1 ^. p2));
  assert (v bit == 0 ==> v dummy == 0);
  let p1' = p1 ^. dummy in
  assert (v dummy == v (if v bit = 1 then (p1 ^. p2) else uint #t 0));
  logxor_lemma p1 p2;
  let p2' = p2 ^. dummy in
  logxor_lemma p2 p1


val cswap2_f:
    #t:limb_t
  -> #len:size_nat
  -> mask:limb t
  -> i:nat{i < len}
  -> tuple2 (lbignum t len) (lbignum t len) ->
  tuple2 (lbignum t len) (lbignum t len)

let cswap2_f #t #len mask i (p1, p2) =
  let dummy = mask &. (p1.[i] ^. p2.[i]) in
  let p1 = p1.[i] <- p1.[i] ^. dummy in
  let p2 = p2.[i] <- p2.[i] ^. dummy in
  (p1, p2)


val cswap2:
    #t:limb_t
  -> #len:size_nat
  -> bit:limb t
  -> b1:lbignum t len
  -> b2:lbignum t len ->
  tuple2 (lbignum t len) (lbignum t len)

let cswap2 #t #len bit b1 b2 =
  let mask = uint #t 0 -. bit in
  Loops.repeati len (cswap2_f #t #len mask) (b1, b2)


val cswap2_lemma:
    #t:limb_t
  -> #len:size_nat
  -> bit:limb t{v bit <= 1}
  -> b1:lbignum t len
  -> b2:lbignum t len ->
  Lemma (let (p1, p2) = cswap2 bit b1 b2 in
    (if v bit = 1 then p1 == b2 /\ p2 == b1 else p1 == b1 /\ p2 == b2))

let cswap2_lemma #t #len bit b1 b2 =
  let mask = uint #t 0 -. bit in
  Loops.eq_repeati0 len (cswap2_f #t #len mask) (b1, b2);
  let (p1, p2) =
  Loops.repeati_inductive #(tuple2 (lbignum t len) (lbignum t len)) len
  (fun i (p1, p2) ->
    (p1, p2) == Loops.repeati i (cswap2_f #t #len mask) (b1, b2) /\
    (forall (k:nat{k < i}).
      (if v bit = 1 then p1.[k] == b2.[k] /\ p2.[k] == b1.[k] else p1.[k] == b1.[k] /\ p2.[k] == b2.[k])) /\
    (forall (k:nat{i <= k /\ k < len}). p1.[k] == b1.[k] /\ p2.[k] == b2.[k]))
  (fun i (p1, p2) ->
    Loops.unfold_repeati (i + 1) (cswap2_f #t #len mask) (b1, b2) i;
    lemma_cswap2_step bit p1.[i] p2.[i];
    cswap2_f #t #len mask i (p1, p2)) (b1, b2) in

  assert (if v bit = 1 then (eq_intro p1 b2; p1 == b2) else (eq_intro p1 b1; p1 == b1));
  assert (if v bit = 1 then (eq_intro p2 b1; p2 == b1) else (eq_intro p2 b2; p2 == b2));
  //eq_intro p1 (if v bit = 1 then b2 else b1);
  //eq_intro p2 (if v bit = 1 then b1 else b2);
  ()


let bn_get_top_index_t (len:size_nat) (i:nat{i <= len}) = x:nat{x < len}

val bn_get_top_index_f:
    #t:limb_t
  -> #len:size_nat
  -> b:lbignum t len
  -> i:nat{i < len}
  -> priv:bn_get_top_index_t len i ->
  bn_get_top_index_t len (i + 1)

let bn_get_top_index_f #t #len b i priv =
  let mask = eq_mask b.[i] (zeros t SEC) in
  if v mask = 0 then i else priv

val bn_get_top_index: #t:limb_t -> #len:size_pos -> b:lbignum t len -> res:size_nat{res < len}
let bn_get_top_index #t #len b =
  Loops.repeat_gen len (bn_get_top_index_t len) (bn_get_top_index_f #t #len b) 0


val bn_get_top_index_lemma: #t:limb_t -> #len:size_pos -> b:lbignum t len ->
  Lemma (let ind = bn_get_top_index #t #len b in
    ind < len /\ (ind > 0 ==> v b.[ind] <> 0) /\ (forall (k:nat{ind < k /\ k < len}). v b.[k] = 0))

let bn_get_top_index_lemma #t #len b =
  Loops.eq_repeat_gen0 len (bn_get_top_index_t len) (bn_get_top_index_f #t #len b) 0;
  let res =
  Loops.repeati_inductive #size_nat len
  (fun i priv ->
    priv == Loops.repeat_gen i (bn_get_top_index_t len) (bn_get_top_index_f #t #len b) 0 /\
    priv < len /\ (priv > 0 ==> v b.[priv] <> 0) /\ (forall (k:nat{priv < k /\ k < i}). v b.[k] = 0))
  (fun i priv ->
    Loops.unfold_repeat_gen (i + 1) (bn_get_top_index_t len) (bn_get_top_index_f #t #len b) 0 i;
    let mask = eq_mask b.[i] (zeros t SEC) in
    eq_mask_lemma b.[i] (zeros t SEC);
    assert (if v mask = 0 then v b.[i] <> 0 else v b.[i] = 0);
    let res = if v mask = 0 then i else priv in
    res) 0 in
  ()


val bn_get_top_index_eval_lemma: #t:limb_t -> #len:size_pos -> b:lbignum t len -> ind:nat -> Lemma
  (requires
    ind < len /\ (ind > 0 ==> v b.[ind] <> 0) /\ (forall (k:nat{ind < k /\ k < len}). v b.[k] = 0))
  (ensures (
    Math.Lemmas.nat_times_nat_is_nat (bits t) ind;
    bn_v b == bn_v (slice b 0 ind) + pow2 (bits t * ind) * v b.[ind]))

let bn_get_top_index_eval_lemma #t #len b ind =
  let pbits = bits t in
  assert (forall (k:nat{ind < k /\ k < len}). v b.[k] = 0);
  bn_eval_split_i b (ind + 1);
  Math.Lemmas.nat_times_nat_is_nat pbits (ind + 1);
  assert (bn_v b == bn_v (slice b 0 (ind + 1)) + pow2 (pbits * (ind + 1)) * bn_v (slice b (ind + 1) len));
  eq_intro (slice b (ind + 1) len) (create (len - ind - 1) (uint #t 0));
  bn_eval_zeroes #t (len - ind - 1) (len - ind - 1);
  Math.Lemmas.mul_zero_right_is_zero (pow2 (pbits * (ind + 1)));
  assert (bn_v b == bn_v (slice b 0 (ind + 1)));
  bn_eval_split_i (slice b 0 (ind + 1)) ind;
  Math.Lemmas.nat_times_nat_is_nat pbits ind;
  assert (bn_v b == bn_v (slice b 0 ind) + pow2 (pbits * ind) * bn_v (slice b ind (ind + 1)));
  bn_eval1 (slice b ind (ind + 1));
  assert (bn_v b == bn_v (slice b 0 ind) + pow2 (pbits * ind) * v b.[ind])


val bn_low_bound_bits:
    #t:limb_t
  -> #len:size_pos{bits t * len <= max_size_t}
  -> b:lbignum t len ->
  res:size_nat{res / bits t < len}

let bn_low_bound_bits #t #len b =
  Math.Lemmas.nat_times_nat_is_nat (bits t) (bn_get_top_index b);
  Math.Lemmas.swap_mul (bits t) (bn_get_top_index b);
  Math.Lemmas.cancel_mul_div (bn_get_top_index b) (bits t);
  Math.Lemmas.lemma_mult_le_left (bits t) (bn_get_top_index b) len;
  bits t * bn_get_top_index b

val bn_low_bound_bits_lemma: #t:limb_t -> #len:size_pos -> b:lbignum t len -> Lemma
  (requires 1 < bn_v b /\ bits t * len <= max_size_t /\ bn_v b % 2 = 1)
  (ensures  pow2 (bn_low_bound_bits b) < bn_v b)

let bn_low_bound_bits_lemma #t #len b =
  let ind = bn_get_top_index #t #len b in
  let low = bn_low_bound_bits b in
  bn_get_top_index_lemma #t #len b;
  bn_get_top_index_eval_lemma #t #len b ind;
  if ind = 0 then (
    Math.Lemmas.mul_zero_right_is_zero (bits t);
    assert_norm (pow2 0 = 1)
  ) else (
    Math.Lemmas.lemma_mult_le_left (pow2 low) 1 (v b.[ind]);
    Math.Lemmas.pos_times_pos_is_pos (bits t) ind;
    Math.Lemmas.pow2_multiplication_modulo_lemma_1 1 1 (bn_low_bound_bits b)
  )


val bn_get_bits_limb:
    #t:limb_t
  -> #nLen:size_nat
  -> n:lbignum t nLen
  -> ind:size_nat{ind / bits t < nLen} ->
  limb t

let bn_get_bits_limb #t #nLen n ind =
  let i = ind / bits t in
  let j = ind % bits t in
  let p1 = n.[i] >>. size j in
  let p2 = if i + 1 < nLen && 0 < j then p1 |. (n.[i + 1] <<. (size (bits t - j))) else p1 in
  p2


val bn_get_bits_limb_aux_lemma:
    #t:limb_t
  -> #nLen:size_nat
  -> n:lbignum t nLen
  -> ind:size_nat{ind / bits t < nLen} ->
  Lemma (
    let pbits = bits t in
    let i = ind / pbits in
    let j = ind % pbits in
    let p1 = n.[i] >>. size j in
    Math.Lemmas.nat_times_nat_is_nat (i+1) pbits;
    bn_v n / pow2 ind % pow2 pbits == bn_v n / pow2 ((i + 1) * pbits) % pow2 pbits * pow2 (pbits - j) % pow2 pbits + v p1)

let bn_get_bits_limb_aux_lemma #t #nLen n ind =
  let pbits = bits t in
  let i = ind / pbits in
  let j = ind % pbits in
  let p1 = n.[i] >>. size j in
  let res = bn_v n / pow2 ind % pow2 pbits in

  Math.Lemmas.nat_times_nat_is_nat (i+1) pbits;
  Math.Lemmas.nat_times_nat_is_nat i pbits;
  Math.Lemmas.pos_times_pos_is_pos (pow2 ind) (pow2 (pbits - j));
  Math.Lemmas.nat_over_pos_is_nat (bn_v n) (pow2 ind);

  calc (==) {
    bn_v n / pow2 ind % pow2 pbits;
    == { Math.Lemmas.euclidean_division_definition res (pow2 (pbits - j)) }
    res / pow2 (pbits - j) * pow2 (pbits - j) + res % pow2 (pbits - j);
    == { Math.Lemmas.pow2_modulo_modulo_lemma_1 (bn_v n / pow2 ind) (pbits - j) pbits }
    res / pow2 (pbits - j) * pow2 (pbits - j) + bn_v n / pow2 ind % pow2 (pbits - j);
    == { bn_get_ith_bit_aux_lemma n ind }
    res / pow2 (pbits - j) * pow2 (pbits - j) + v p1;
    == { Math.Lemmas.pow2_modulo_division_lemma_1 (bn_v n / pow2 ind) (pbits - j) pbits }
    bn_v n / pow2 ind / pow2 (pbits - j) % pow2 j * pow2 (pbits - j) + v p1;
    == { Math.Lemmas.division_multiplication_lemma (bn_v n) (pow2 ind) (pow2 (pbits - j)) }
    bn_v n / (pow2 ind * pow2 (pbits - j)) % pow2 j * pow2 (pbits - j) + v p1;
    == { Math.Lemmas.pow2_plus ind (pbits - j) }
    bn_v n / pow2 (ind + pbits - j) % pow2 j * pow2 (pbits - j) + v p1;
    == { Math.Lemmas.euclidean_division_definition ind pbits }
    bn_v n / pow2 (i * pbits + pbits) % pow2 j * pow2 (pbits - j) + v p1;
    == { Math.Lemmas.pow2_multiplication_modulo_lemma_2 (bn_v n / pow2 (i * pbits + pbits)) pbits (pbits - j) }
    bn_v n / pow2 (i * pbits + pbits) * pow2 (pbits - j) % pow2 pbits + v p1;
    == { Math.Lemmas.distributivity_add_left i 1 pbits }
    bn_v n / pow2 ((i + 1) * pbits) * pow2 (pbits - j) % pow2 pbits + v p1;
    == { Math.Lemmas.lemma_mod_mul_distr_l (bn_v n / pow2 ((i + 1) * pbits)) (pow2 (pbits - j)) (pow2 pbits) }
    bn_v n / pow2 ((i + 1) * pbits) % pow2 pbits * pow2 (pbits - j) % pow2 pbits + v p1;
    }


val bn_get_bits_limb_lemma:
    #t:limb_t
  -> #nLen:size_nat
  -> n:lbignum t nLen
  -> ind:size_nat{ind / bits t < nLen} ->
  Lemma (v (bn_get_bits_limb n ind) == bn_v n / pow2 ind % pow2 (bits t))

#push-options "--z3rlimit 100"
let bn_get_bits_limb_lemma #t #nLen n ind =
  let pbits = bits t in
  let i = ind / pbits in
  let j = ind % pbits in
  assert (i == ind / bits t);
  assert (i < nLen);
  Math.Lemmas.nat_over_pos_is_nat ind pbits;
  let p1 = n.[i] >>. size j in
  let res = bn_v n / pow2 ind % pow2 pbits in
  bn_get_ith_bit_aux_lemma n ind;
  assert (v p1 == bn_v n / pow2 ind % pow2 (pbits - j));

  if j = 0 then () else begin
    bn_get_bits_limb_aux_lemma n ind;

    if i + 1 < nLen then begin
      let p2 = n.[i + 1] <<. (size (pbits - j)) in
      calc (==) {
	v p2 % pow2 (pbits - j);
	== { }
	v n.[i + 1] * pow2 (pbits - j) % pow2 pbits % pow2 (pbits - j);
	== { Math.Lemmas.pow2_modulo_modulo_lemma_1 (v n.[i + 1] * pow2 (pbits - j)) (pbits - j) pbits }
	v n.[i + 1] * pow2 (pbits - j) % pow2 (pbits - j);
	== { Math.Lemmas.multiple_modulo_lemma (v n.[i + 1]) (pow2 (pbits - j)) }
	0;
	};
      let p3 = p1 |. p2 in
      logor_disjoint p1 p2 (pbits - j);
      assert (v p3 == v p1 + v p2);
      bn_eval_index n (i + 1);
      Math.Lemmas.swap_mul (i+1) pbits;
      assert (res == v p1 + v p2);
      assert (ind / bits t + 1 < nLen && 0 < ind % bits t) end
    else begin
      bn_eval_bound n nLen;
      Math.Lemmas.nat_times_nat_is_nat nLen pbits;
      assert (bn_v n < pow2 (nLen * pbits));
      Math.Lemmas.lemma_div_lt_nat (bn_v n) (nLen * pbits) ((i + 1) * pbits);
      Math.Lemmas.pow2_minus (nLen * pbits) ((i + 1) * pbits);
      assert (bn_v n / pow2 ((i + 1) * pbits) < pow2 0);
      assert_norm (pow2 0 = 1);

      Math.Lemmas.nat_over_pos_is_nat (bn_v n) (pow2 ((i+1) * pbits));
      assert (bn_v n / pow2 ((i+1) * pbits) == 0);

      Math.Lemmas.small_mod 0 (pow2 pbits);
      assert (res == 0 * pow2 (pbits - j) % pow2 pbits + v p1);
      Math.Lemmas.mul_zero_right_is_zero (pow2 (pbits - j));

      assert (res == v p1)
    end
  end
#pop-options

val bn_get_bits:
    #t:limb_t
  -> #nLen:size_nat
  -> n:lbignum t nLen
  -> i:size_nat
  -> l:size_nat{l < bits t /\ i / bits t < nLen} ->
  limb t

let bn_get_bits #t #nLen n ind l =
  let mask_l = (uint #t #SEC 1 <<. size l) -. uint #t 1 in
  bn_get_bits_limb n ind &. mask_l


val bn_get_bits_lemma:
    #t:limb_t
  -> #nLen:size_nat
  -> n:lbignum t nLen
  -> i:size_nat
  -> l:size_nat{l < bits t /\ i / bits t < nLen} ->
  Lemma (v (bn_get_bits n i l) == bn_v n / pow2 i % pow2 l)

let bn_get_bits_lemma #t #nLen n ind l =
  let tmp = bn_get_bits_limb n ind in
  let mask_l = (uint #t #SEC 1 <<. size l) -. uint #t 1 in
  let tmp1 = tmp &. mask_l in
  Math.Lemmas.pow2_lt_compat (bits t) l;
  mod_mask_lemma tmp (size l);

  shift_left_lemma #t #SEC (mk_int 1) (size l);
  assert (v (uint #t #SEC 1 <<. size l) == (1 * pow2 l) % modulus t);
  Math.Lemmas.mul_one_left_is_same (pow2 l);
  Math.Lemmas.small_mod (pow2 l) (modulus t);
  assert (v (uint #t #SEC 1 <<. size l) - 1 >= 0);

  assert (v (uint #t #SEC 1 <<. size l) - 1 < modulus t);
  Math.Lemmas.small_mod (v (uint #t #SEC 1 <<. size l) - 1) (modulus t);
  assert (v (mod_mask #t #SEC (size l)) == v mask_l);

  assert (v tmp1 == v tmp % pow2 l);
  bn_get_bits_limb_lemma #t #nLen n ind;
  assert (v tmp1 == bn_v n / pow2 ind % pow2 (bits t) % pow2 l);
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (bn_v n / pow2 ind) l (bits t);
  assert (v tmp1 == bn_v n / pow2 ind % pow2 l)
