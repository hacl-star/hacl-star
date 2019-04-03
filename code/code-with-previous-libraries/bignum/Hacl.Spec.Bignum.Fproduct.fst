module Hacl.Spec.Bignum.Fproduct

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Limb

open Hacl.Spec.Bignum.Modulo

module U32 = FStar.UInt32

#reset-options "--max_fuel 0 --max_ifuel 0"

let copy_from_wide_pre (s:seqelem_wide) : GTot Type0 =
  (forall (i:nat). {:pattern w (Seq.index s i)} i < len ==> w (Seq.index s i) < pow2 n)


#set-options "--z3rlimit 20"

val copy_from_wide_spec_: s:seqelem_wide{copy_from_wide_pre s} ->
  Tot (s':seqelem{(forall (j:nat). j < len ==> v (Seq.index s' j) = w (Seq.index s j))})
let copy_from_wide_spec_ s =
  Spec.Loops.seq_map (fun x -> wide_to_limb x) s

#reset-options "--max_fuel 1 --max_ifuel 1 --z3rlimit 50"

val lemma_copy_from_wide_: s:seqelem_wide{copy_from_wide_pre s} -> i:nat{i <= len} ->
  Lemma (seval_ (copy_from_wide_spec_ s) i = seval_wide_ s i)
let rec lemma_copy_from_wide_ s i =
  if i = 0 then ()
  else lemma_copy_from_wide_ s (i-1)


val copy_from_wide_spec: s:seqelem_wide{copy_from_wide_pre s} ->
  Tot (s':seqelem{(forall (j:nat). j < len ==> v (Seq.index s' j) = w (Seq.index s j))})
let copy_from_wide_spec s = copy_from_wide_spec_ s


val lemma_copy_from_wide: s:seqelem_wide{copy_from_wide_pre s} ->
  Lemma (seval (copy_from_wide_spec s) = seval_wide s)
let lemma_copy_from_wide s = lemma_copy_from_wide_ s len


val shift_spec: seqelem -> Tot seqelem
let shift_spec s =
  let sfirst = Seq.slice s 0 (len - 1) in
  let slast = Seq.slice s (len-1) len in
  Seq.append slast sfirst


val lemma_shift_spec_quantifiers: s:seqelem -> Lemma
  ((forall (i:nat). {:pattern (Seq.index s i)} (i > 0 /\ i < len) ==>
            Seq.index (shift_spec s) i == Seq.index s (i-1))
   /\ Seq.index (shift_spec s) 0 == Seq.index s (len - 1))
let lemma_shift_spec_quantifiers s = ()


#set-options "--z3rlimit 20 --initial_fuel 1 --max_fuel 1"

open FStar.Mul

let sum_scalar_multiplication_pre_ (sw:seqelem_wide) (s:seqelem) (scalar:limb) (i:nat{i <= len}) : GTot Type0 =
  (forall (j:nat). {:pattern (w (Seq.index sw j)) \/ (v (Seq.index s j))}j < i ==> w (Seq.index sw j) + (v (Seq.index s j) * v scalar) < pow2 wide_n)

private
val lemma_mod: a:nat -> b:nat -> s:nat -> Lemma
  (requires (a + b * s < pow2 wide_n))
  (ensures ((a + b * s) % pow2 wide_n = a + b * s))
  [SMTPat ((a + b * s) % pow2 wide_n)]
let lemma_mod a b s =
  Math.Lemmas.modulo_lemma (a + b * s) (pow2 wide_n)

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

val sum_scalar_multiplication_spec:
  sw:seqelem_wide ->
  s:seqelem ->
  scalar:limb{sum_scalar_multiplication_pre_ sw s scalar len} ->
  Tot (s':seqelem_wide{
    (forall (j:nat). {:pattern (w (Seq.index s' j))} j < len ==>
      w (Seq.index s' j) = w (Seq.index sw j) + (v (Seq.index s j) * v scalar))})
let sum_scalar_multiplication_spec sw s scalar =
  Spec.Loops.seq_map2 (fun x y -> Hacl.Bignum.Wide.(x +%^ (y *^ scalar))) sw s


#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

private val lemma_sum_scalar_multiplication_aux_1: a:nat -> b:nat -> c:nat -> d:nat -> e:nat -> f:nat -> g:nat -> h:nat -> i:nat -> scalar:nat -> v:nat -> Lemma
    (requires (a = v * b + c
    /\ d = v * e + f
    /\ g = v * h + i
    /\ b = e + h * scalar
    /\ c = f + i * scalar))
    (ensures (a = d + g * scalar))
private let lemma_sum_scalar_multiplication_aux_1 a b c d  e f g h i scalar v = ()


#reset-options "--max_fuel 1 --initial_fuel 1 --z3rlimit 100"

val lemma_sum_scalar_multiplication_:
  sw:seqelem_wide -> s:seqelem -> scalar:limb -> i:nat{i <= len /\ sum_scalar_multiplication_pre_ sw s scalar len} ->
  Lemma (seval_wide_ (sum_scalar_multiplication_spec sw s scalar) i = seval_wide_ sw i + (seval_ s i * v scalar))
let rec lemma_sum_scalar_multiplication_ sw s scalar i =
  if i = 0 then ()
  else (
    lemma_sum_scalar_multiplication_ sw s scalar (i-1);
    let s' = sum_scalar_multiplication_spec sw s scalar in
    cut (w (Seq.index s' (i-1)) = w (Seq.index sw (i-1)) + v (Seq.index s (i-1)) * v scalar);
    cut (seval_wide_ s' i = pow2 (limb_size * (i-1)) * w (Seq.index s' (i-1)) + seval_wide_ s' (i-1));
    cut (seval_wide_ sw i = pow2 (limb_size * (i-1)) * w (Seq.index sw (i-1)) + seval_wide_ sw (i-1));
    cut (seval_ s i = pow2 (limb_size * (i-1)) * v (Seq.index s (i-1)) + seval_ s (i-1));
    lemma_sum_scalar_multiplication_aux_1 (seval_wide_ s' i) (w (Seq.index s' (i-1))) (seval_wide_ s' (i-1)) (seval_wide_ sw i) (w (Seq.index sw (i-1))) (seval_wide_ sw (i-1)) (seval_ s i) (v (Seq.index s (i-1))) (seval_ s (i-1)) (v scalar) (pow2 (limb_size * (i-1)))
  )


let carry_wide_pre (s:seqelem_wide) (i:nat{i < len}) : GTot Type0 =
  (forall (j:nat). {:pattern (w (Seq.index s j))} (j > i /\ j < len) ==> w (Seq.index s j) < pow2 (wide_n - 1))
  /\ (forall (j:nat). {:pattern (w (Seq.index s j))} (j < i) ==> w (Seq.index s j) < pow2 limb_size)


#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

val carry_wide_step: s:seqelem_wide ->
    i:nat{i < len-1 /\ carry_wide_pre s i} ->
  Tot (s':seqelem_wide{
    (forall (j:nat). {:pattern (Seq.index s' j)} (j < i \/ (j > i+1 /\ j < len))
               ==> Seq.index s' j == Seq.index s j)
    /\ w (Seq.index s' i) = w (Seq.index s i) % pow2 limb_size
    /\ w (Seq.index s' (i+1)) = w (Seq.index s (i+1)) + (w (Seq.index s i) / pow2 limb_size)
    })

#reset-options "--z3rlimit 100 --max_fuel 0"

let lemma_carry_wide_step_aux_1 (x:nat) (y:pos) : Lemma (x % y < y) = ()

let carry_wide_step s i =
    Math.Lemmas.pow2_le_compat (wide_n - 1) (wide_n - limb_size);
    let si = Seq.index s i in
    let sip1 = Seq.index s (i+1) in
    assert (w sip1 < pow2 (wide_n - 1));
    assert_norm(pow2 0 = 1);
    Math.Lemmas.pow2_lt_compat limb_size 0;
    Math.Lemmas.pow2_lt_compat limb_n limb_size;
    Math.Lemmas.modulo_lemma (pow2 limb_size) (pow2 limb_n);
    let mask = (limb_one <<^ climb_size) -^ limb_one in
    UInt.logand_mask #limb_n (v (wide_to_limb si)) limb_size;
    let r0 = wide_to_limb si &^ mask in
    Math.Lemmas.pow2_plus (limb_n - limb_size) (limb_size);
    Math.Lemmas.modulo_modulo_lemma (w si) (pow2 limb_size) (pow2 (limb_n - limb_size));
    assert(v r0 = w si % pow2 limb_size);
    lemma_carry_wide_step_aux_1 (w si) (pow2 limb_size);
    assert(v r0 < pow2 limb_size);
    let open Hacl.Bignum.Wide in
    let c = si >>^ climb_size in
    Math.Lemmas.pow2_lt_compat (wide_n - 1) (limb_n);
    Math.Lemmas.pow2_double_sum (wide_n - 1);
    Math.Lemmas.lemma_div_lt (w si) (wide_n) (limb_size);
    Math.Lemmas.pow2_le_compat (wide_n - 1) (wide_n - limb_size);
    assert (w c < pow2 (wide_n - 1));
    let s' = Seq.upd s i (limb_to_wide r0) in
    assert(forall (j:nat). {:pattern (Seq.index s' j)} j < i + 1 ==> w (Seq.index s' j) < pow2 limb_size);
    assert(forall (j:nat). {:pattern (Seq.index s' j)} (j > i /\ j < len) ==> w (Seq.index s' j) < pow2 (wide_n - 1));
    let s'' = Seq.upd s' (i+1) (sip1 +^ c) in
    assert(forall (j:nat). {:pattern (Seq.index s'' j)} j < i + 1 ==> w (Seq.index s'' j) < pow2 limb_size);
    assert(forall (j:nat). {:pattern (Seq.index s'' j)} (j > i + 1 /\ j < len) ==> w (Seq.index s'' j) < pow2 (wide_n - 1));
    s''


#reset-options "--z3rlimit 100 --initial_fuel 2 --max_fuel 2"

val lemma_carry_wide_step_1: s:seqelem_wide -> i:nat{i < len - 1 /\ carry_wide_pre s i} -> j:nat{j <= i} ->
  Lemma (requires (true))
        (ensures (seval_wide_ (carry_wide_step s i) j = seval_wide_ s j))
let rec lemma_carry_wide_step_1 s i j =
  if j = 0 then () else lemma_carry_wide_step_1 s i (j-1)

#reset-options "--z3rlimit 400 --max_fuel 0"

val lemma_carry_wide_step_2_1: s1':nat -> s0':nat -> s1:nat -> s0:nat -> i:nat -> Lemma
  (requires (s0' = s0 % pow2 limb_size /\ s1' = s1 + s0 / pow2 limb_size))
  (ensures  (pow2 (limb_size * (i+1)) * s1' + pow2 (limb_size * (i)) * s0'
    = pow2 (limb_size * (i+1)) * s1 + pow2 (limb_size * (i)) * s0))
let lemma_carry_wide_step_2_1 s1' s0' s1 s0 i =
  Math.Lemmas.lemma_div_mod s0 (pow2 limb_size);
  assert(s0 = (pow2 limb_size) * (s0 / pow2 limb_size) + (s0 % pow2 limb_size));
  Math.Lemmas.distributivity_add_right (limb_size) i 1;
  assert(pow2 (limb_size * (i + 1)) = pow2 (limb_size * i + limb_size));
  Math.Lemmas.pow2_plus (limb_size * i) limb_size;
  assert(pow2 (limb_size * (i + 1)) = pow2 (limb_size * i) * pow2 limb_size);
  Math.Lemmas.distributivity_add_right (pow2 (limb_size * (i+1))) s1 (s0 / pow2 limb_size);
  Math.Lemmas.paren_mul_right (pow2 limb_size * i) (pow2 limb_size) (s0 / pow2 limb_size);
  Math.Lemmas.distributivity_add_right (pow2 (limb_size * i)) (pow2 limb_size * s1) s0;
  Math.Lemmas.distributivity_add_right (pow2 (limb_size * i)) (pow2 limb_size * (s0 / pow2 limb_size)) (s0 % pow2 limb_size)


#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

val lemma_carry_wide_step_2: s:seqelem_wide -> i:nat{i < len - 1 /\ carry_wide_pre s i
  /\ (forall (j:nat). {:pattern (w (Seq.index s j))} j < i ==> w (Seq.index s j) < pow2 limb_size)} ->
  Lemma (requires (true))
        (ensures (seval_wide_ (carry_wide_step s i) (i+2) = seval_wide_ s (i+2)))
let lemma_carry_wide_step_2 s i =
  let s' = carry_wide_step s i in
  lemma_seval_wide_def s' (i+2);
  lemma_seval_wide_def s' (i+1);
  lemma_seval_wide_def s (i+2);
  lemma_seval_wide_def s (i+1);
  cut (seval_wide_ s' (i+2) = pow2 (limb_size * (i+1)) * w (Seq.index s' (i+1))
                              + pow2 (limb_size * (i)) * w (Seq.index s' (i))
                              + seval_wide_ s' i);
  let s1' = w (Seq.index s' (i+1)) in
  let s0' = w (Seq.index s' (i)) in
  let s1 = w (Seq.index s (i+1)) in
  let s0 = w (Seq.index s (i)) in
  lemma_carry_wide_step_2_1 s1' s0' s1 s0 i;
  lemma_carry_wide_step_1 s i i


#set-options "--initial_fuel 1 --max_fuel 1"

val lemma_carry_wide_step_3: s:seqelem_wide -> i:nat{i < len - 1 /\ carry_wide_pre s i} -> j:nat{j > i + 1 /\ j <= len} ->
  Lemma (requires (true))
        (ensures (seval_wide_ (carry_wide_step s i) j = seval_wide_ s j))
        (decreases (j-i-2))
let rec lemma_carry_wide_step_3 s i j =
  if j = i+2 then lemma_carry_wide_step_2 s i
  else lemma_carry_wide_step_3 s i (j-1)

val lemma_carry_wide_step: s:seqelem_wide -> i:nat{i < len - 1 /\ carry_wide_pre s i} ->
  Lemma (requires (true))
        (ensures (seval_wide (carry_wide_step s i) = seval_wide s))
let lemma_carry_wide_step s i = lemma_carry_wide_step_3 s i len


#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

val carry_wide_step': s:seqelem_wide ->
    i:nat{i < len-1 /\ carry_wide_pre s i} ->
  Tot (s':seqelem_wide{carry_wide_pre s' (i+1) /\ seval_wide s' = seval_wide s})
let carry_wide_step' s i =
  let s' = carry_wide_step s i in
  lemma_carry_wide_step s i;
  Math.Lemmas.lemma_div_lt (w (Seq.index s i)) (2*word_size) limb_size;
  s'

val carry_wide_spec_: s:seqelem_wide -> i:nat{i < len /\ carry_wide_pre s i} ->
  k:nat{i <= k /\ k < len} ->
  Tot (s':seqelem_wide{seval_wide s' = seval_wide s
    /\ carry_wide_pre s' k
    /\ (forall (j:nat). {:pattern (w (Seq.index s' j))} (j < k) ==> w (Seq.index s' j) < pow2 limb_size)
    (* /\ (i < len-1 ==> w (Seq.index s' (len-1)) < w (Seq.index s (len-1)) + pow2 (2*word_size - limb_size)) *)})
  (decreases (len - 1 - i))
let rec carry_wide_spec_ s i k =
  (* Spec.Loops.repeat_range_spec 0 (len-1) carry_wide_step' s *)
  if i = k then s
  else (
    let s'' = carry_wide_step' s i in
    (* lemma_carry_wide_step s i; *)
    (* Math.Lemmas.lemma_div_lt (w (Seq.index s i)) (2*word_size) limb_size; *)
    carry_wide_spec_ s'' (i+1) k
  )


#reset-options "--initial_fuel 2 --max_fuel 2 --z3rlimit 200"

val lemma_carry_wide_spec_:
  min:nat -> max:nat{min < max /\ max < len} -> s:seqelem_wide{carry_wide_pre s min} -> 
  Lemma (requires (True))
        (ensures (
          (* carry_wide_pre (carry_wide_spec_ s min (max-1))  *)
          carry_wide_step' (carry_wide_spec_ s min (max-1)) (max-1) == carry_wide_spec_ s min max))
        (decreases (max - min))
let rec lemma_carry_wide_spec_ min max x =
  if min = max - 1 then ()
  else lemma_carry_wide_spec_ (min+1) max (carry_wide_step' x min)

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 200"

val carry_wide_spec: s:seqelem_wide{carry_wide_pre s 0} -> (* i:nat{i < len /\ carry_wide_pre s i} -> *)
  Tot (s':seqelem_wide{seval_wide s' = seval_wide s
    /\ (forall (j:nat). {:pattern (w (Seq.index s' j))} (j < len - 1) ==> w (Seq.index s' j) < pow2 limb_size)
    (* /\ (i < len-1 ==> w (Seq.index s' (len-1)) < w (Seq.index s (len-1)) + pow2 (2*word_size - limb_size)) *)})
  (* (decreases (len - 1 - i)) *)
let (* rec *) carry_wide_spec s =
  carry_wide_spec_ s 0 (len-1)

  (* if i = len - 1 then s *)
  (* else ( *)
  (*   let s'' = carry_wide_step s i in *)
  (*   lemma_carry_wide_step s i; *)
  (*   Math.Lemmas.lemma_div_lt (w (Seq.index s i)) (2*word_size) limb_size; *)
  (*   carry_wide_spec s'' (i+1) *)
  (* ) *)


let carry_limb_pre (s:seqelem) (i:nat{i < len}) : GTot Type0 =
  (forall (j:nat). {:pattern (v (Seq.index s j))} (j > i /\ j < len) ==> v (Seq.index s j) < pow2 (limb_n - 1))
  /\ (forall (j:nat). {:pattern (v (Seq.index s j))} (j < i) ==> v (Seq.index s j) < pow2 limb_size)


#set-options "--z3rlimit 200 --initial_fuel 0 --max_fuel 0"


val carry_limb_step: s:seqelem -> i:nat{i < len-1 /\ carry_limb_pre s i} ->
  Tot (s':seqelem{
    (forall (j:nat). {:pattern (Seq.index s' j)} (j < i \/ (j > i+1 /\ j < len))
               ==> Seq.index s' j == Seq.index s j)
    /\ v (Seq.index s' i) = v (Seq.index s i) % pow2 limb_size
    /\ v (Seq.index s' (i+1)) = v (Seq.index s (i+1)) + (v (Seq.index s i) / pow2 limb_size)})
let carry_limb_step s i =
    let si = Seq.index s i in
    let sip1 = Seq.index s (i+1) in
    cut (v sip1 < pow2 (limb_n - 1));
    assert_norm(pow2 0 = 1);
    Math.Lemmas.pow2_lt_compat limb_size 0;
    Math.Lemmas.pow2_lt_compat limb_n limb_size;
    Math.Lemmas.modulo_lemma (pow2 limb_size) (pow2 limb_n);
    let mask = (limb_one <<^ climb_size) -^ limb_one in
    UInt.logand_mask #limb_n (v ( si)) limb_size;
    let r0 =  si &^ mask in
    Math.Lemmas.pow2_plus (limb_n - limb_size) (limb_size);
    Math.Lemmas.modulo_modulo_lemma (v si) (pow2 limb_size) (pow2 (limb_n - limb_size));
    assert(v r0 = v si % pow2 limb_size);
    assert(v r0 < pow2 limb_size);
    let open Hacl.Bignum.Limb in
    let c = si >>^ climb_size in
    Math.Lemmas.pow2_double_sum (limb_n - 1);
    Math.Lemmas.lemma_div_lt (v si) (limb_n) (limb_size);
    Math.Lemmas.pow2_le_compat (limb_n - 1) (limb_n - limb_size);
    cut (v c < pow2 (limb_n - 1));
    let s' = Seq.upd s i ( r0) in
    assert(forall (j:nat). {:pattern (Seq.index s' j)} j < i + 1 ==> v (Seq.index s' j) < pow2 limb_size);
    assert(forall (j:nat). {:pattern (Seq.index s' j)} (j > i /\ j < len) ==> v (Seq.index s' j) < pow2 (limb_n - 1));
    let s'' = Seq.upd s' (i+1) (sip1 +^ c) in
    assert(forall (j:nat). {:pattern (Seq.index s'' j)} j < i + 1 ==> v (Seq.index s'' j) < pow2 limb_size);
    assert(forall (j:nat). {:pattern (Seq.index s'' j)} (j > i + 1 /\ j < len) ==> v (Seq.index s'' j) < pow2 (limb_n - 1));
    s''


#set-options "--initial_fuel 1 --max_fuel 1"

val lemma_carry_limb_step_1: s:seqelem -> i:nat{i < len - 1 /\ carry_limb_pre s i} -> j:nat{j <= i} ->
  Lemma (requires (true))
        (ensures (seval_ (carry_limb_step s i) j = seval_ s j))
let rec lemma_carry_limb_step_1 s i j =
  if j = 0 then () else lemma_carry_limb_step_1 s i (j-1)

#reset-options "--z3rlimit 1000 --initial_fuel 0 --max_fuel 0"

val lemma_carry_limb_step_2_1: s1':nat -> s0':nat -> s1:nat -> s0:nat -> i:nat -> Lemma
  (requires (s0' = s0 % pow2 limb_size /\ s1' = s1 + s0 / pow2 limb_size))
  (ensures  (pow2 (limb_size * (i+1)) * s1' + pow2 (limb_size * (i)) * s0'
    = pow2 (limb_size * (i+1)) * s1 + pow2 (limb_size * (i)) * s0))
let lemma_carry_limb_step_2_1 s1' s0' s1 s0 i =
  Math.Lemmas.lemma_div_mod s1 (pow2 limb_size);
  cut (s0 + pow2 limb_size * s1 = s0' + pow2 limb_size * s1');
  cut (pow2 (limb_size * i) * (s0 + pow2 limb_size * s1) = pow2 (limb_size * i) * (s0' + pow2 limb_size * s1'));
  cut (limb_size * (i+1) = limb_size * i + limb_size);
  Math.Lemmas.pow2_plus (limb_size * i) limb_size;
  Math.Lemmas.distributivity_add_right (pow2 (limb_size * i)) (pow2 limb_size * s1) s0;
  Math.Lemmas.paren_mul_right (pow2 (limb_size * i)) (pow2 limb_size) s1;
  Math.Lemmas.distributivity_add_right (pow2 (limb_size * i)) (pow2 limb_size * s1') s0'

#reset-options "--z3rlimit 200 --initial_fuel 2 --max_fuel 2"

val lemma_carry_limb_step_2: s:seqelem -> i:nat{i < len - 1 /\ carry_limb_pre s i} ->
  Lemma (requires (true))
        (ensures (seval_ (carry_limb_step s i) (i+2) = seval_ s (i+2)))
let rec lemma_carry_limb_step_2 s i =
  let s' = carry_limb_step s i in
  cut (seval_ s' (i+2) = pow2 (limb_size * (i+1)) * v (Seq.index s' (i+1))
                              + pow2 (limb_size * (i)) * v (Seq.index s' (i))
                              + seval_ s' i);
  let s1' = v (Seq.index s' (i+1)) in
  let s0' = v (Seq.index s' (i)) in
  let s1 = v (Seq.index s (i+1)) in
  let s0 = v (Seq.index s (i)) in
  lemma_carry_limb_step_2_1 s1' s0' s1 s0 i;
  lemma_carry_limb_step_1 s i i

val lemma_carry_limb_step_3: s:seqelem -> i:nat{i < len - 1 /\ carry_limb_pre s i} -> j:nat{j > i + 1 /\ j <= len} ->
  Lemma (requires (true))
        (ensures (seval_ (carry_limb_step s i) j = seval_ s j))
        (decreases (j-i-2))
let rec lemma_carry_limb_step_3 s i j =
  if j = i+2 then lemma_carry_limb_step_2 s i
  else lemma_carry_limb_step_3 s i (j-1)

val lemma_carry_limb_step: s:seqelem -> i:nat{i < len - 1 /\ carry_limb_pre s i} ->
  Lemma (requires (true))
        (ensures (seval (carry_limb_step s i) = seval s))
let lemma_carry_limb_step s i = lemma_carry_limb_step_3 s i len


#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0"

val carry_limb_step': s:seqelem ->
    i:nat{i < len-1 /\ carry_limb_pre s i} ->
  Tot (s':seqelem{carry_limb_pre s' (i+1) /\ seval s' = seval s})
let carry_limb_step' s i =
  let s' = carry_limb_step s i in
  lemma_carry_limb_step s i;
  s'

val carry_limb_spec_: s:seqelem -> i:nat{i < len /\ carry_limb_pre s i} -> k:nat{i <= k /\ k < len} ->
  Tot (s':seqelem{seval s' = seval s /\ carry_limb_pre s' k})
  (decreases (len - 1 - i))
let rec carry_limb_spec_ s i k =
  if i = k then s
  else (
    let s'' = carry_limb_step' s i in
    carry_limb_spec_ s'' (i+1) k
  )


#reset-options "--initial_fuel 2 --max_fuel 2 --z3rlimit 200"

val lemma_carry_limb_spec_:
  min:nat -> max:nat{min < max /\ max < len} -> s:seqelem{carry_limb_pre s min} -> 
  Lemma (requires (True))
        (ensures (
          carry_limb_step' (carry_limb_spec_ s min (max-1)) (max-1) == carry_limb_spec_ s min max))
        (decreases (max - min))
let rec lemma_carry_limb_spec_ min max x =
  if min = max - 1 then ()
  else lemma_carry_limb_spec_ (min+1) max (carry_limb_step' x min)

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 200"

val carry_limb_spec: s:seqelem{carry_limb_pre s 0} ->
  Tot (s':seqelem{seval s' = seval s})
let carry_limb_spec s =
  carry_limb_spec_ s 0 (len-1)



let carry_0_to_1_pre (input:seqelem) : GTot Type0 =
  (forall (i:nat). (i > 0 /\ i < len) ==> v (Seq.index input i) < pow2 limb_size)


#reset-options "--z3rlimit 50 --initial_fuel 0 --max_fuel 0"

val carry_0_to_1_spec: input:seqelem{carry_0_to_1_pre input} -> Tot (output:seqelem{seval output = seval input
  /\ v (Seq.index output 0) = v (Seq.index input 0) % pow2 limb_size
  /\ v (Seq.index output 1) = v (Seq.index input 1) + v (Seq.index input 0) / pow2 limb_size})
let carry_0_to_1_spec input =
  let i0 = Seq.index input 0 in
  let i1 = Seq.index input 1 in
  assert_norm(pow2 0 = 1);
  Math.Lemmas.pow2_lt_compat limb_size 0;
  Math.Lemmas.pow2_lt_compat limb_n limb_size;
  Math.Lemmas.modulo_lemma (pow2 limb_size) (pow2 limb_n);
  let i0' = i0 &^ ((limb_one <<^ climb_size) -^ limb_one) in
  UInt.logand_mask #limb_n (v i0) limb_size;
  Math.Lemmas.pow2_plus (limb_n - limb_size) (limb_size);
  Math.Lemmas.modulo_modulo_lemma (v i0) (pow2 limb_size) (pow2 (limb_n - limb_size));
  let c = i0 >>^ climb_size in
  Math.Lemmas.pow2_double_sum (limb_n - 1);
  Math.Lemmas.pow2_le_compat (limb_n - 1) limb_size;
  Math.Lemmas.lemma_div_lt (v i0) (limb_n) (limb_size);
  Math.Lemmas.pow2_le_compat (limb_n - 1) (limb_n - limb_size);
  let i1' = i1 +^ c in
  let output = Seq.upd input 0 i0' in
  lemma_carry_limb_step input 0;
  Seq.upd output 1 i1'
