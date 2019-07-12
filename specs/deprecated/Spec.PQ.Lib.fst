module Spec.PQ.Lib

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
//open Lib.Sequence.Lemmas
open FStar.Math.Lemmas

let numeric #t x =
  match t with
  | U8 -> u8 x
  | U16 -> u16 x
  | U32 -> u32 x
  | U64 -> u64 x
  | U128 -> u128 x
  | SIZE -> size x
  | NATm m -> modulo x m

let to_numeric #t t1 x =
  match t, t1 with
  | U16, U16 -> x
  | U16, NATm m -> modulo ((Lib.RawIntTypes.uint_to_nat x) % m) m
  | NATm m, U16 -> u16 ((Lib.RawIntTypes.uint_to_nat x) % modulus U16)
  | _ -> admit()

let vector_t t len = lseq (uint_t t) len

let vector_create t len = create len (numeric #t 0)

let vget #t #len a i = a.[i]

let vset #t #len a i v = a.[i] <- v

let vector_zero #t #len = vector_create t len

val vector_pred0:
  #t:numeric_t -> #len:size_nat -> f:(uint_t t -> uint_t t -> uint_t t) ->
  a:vector_t t len -> b:vector_t t len ->
  i:size_nat{i <= len} -> res:vector_t t len -> Tot Type0
let vector_pred0 #t #len f a b i res = forall (i1:size_nat{i1 < i}). vget res i1 == f (vget a i1) (vget b i1)

val vector_f0:
  #t:numeric_t -> #len:size_nat -> f:(uint_t t -> uint_t t -> uint_t t) ->
  a:vector_t t len -> b:vector_t t len ->
  Tot (repeatable #(vector_t t len) #len (vector_pred0 #t #len f a b))
let vector_f0 #t #len f a b i c = vset c i (f (vget a i) (vget b i))

let vector_add #t #len a b =
  let res = vector_create t len in
  repeati_inductive len
  (vector_pred0 #t #len add_mod a b)
  (fun i res -> vector_f0 add_mod a b i res)
  res

let vector_sub #t #len a b =
  let res = vector_create t len in
  repeati_inductive len
  (vector_pred0 #t #len sub_mod a b)
  (fun i res -> vector_f0 sub_mod a b i res)
  res

let vector_pointwise_mul #t #len a b =
  let res = vector_create t len in
  repeati_inductive len
  (vector_pred0 #t #len mul_mod a b)
  (fun i res -> vector_f0 mul_mod a b i res)
  res

let matrix_t t n1 n2 = lseq (vector_t t n1) n2

let matrix_create t n1 n2 = create n2 (vector_create t n1)

let mget #t #n1 #n2 a i j = (a.[j]).[i]

let mset #t #n1 #n2 a i j v = //(a.[j]).[i] <- v
  let aj = a.[j] in
  let aji = aj.[i] <- v in
  a.[j] <- aji

val sum_:
  #t:numeric_t -> n:size_nat -> f:(j:size_nat{j < n} -> uint_t t) ->
  tmp0:uint_t t -> i:size_nat{i <= n} -> Tot (uint_t t)
  (decreases (n - i))
let rec sum_ #t n f tmp0 i =
  if (i < n) then
    sum_ #t n f (tmp0 +. f i) (i + 1)
  else tmp0

let sum #t n f tmp0 = sum_ #t n f tmp0 0

let matrix_zero #t #n1 #n2 = matrix_create t n1 n2

val matrix_pred0:
  #t:numeric_t -> #n1:size_nat -> #n2:size_nat -> f:(uint_t t -> uint_t t -> uint_t t) ->
  a:matrix_t t n1 n2 -> b:matrix_t t n1 n2 ->
  i0:size_nat{i0 < n1} -> res0:matrix_t t n1 n2 -> j:size_nat{j <= n2} -> res:matrix_t t n1 n2 -> Tot Type0
let matrix_pred0 #t #n1 #n2 f a b i0 res0 j res =
  (forall (j1:size_nat{j1 < j}). mget res i0 j1 == f (mget a i0 j1) (mget b i0 j1)) /\
  (forall (i:size_nat{i < n1 /\ i <> i0}) (j:size_nat{j < n2}). mget res0 i j == mget res i j)

val matrix_f0:
  #t:numeric_t -> #n1:size_nat -> #n2:size_nat -> f:(uint_t t -> uint_t t -> uint_t t) ->
  a:matrix_t t n1 n2 -> b:matrix_t t n1 n2 ->
  i0:size_nat{i0 < n1} -> res0:matrix_t t n1 n2 -> Tot (repeatable #(matrix_t t n1 n2) #n2 (matrix_pred0 #t #n1 #n2 f a b i0 res0))
let matrix_f0 #q #n1 #n2 f a b i0 res0 j c = mset c i0 j (f (mget a i0 j) (mget b i0 j))

val matrix_pred1:
  #t:numeric_t -> #n1:size_nat -> #n2:size_nat -> f:(uint_t t -> uint_t t -> uint_t t) ->
  a:matrix_t t n1 n2 -> b:matrix_t t n1 n2 ->
  i:size_nat{i <= n1} -> res:matrix_t t n1 n2 -> Tot Type0
let matrix_pred1 #q #n1 #n2 f a b i res = forall (i1:size_nat{i1 < i}) (j:size_nat{j < n2}). mget res i1 j == f (mget a i1 j) (mget b i1 j)

val matrix_f1:
  #t:numeric_t -> #n1:size_nat -> #n2:size_nat -> f:(uint_t t -> uint_t t -> uint_t t) ->
  a:matrix_t t n1 n2 -> b:matrix_t t n1 n2 ->
  Tot (repeatable #(matrix_t t n1 n2) #n1 (matrix_pred1 #t #n1 #n2 f a b))
let matrix_f1 #t #n1 #n2 f a b i c =
  let res =
    repeati_inductive n2
    (matrix_pred0 #t #n1 #n2 f a b i c)
    (fun j cj -> matrix_f0 #t #n1 #n2 f a b i c j cj) c in
  res

let matrix_add #t #n1 #n2 a b =
  let c = matrix_create t n1 n2 in
  repeati_inductive n1
  (matrix_pred1 #t #n1 #n2 add_mod a b)
  (fun i c -> matrix_f1 #t #n1 #n2 add_mod a b i c) c

let matrix_sub #t #n1 #n2 a b =
  let c = matrix_create t n1 n2 in
  repeati_inductive n1
  (matrix_pred1 #t #n1 #n2 sub_mod a b)
  (fun i c -> matrix_f1 #t #n1 #n2 sub_mod a b i c) c

val matrix_mul_pred0:
  #t:numeric_t{t <> U128} -> #n1:size_nat -> #n2:size_nat -> #n3:size_nat ->
  a:matrix_t t n1 n2 -> b:matrix_t t n2 n3 ->
  i0:size_nat{i0 < n1} -> res0:matrix_t t n1 n3 -> k:size_nat{k <= n3} -> res:matrix_t t n1 n3 -> Tot Type0
let matrix_mul_pred0 #t #n1 #n2 #n3 a b i0 res0 k res =
  (forall (k1:size_nat{k1 < k}). mget res i0 k1 == sum #t n2 (fun j -> mget a i0 j *. mget b j k1) (numeric #t 0)) /\
  (forall (i:size_nat{i < n1 /\ i <> i0}) (k:size_nat{k < n3}). mget res0 i k == mget res i k)

val matrix_mul_f0:
  #t:numeric_t{t <> U128} -> #n1:size_nat -> #n2:size_nat -> #n3:size_nat ->
  a:matrix_t t n1 n2 -> b:matrix_t t n2 n3 ->
  i0:size_nat{i0 < n1} -> res0:matrix_t t n1 n3 -> Tot (repeatable #(matrix_t t n1 n3) #n3 (matrix_mul_pred0 #t #n1 #n2 #n3 a b i0 res0))
let matrix_mul_f0 #t #n1 #n2 #n3 a b i0 res0 k c = mset c i0 k (sum #t n2 (fun j -> mget a i0 j *. mget b j k) (numeric #t 0))

val matrix_mul_pred1:
  #t:numeric_t{t <> U128} -> #n1:size_nat -> #n2:size_nat -> #n3:size_nat ->
  a:matrix_t t n1 n2 -> b:matrix_t t n2 n3 ->
  i:size_nat{i <= n1} -> res:matrix_t t n1 n3 -> Tot Type0
let matrix_mul_pred1 #t #n1 #n2 #n3 a b i res =
  forall (i1:size_nat{i1 < i}) (k:size_nat{k < n3}). mget res i1 k == sum #t n2 (fun j -> mget a i1 j *. mget b j k) (numeric #t 0)

val matrix_mul_f1:
  #t:numeric_t{t <> U128} -> #n1:size_nat -> #n2:size_nat -> #n3:size_nat ->
  a:matrix_t t n1 n2 -> b:matrix_t t n2 n3 ->
  Tot (repeatable #(matrix_t t n1 n3) #n1 (matrix_mul_pred1 #t #n1 #n2 #n3 a b))
let matrix_mul_f1 #t #n1 #n2 #n3 a b i c =
  let res =
    repeati_inductive n3
    (matrix_mul_pred0 #t #n1 #n2 #n3 a b i c)
    (fun k ck -> matrix_mul_f0 #t #n1 #n2 #n3 a b i c k ck) c in
  res

#reset-options "--z3rlimit 50 --max_fuel  0"
let matrix_mul #t #n1 #n2 #n3 a b =
  let c = matrix_create t n1 n3 in
  repeati_inductive n1
  (matrix_mul_pred1 #t #n1 #n2 #n3 a b)
  (fun i c -> matrix_mul_f1 #t #n1 #n2 #n3 a b i c) c

(* Lemmas about the sum function *)

val sum_linearity:
  #t:numeric_t -> n:size_nat ->
  f:(i:size_nat{i < n} -> uint_t t) -> tmp0:uint_t t ->
  g:(i:size_nat{i < n} -> uint_t t) -> tmp1:uint_t t ->
  i:size_nat{i <= n} -> Lemma
  (requires True)
  (ensures (sum_ #t n f tmp0 i +. sum_ #t n g tmp1 i == sum_ #t n (fun j -> f j +. g j) (tmp0 +. tmp1) i))
  (decreases (n - i))
  #reset-options "--z3rlimit 50 --max_fuel 1"
let rec sum_linearity #t n f tmp0 g tmp1 i =
  if (i < n) then begin
    modulo_distributivity (uint_v tmp0 + uint_v tmp1) (uint_v (f i) + uint_v (g i)) (modulus t);
    modulo_distributivity (uint_v tmp0 + uint_v (f i)) (uint_v tmp1 + uint_v (g i)) (modulus t);
    uintv_extensionality ((tmp0 +. tmp1) +. (f i +. g i)) ((tmp0 +. f i) +. (tmp1 +. g i));
    sum_linearity #t n f (tmp0 +. f i) g (tmp1 +. g i) (i + 1) end
  else ()

val sum_extensionality:
  #t:numeric_t -> n:size_nat ->
  f:(i:size_nat{i < n} -> uint_t t) ->
  g:(i:size_nat{i < n} -> uint_t t) ->
  tmp0:uint_t t -> i:size_nat{i <= n} -> Lemma
  (requires (forall (i:size_nat{i < n}). f i == g i))
  (ensures (sum_ #t n f tmp0 i == sum_ #t n g tmp0 i))
  (decreases (n - i))
  [SMTPat (sum_ #t n f tmp0 i == sum_ #t n g tmp0 i)]
  #reset-options "--z3rlimit 50 --max_fuel 1"
let rec sum_extensionality #t n f g tmp0 i =
  if (i < n) then
    sum_extensionality #t n f g (tmp0 +. f i) (i + 1)
  else ()

val sum_mul_scalar:
  #t:numeric_t{t <> U128} -> n:size_nat ->
  f:(i:size_nat{i < n} -> uint_t t) -> tmp0:uint_t t ->
  sc:uint_t t -> i:size_nat{i <= n} -> Lemma
  (requires True)
  (ensures (sum_ #t n f tmp0 i *. sc == sum_ #t n (fun j -> f j *. sc) (tmp0 *. sc) i))
  (decreases (n - i))
  #reset-options "--z3rlimit 50 --max_fuel 1"
let rec sum_mul_scalar #t n f tmp0 sc i =
  if (i < n) then begin
    //assume (zqadd (zqmul tmp0 sc) (zqmul sc (f i)) = zqmul sc (zqadd tmp0 (f i)));
    lemma_mod_mul_distr_l (uint_v tmp0 + uint_v (f i)) (uint_v sc) (modulus t);
    distributivity_add_left (uint_v tmp0) (uint_v (f i)) (uint_v sc);
    modulo_distributivity (uint_v tmp0 * uint_v sc) (uint_v (f i) * uint_v sc) (modulus t);
    uintv_extensionality (tmp0 *. sc +. f i *. sc) ((tmp0 +. f i) *. sc);
    sum_mul_scalar #t n f (tmp0 +. f i) sc (i + 1) end
  else ()

assume
val sum_fubini:
   #t:numeric_t -> n1:size_nat -> n2:size_nat ->
   f:(i:size_nat{i < n1} -> j:size_nat{j < n2} -> uint_t t) ->
   Lemma
   (sum #t n1 (fun i -> sum #t n2 (fun j -> f i j) (numeric #t 0)) (numeric #t 0)  ==
    sum #t n2 (fun j -> sum #t n1 (fun i -> f i j) (numeric #t 0)) (numeric #t 0))

(* Lemmas *)
val matrix_equality:
  #t:numeric_t -> #n1:size_nat -> #n2:size_nat ->
  a:matrix_t t n1 n2 -> b:matrix_t t n1 n2 -> Lemma
  (requires (forall (i:size_nat{i < n1}) (j:size_nat{j < n2}). mget a i j == mget b i j))
  (ensures  (a == b))
let matrix_equality #q #n1 #n2 a b =
  let open FStar.Tactics in
  assert (forall (j:size_nat{j < n2}) (i:size_nat{i < n1}). mget a i j == index (index a j) i);
  assert (forall (j:size_nat{j < n2}) (i:size_nat{i < n1}). mget b i j == index (index b j) i);
  assert_by_tactic (a == b)
    (fun () ->
      apply_lemma (`eq_elim);
      apply_lemma (`eq_intro);
      let j = forall_intro () in
      apply_lemma (`eq_elim);
      apply_lemma (`eq_intro);
      let i = forall_intro () in
      smt ())

val add_distr_right:
  #t:numeric_t{t <> U128} -> a:uint_t t -> b:uint_t t -> c:uint_t t -> Lemma
  (requires True)
  (ensures ((a +. b) *. c == a *. c +. b *. c))
  [SMTPat (a *. c +. b *. c)]
let add_distr_right #t a b c =
  let r = (a +. b) *. c in
  lemma_mod_mul_distr_l (uint_v a + uint_v b) (uint_v c) (modulus t);
  distributivity_add_left (uint_v a) (uint_v b) (uint_v c);
  modulo_distributivity (uint_v a * uint_v c) (uint_v b * uint_v c) (modulus t);
  uintv_extensionality ((a +. b) *. c) (a *. c +. b *. c)

val matrix_distributivity_add_right_get:
  #t:numeric_t{t <> U128} -> #n1:size_nat -> #n2:size_nat -> #n3:size_nat ->
  a:matrix_t t n1 n2 -> b:matrix_t t n1 n2 -> c:matrix_t t n2 n3 ->
  i:size_nat{i < n1} -> k:size_nat{k < n3} -> Lemma
  (requires True)
  (ensures ( sum #t n2 (fun j -> (mget a i j +. mget b i j) *. mget c j k) (numeric 0) ==
             sum #t n2 (fun j -> mget a i j *. mget c j k) (numeric 0) +. sum #t n2 (fun j -> mget b i j *. mget c j k) (numeric 0)))
  [SMTPat (sum #t n2 (fun j -> (mget a i j +. mget b i j) *. mget c j k) (numeric 0))]
  #reset-options "--z3rlimit 50 --max_fuel 0"
let matrix_distributivity_add_right_get #t #n1 #n2 #n3 a b c i k =
  sum_linearity #t n2 (fun j -> mget a i j *. mget c j k) (numeric 0) (fun j -> mget b i j *. mget c j k) (numeric 0) 0;
  uintv_extensionality (numeric #t 0 +. numeric #t 0) (numeric #t 0);
  sum_extensionality #t n2 (fun j -> mget a i j *. mget c j k +. mget b i j *. mget c j k) (fun j -> (mget a i j +. mget b i j) *. mget c j k) (numeric 0) 0


val sum_extensionality':
  #t:numeric_t -> n1:size_nat -> n3:size_nat ->
  n:size_nat -> i:size_nat{i < n1} -> k:size_nat{k < n3} ->
  f:(i:size_nat{i < n} -> uint_t t) ->
  g:(i:size_nat{i < n} -> uint_t t){(forall (i:size_nat{i < n}). f i == g i)} ->
  Lemma (sum_ #t n f (numeric 0) 0 == sum_ #t n g (numeric 0) 0)
let sum_extensionality' #t n1 n3 n i k f g =
  sum_extensionality #t n f g (numeric 0) 0

#reset-options "--z3rlimit 50 --max_fuel 0"
let matrix_distributivity_add_right #t #n1 #n2 #n3 a b c =
  let r1 = matrix_add a b in
  let r2 = matrix_mul r1 c in
  Classical.forall_intro_2 #(i:size_nat{i < n1}) #(fun i -> k:size_nat{k < n3})
    #(fun i k -> sum_ #t n2 (fun j -> mget r1 i j *. mget c j k) (numeric 0) 0 ==
               sum_ #t n2 (fun j -> (mget a i j +. mget b i j) *. mget c j k) (numeric 0) 0)
    (fun i k ->
      ((sum_extensionality' #t n1 n3 n2 i k
        (fun j -> mget r1 i j *. mget c j k)
        (fun j -> (mget a i j +. mget b i j) *. mget c j k) <:
      (Lemma
        (sum_ #t n2 (fun j -> mget r1 i j *. mget c j k) (numeric 0) 0 ==
         sum_ #t n2 (fun j -> (mget a i j +. mget b i j) *. mget c j k) (numeric 0) 0)))));
  assert (forall (i:size_nat{i < n1}) (k:size_nat{k < n3}).{:pattern (mget r2 i k)}
    mget r2 i k ==
    sum #t n2 (fun j -> (mget a i j +. mget b i j) *. mget c j k) (numeric 0));
  Classical.forall_intro_2 #(i:size_nat{i < n1}) #(fun i -> k:size_nat{k < n3})
    #(fun i k -> sum #t n2 (fun j -> (mget a i j +. mget b i j) *. mget c j k) (numeric 0) ==
	       sum #t n2 (fun j -> mget a i j *. mget c j k) (numeric 0) +. sum #t n2 (fun j -> mget b i j *. mget c j k) (numeric 0))
    (fun i k ->
      (matrix_distributivity_add_right_get #t #n1 #n2 #n3 a b c i k) <:
      (Lemma
        (sum #t n2 (fun j -> (mget a i j +. mget b i j) *. mget c j k) (numeric 0) ==
	 sum #t n2 (fun j -> mget a i j *. mget c j k) (numeric 0) +. sum #t n2 (fun j -> mget b i j *. mget c j k) (numeric 0))));
  assert (forall (i:size_nat{i < n1}) (k:size_nat{k < n3}).
    sum #t n2 (fun j -> (mget a i j +. mget b i j) *. mget c j k) (numeric 0) ==
    sum #t n2 (fun j -> mget a i j *. mget c j k) (numeric 0) +. sum #t n2 (fun j -> mget b i j *. mget c j k) (numeric 0));
  let r3 = matrix_mul a c in
  let r4 = matrix_mul b c in
  let r5 = matrix_add r3 r4 in
  matrix_equality r2 r5

val add_distr_left:
  #t:numeric_t{t <> U128} -> a:uint_t t -> b:uint_t t -> c:uint_t t -> Lemma
  (requires True)
  (ensures (c *. (a +. b) == c *. a +. c *. b))
  [SMTPat (c *. a +. c *. b)]
let add_distr_left #t a b c =
  let r = c *. (a +. b) in
  lemma_mod_mul_distr_l (uint_v a + uint_v b) (uint_v c) (modulus t);
  assert (uint_v r = ((uint_v a + uint_v b) * uint_v c) % modulus t);
  assert (uint_v r = (uint_v c * (uint_v a + uint_v b)) % modulus t);
  distributivity_add_right (uint_v c) (uint_v a) (uint_v b);
  modulo_distributivity (uint_v c * uint_v a) (uint_v c * uint_v b) (modulus t);
  uintv_extensionality (c *. (a +. b)) (c *. a +. c *. b)

val matrix_distributivity_add_left_get:
  #t:numeric_t{t <> U128} -> #n1:size_nat -> #n2:size_nat -> #n3:size_nat ->
  a:matrix_t t n1 n2 -> b:matrix_t t n1 n2 -> c:matrix_t t n3 n1 ->
  i:size_nat{i < n3} -> k:size_nat{k < n2} -> Lemma
  (requires True)
  (ensures (sum #t n1 (fun j -> mget c i j *. mget a j k) (numeric 0) +. sum #t n1 (fun j -> mget c i j *. mget b j k) (numeric 0) ==
	    sum #t n1 (fun j -> mget c i j *. (mget a j k +. mget b j k)) (numeric 0)))
let matrix_distributivity_add_left_get #t #n1 #n2 #n3 a b c i k =
  sum_linearity #t n1 (fun j -> mget c i j *. mget a j k) (numeric 0) (fun j -> mget c i j *. mget b j k) (numeric 0) 0;
  uintv_extensionality (numeric #t 0 +. numeric #t 0) (numeric #t 0);
  assert (sum #t n1 (fun j -> mget c i j *. mget a j k) (numeric 0) +. sum #t n1 (fun j -> mget c i j *. mget b j k) (numeric 0) ==
	  sum #t n1 (fun j -> mget c i j *. mget a j k +. mget c i j *. mget b j k) (numeric 0));
  sum_extensionality #t n1 (fun j -> mget c i j *. mget a j k +. mget c i j *. mget b j k) (fun j -> mget c i j *. (mget a j k +. mget b j k)) (numeric 0) 0

let matrix_distributivity_add_left #t #n1 #n2 #n3 a b c =
  let r1 = matrix_add a b in
  let r2 = matrix_mul c r1 in
  Classical.forall_intro_2 #(i:size_nat{i < n3}) #(fun i -> k:size_nat{k < n2})
    #(fun i k -> sum_ #t n1 (fun j -> mget c i j *. mget r1 j k) (numeric 0) 0 ==
               sum_ #t n1 (fun j -> mget c i j *. (mget a j k +. mget b j k)) (numeric 0) 0)
    (fun i k ->
      (sum_extensionality' #t n3 n2 n1 i k
        (fun j -> mget c i j *. mget r1 j k)
        (fun j -> mget c i j *. (mget a j k +. mget b j k)) <:
      (Lemma
        (sum_ #t n1 (fun j -> mget c i j *. mget r1 j k) (numeric 0) 0 ==
         sum_ #t n1 (fun j -> mget c i j *. (mget a j k +. mget b j k)) (numeric 0) 0))));
  assert (forall (i:size_nat{i < n3}) (k:size_nat{k < n2}).
    mget r2 i k ==
    sum_ #t n1 (fun j -> mget c i j *. (mget a j k +. mget b j k)) (numeric 0) 0);
  Classical.forall_intro_2 #(i:size_nat{i < n3}) #(fun i -> k:size_nat{k < n2})
    #(fun i k -> sum #t n1 (fun j -> mget c i j *. (mget a j k +. mget b j k)) (numeric 0) ==
	       sum #t n1 (fun j -> mget c i j *. mget a j k) (numeric 0) +. sum #t n1 (fun j -> mget c i j *. mget b j k) (numeric 0))
    (fun i k ->
      (matrix_distributivity_add_left_get #t #n1 #n2 #n3 a b c i k) <:
      (Lemma
	(sum #t n1 (fun j -> mget c i j *. (mget a j k +. mget b j k)) (numeric 0) ==
         sum #t n1 (fun j -> mget c i j *. mget a j k) (numeric 0) +. sum #t n1 (fun j -> mget c i j *. mget b j k) (numeric 0))));
  assert (forall (i:size_nat{i < n3}) (k:size_nat{k < n2}).
    sum #t n1 (fun j -> mget c i j *. (mget a j k +. mget b j k)) (numeric 0) ==
    sum #t n1 (fun j -> mget c i j *. mget a j k) (numeric 0) +. sum #t n1 (fun j -> mget c i j *. mget b j k) (numeric 0));
  let r3 = matrix_mul c a in
  let r4 = matrix_mul c b in
  let r5 = matrix_add r3 r4 in
  matrix_equality r2 r5

val mul_assoc:
  #t:numeric_t{t <> U128} -> a:uint_t t -> b:uint_t t -> c:uint_t t ->
  Lemma (a *. b *. c == a *. (b *. c))
  [SMTPat (a *. b *. c)]
  #reset-options "--z3rlimit 50 --max_fuel 0"
let mul_assoc #t a b c =
  let r = a *. b *. c in
  lemma_mod_mul_distr_l (uint_v a * uint_v b) (uint_v c) (modulus t);
  paren_mul_right (uint_v a) (uint_v b) (uint_v c);
  lemma_mod_mul_distr_l (uint_v b * uint_v c) (uint_v a) (modulus t);
  uintv_extensionality (a *. b *. c) (a *. (b *. c))

let matrix_associativity_mul #t #n1 #n2 #n3 #n4 a b c = admit()

val lemma_add_associativity:
  #t:numeric_t -> a:uint_t t -> b:uint_t t -> c:uint_t t -> Lemma
  (requires True)
  (ensures ((a +. b) +. c == a +. (b +. c)))
  [SMTPat ((a +. b) +. c)]
let lemma_add_associativity #q a b c =
  let r = (a +. b) +. c in
  lemma_mod_plus_distr_l (uint_v a + uint_v b) (uint_v c) (modulus q);
  lemma_mod_plus_distr_l (uint_v b + uint_v c) (uint_v a) (modulus q);
  uintv_extensionality ((a +. b) +. c) (a +. (b +. c))

#reset-options "--z3rlimit 50 --max_fuel 0"
let matrix_associativity_add #t #n1 #n2 a b c =
  let r1 = matrix_add a b in
  let r2 = matrix_add r1 c in
  let r3 = matrix_add b c in
  let r4 = matrix_add a r3 in
  matrix_equality r2 r4

val lemma_add_commutativity:
  #t:numeric_t -> a:uint_t t -> b:uint_t t -> Lemma
  (requires True)
  (ensures (a +. b == b +. a))
  [SMTPat (a +. b)]
let lemma_add_commutativity #q a b =
  let r = a +. b in
  uintv_extensionality (a +. b) (b +. a)

let matrix_commutativity_add #t #n1 #n2 a b =
  let r1 = matrix_add a b in
  let r2 = matrix_add b a in
  matrix_equality r1 r2

val lemma_sub_zero:
  #t:numeric_t -> a:uint_t t -> Lemma
  (requires True)
  (ensures (a -. a == numeric #t 0))
  [SMTPat (a -. a)]
let lemma_sub_zero #t a =
  let r = a -. a in
  uintv_extensionality (a -. a) (numeric #t 0)

let matrix_sub_zero #t #n1 #n2 a =
  let r = matrix_sub a a in
  matrix_equality r (matrix_zero #t #n1 #n2)

val lemma_add_zero:
  #t:numeric_t -> a:uint_t t -> Lemma
  (requires True)
  (ensures (a +. numeric #t 0 == a))
  [SMTPat (a +. numeric #t 0)]
let lemma_add_zero #t a =
  let r = a +. numeric #t 0 in
  assert (uint_v r = uint_v a + 0);
  uintv_extensionality (a +. numeric #t 0) a

#reset-options "--z3rlimit 150 --max_fuel 0"
let matrix_add_zero #t #n1 #n2 a =
  let r = matrix_add a (matrix_zero #t #n1 #n2) in
  matrix_equality #t #n1 #n2 r a
