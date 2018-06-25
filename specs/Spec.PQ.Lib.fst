module Spec.PQ.Lib

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open FStar.Math.Lemmas

let zqelem_t q = x:nat{x < q}
let zqelem #q x = x % q
let zqelem_v #q x = x
let zqadd #q a b = zqelem (a + b)
let zqsub #q a b = zqelem (a + q - b)
let zqmul #q a b = zqelem (a * b)

let zqvector_t q n = lseq (zqelem_t q) n
let zqvector_add #q #n a b =
  let c:zqvector_t q n = create n (zqelem #q 0) in
  repeati n
  (fun i c ->
    c.[i] <- zqadd a.[i] b.[i]
  ) c

let zqvector_sub #q #n a b =
  let c:zqvector_t q n = create n (zqelem #q 0) in
  repeati n
  (fun i c ->
    c.[i] <- zqsub a.[i] b.[i]
  ) c

let zqmatrix_t q n m = lseq (zqvector_t q n) m
let zqmatrix_create q n m = create m (create n (zqelem #q 0))

let get #q #n1 #n2 m i j = (m.[j]).[i]

let set #q #n1 #n2 m i j v =   //(m.[j]).[i] <- v
  let mj = m.[j] in
  let mji = mj.[i] <- v in
  m.[j] <- mji

val sum_:
  q:size_pos -> n:size_nat -> f:(j:size_nat{j < n} -> zqelem_t q) ->
  tmp0:zqelem_t q -> i:size_nat{i <= n} -> Tot (zqelem_t q)
  (decreases (n - i))
let rec sum_ q n f tmp0 i =
  if (i < n) then
    sum_ q n f (zqadd tmp0 (f i)) (i + 1)
  else tmp0

let sum q n f tmp0 = sum_ q n f tmp0 0

let zqmatrix_zero #q #n #m = zqmatrix_create q n m

val zqmatrix_pred0:
  #q:size_pos -> #n1:size_pos -> #n2:size_pos -> f:(zqelem_t q -> zqelem_t q -> zqelem_t q) ->
  a:zqmatrix_t q n1 n2 -> b:zqmatrix_t q n1 n2 ->
  i0:size_nat{i0 < n1} -> res0:zqmatrix_t q n1 n2 -> j:size_nat{j <= n2} -> res:zqmatrix_t q n1 n2 -> Tot Type0
let zqmatrix_pred0 #q #n1 #n2 f a b i0 res0 j res =
  (forall (j1:size_nat{j1 < j}). get res i0 j1 = f (get a i0 j1) (get b i0 j1)) /\
  (forall (i:size_nat{i < n1 /\ i <> i0}) (j:size_nat{j < n2}). get res0 i j = get res i j)

val zqmatrix_f0:
  #q:size_pos -> #n1:size_pos -> #n2:size_pos -> f:(zqelem_t q -> zqelem_t q -> zqelem_t q) ->
  a:zqmatrix_t q n1 n2 -> b:zqmatrix_t q n1 n2 ->
  i0:size_nat{i0 < n1} -> res0:zqmatrix_t q n1 n2 -> Tot (repeatable #(zqmatrix_t q n1 n2) #n2 (zqmatrix_pred0 #q #n1 #n2 f a b i0 res0))
let zqmatrix_f0 #q #n1 #n2 f a b i0 res0 j c = set c i0 j (f (get a i0 j) (get b i0 j))

val zqmatrix_pred1:
  #q:size_pos -> #n1:size_pos -> #n2:size_pos -> f:(zqelem_t q -> zqelem_t q -> zqelem_t q) ->
  a:zqmatrix_t q n1 n2 -> b:zqmatrix_t q n1 n2 ->
  i:size_nat{i <= n1} -> res:zqmatrix_t q n1 n2 -> Tot Type0
let zqmatrix_pred1 #q #n1 #n2 f a b i res = forall (i1:size_nat{i1 < i}) (j:size_nat{j < n2}). get res i1 j == f (get a i1 j) (get b i1 j)

val zqmatrix_f1:
  #q:size_pos -> #n1:size_pos -> #n2:size_pos -> f:(zqelem_t q -> zqelem_t q -> zqelem_t q) ->
  a:zqmatrix_t q n1 n2 -> b:zqmatrix_t q n1 n2 ->
  Tot (repeatable #(zqmatrix_t q n1 n2) #n1 (zqmatrix_pred1 #q #n1 #n2 f a b))
let zqmatrix_f1 #q #n1 #n2 f a b i c =
  let res =
    repeati_inductive n2
    (zqmatrix_pred0 #q #n1 #n2 f a b i c)
    (fun j cj -> zqmatrix_f0 #q #n1 #n2 f a b i c j cj) c in
  res

let zqmatrix_add #q #n1 #n2 a b =
  let c = zqmatrix_create q n1 n2 in
  repeati_inductive n1
  (zqmatrix_pred1 #q #n1 #n2 zqadd a b)
  (fun i c -> zqmatrix_f1 #q #n1 #n2 zqadd a b i c) c

let zqmatrix_sub #q #n1 #n2 a b =
  let c = zqmatrix_create q n1 n2 in
  repeati_inductive n1
  (zqmatrix_pred1 #q #n1 #n2 zqsub a b)
  (fun i c -> zqmatrix_f1 #q #n1 #n2 zqsub a b i c) c

val zqmatrix_mul_pred0:
  #q:size_pos -> #n1:size_pos -> #n2:size_pos -> #n3:size_pos ->
  a:zqmatrix_t q n1 n2 -> b:zqmatrix_t q n2 n3 ->
  i0:size_nat{i0 < n1} -> res0:zqmatrix_t q n1 n3 -> k:size_nat{k <= n3} -> res:zqmatrix_t q n1 n3 -> Tot Type0
let zqmatrix_mul_pred0 #q #n1 #n2 #n3 a b i0 res0 k res =
  (forall (k1:size_nat{k1 < k}). get res i0 k1 = sum q n2 (fun j -> zqmul (get a i0 j) (get b j k1)) (zqelem #q 0)) /\
  (forall (i:size_nat{i < n1 /\ i <> i0}) (k:size_nat{k < n3}). get res0 i k = get res i k)

val zqmatrix_mul_f0:
  #q:size_pos -> #n1:size_pos -> #n2:size_pos -> #n3:size_pos ->
  a:zqmatrix_t q n1 n2 -> b:zqmatrix_t q n2 n3 ->
  i0:size_nat{i0 < n1} -> res0:zqmatrix_t q n1 n3 -> Tot (repeatable #(zqmatrix_t q n1 n3) #n3 (zqmatrix_mul_pred0 #q #n1 #n2 #n3 a b i0 res0))
let zqmatrix_mul_f0 #q #n1 #n2 #n3 a b i0 res0 k c = set c i0 k (sum q n2 (fun j -> zqmul (get a i0 j) (get b j k)) (zqelem #q 0))

val zqmatrix_mul_pred1:
  #q:size_pos -> #n1:size_pos -> #n2:size_pos -> #n3:size_pos ->
  a:zqmatrix_t q n1 n2 -> b:zqmatrix_t q n2 n3 ->
  i:size_nat{i <= n1} -> res:zqmatrix_t q n1 n3 -> Tot Type0
let zqmatrix_mul_pred1 #q #n1 #n2 #n3 a b i res =
  forall (i1:size_nat{i1 < i}) (k:size_nat{k < n3}). get res i1 k == sum q n2 (fun j -> zqmul (get a i1 j) (get b j k)) (zqelem #q 0)

val zqmatrix_mul_f1:
  #q:size_pos -> #n1:size_pos -> #n2:size_pos -> #n3:size_pos ->
  a:zqmatrix_t q n1 n2 -> b:zqmatrix_t q n2 n3 ->
  Tot (repeatable #(zqmatrix_t q n1 n3) #n1 (zqmatrix_mul_pred1 #q #n1 #n2 #n3 a b))
let zqmatrix_mul_f1 #q #n1 #n2 #n3 a b i c =
  let res =
    repeati_inductive n3
    (zqmatrix_mul_pred0 #q #n1 #n2 #n3 a b i c)
    (fun k ck -> zqmatrix_mul_f0 #q #n1 #n2 #n3 a b i c k ck) c in
  res

let zqmatrix_mul #q #n1 #n2 #n3 a b =
  let c = zqmatrix_create q n1 n3 in
  repeati_inductive n1
  (zqmatrix_mul_pred1 #q #n1 #n2 #n3 a b)
  (fun i c -> zqmatrix_mul_f1 #q #n1 #n2 #n3 a b i c) c

(* Lemmas about the sum function *)
val sum_linearity:
  q:size_pos -> n:size_nat ->
  f:(i:size_nat{i < n} -> zqelem_t q) -> tmp0:zqelem_t q ->
  g:(i:size_nat{i < n} -> zqelem_t q) -> tmp1:zqelem_t q ->
  i:size_nat{i <= n} -> Lemma
  (requires True)
  (ensures (zqadd (sum_ q n f tmp0 i) (sum_ q n g tmp1 i) == sum_ q n (fun j -> zqadd (f j) (g j)) (zqadd tmp0 tmp1) i))
  (decreases (n - i))
  #reset-options "--z3rlimit 50 --max_fuel 1"
let rec sum_linearity q n f tmp0 g tmp1 i =
  if (i < n) then begin
    //assert (zqelem_v (zqadd (zqadd tmp0 (f i)) (zqadd tmp1 (g i))) == ((zqelem_v tmp0 + zqelem_v (f i)) % q + (zqelem_v tmp1 + zqelem_v (g i)) % q) % q);
    modulo_distributivity (zqelem_v tmp0 + zqelem_v (f i)) (zqelem_v tmp1 + zqelem_v (g i)) q;
    modulo_distributivity (zqelem_v tmp0 + zqelem_v tmp1) (zqelem_v (f i) + zqelem_v (g i)) q;
    sum_linearity q n f (zqadd tmp0 (f i)) g (zqadd tmp1 (g i)) (i + 1) end
  else ()

val sum_extensionality:
  q:size_pos -> n:size_nat ->
  f:(i:size_nat{i < n} -> zqelem_t q) ->
  g:(i:size_nat{i < n} -> zqelem_t q) ->
  tmp0:zqelem_t q -> i:size_nat{i <= n} -> Lemma
  (requires (forall (i:size_nat{i < n}). f i == g i))
  (ensures (sum_ q n f tmp0 i == sum_ q n g tmp0 i))
  (decreases (n - i))
  #reset-options "--z3rlimit 50 --max_fuel 1"
let rec sum_extensionality q n f g tmp0 i =
  if (i < n) then
    sum_extensionality q n f g (zqadd tmp0 (f i)) (i + 1)
  else ()

val sum_mul_scalar:
  q:size_pos -> n:size_nat ->
  f:(i:size_nat{i < n} -> zqelem_t q) -> tmp0:zqelem_t q ->
  sc:zqelem_t q -> i:size_nat{i <= n} -> Lemma
  (requires True)
  (ensures (zqmul (sum_ q n f tmp0 i) sc == sum_ q n (fun j -> zqmul (f j) sc) (zqmul tmp0 sc) i))
  (decreases (n - i))
  #reset-options "--z3rlimit 50 --max_fuel 1"
let rec sum_mul_scalar q n f tmp0 sc i =
  if (i < n) then begin
    //assume (zqadd (zqmul tmp0 sc) (zqmul sc (f i)) = zqmul sc (zqadd tmp0 (f i)));
    lemma_mod_mul_distr_l (zqelem_v tmp0 + zqelem_v (f i)) (zqelem_v sc) q;
    distributivity_add_left (zqelem_v tmp0) (zqelem_v (f i)) (zqelem_v sc);
    modulo_distributivity (zqelem_v tmp0 * zqelem_v sc) (zqelem_v (f i) * zqelem_v sc) q;
    sum_mul_scalar q n f (zqadd tmp0 (f i)) sc (i + 1) end
  else ()

// // let rec sum_ q n f tmp0 i =
// //   if (i < n) then
// //     sum_ q n f (zqadd tmp0 (f i)) (i + 1)
// //   else tmp0

// val sum_fubini:
//   q:size_pos -> n1:size_nat -> n2:size_nat ->
//   f:(i:size_nat{i < n1} -> j:size_nat{j < n2} -> zqelem_t q) ->
//   tmp0:zqelem_t q -> k:size_nat{k <= n1} -> Lemma
//   (requires True)
//   (ensures (sum_ q n1 (fun i -> sum_ q n2 (fun j -> f i j) tmp0 0) (zqelem 0) k == sum_ q n2 (fun j -> sum_ q n1 (fun i -> f i j) tmp0 k) (zqelem 0) 0))
//   (decreases (n1 - k))
//   #reset-options "--z3rlimit 50 --max_fuel 1"
// let rec sum_fubini q n1 n2 f tmp0 k =
//   if (k < n1) then begin
//     //assert (sum_ q n1 (fun i -> sum_ q n2 (fun j -> f i j) tmp0 n2) tmp0 i == sum_ q n1 (fun i -> sum_ q n2 (fun j -> f i j) tmp0 n2) (zqadd tmp0 (sum_ q n2 (fun j -> f i j) tmp0 n2)) (i + 1));
//     //sum_extensionality q n2 (fun j -> sum_ q n1 (fun i -> f i j) tmp0 i) (fun j -> sum_ q n1 (fun i -> f i j) (zqadd tmp0 (f i j)) (i + 1)) tmp0 n2;
//     //assert (sum_ q n2 (fun j -> sum_ q n1 (fun i -> f i j) tmp0 i) tmp0 n2 == sum_ q n2 (fun j -> sum_ q n1 (fun i -> f i j) (zqadd tmp0 (sum_ q n2 (fun j -> f i j) tmp0 n2)) i) tmp0 n2);
//    // sum_fubini q n1 n2 f (zqadd tmp0 (sum_ q n2 (fun j -> f i j) tmp0 n2)) (i + 1);
//     //assert (sum_ q n1 (fun i -> sum_ q n2 (fun j -> f i j) (zqadd tmp0 (sum_ q n2 (fun j -> f i j) tmp0 n2)) n2) tmp0 i == sum_ q n2 (fun j -> sum_ q n1 (fun i -> f i j) tmp0 i) tmp0 n2)
//     admit() end
//   else begin
//     assert (sum_ q n1 (fun i -> sum_ q n2 (fun j -> f i j) tmp0 0) (zqelem 0) k = zqelem 0);
//     assert (sum_ q n2 (fun j -> sum_ q n1 (fun i -> f i j) tmp0 k) (zqelem 0) 0 = sum_ q n2 (fun j -> tmp0) (zqelem 0) 0);
//     admit()
//   end

//   // assume (sum q n3 (fun j -> sum q n2 (fun l -> zqmul (get a i l) (zqmul (get b l j) (get c j k))) (zqelem 0)) (zqelem 0) ==
//   // 	     sum q n2 (fun l -> sum q n3 (fun j -> zqmul (get a i l) (zqmul (get b l j) (get c j k))) (zqelem 0)) (zqelem 0));


(* Lemmas *)
// assume val zqmatrix_create_f:
//   q:size_pos -> n:size_pos -> m:size_pos ->
//   f:(i:size_nat{i < n} -> j:size_nat{j < m} -> zqelem_t q) ->
//   Tot (r:zqmatrix_t q n m{forall (i:size_nat{i < n}) (j:size_nat{j < m}).{:pattern get r i j} get r i j == f i j})

// assume val matrix_extensionality:
//   #q:size_pos -> #n1:size_pos -> #n2:size_pos ->
//   f:(i:size_nat{i < n1} -> j:size_nat{j < n2} -> zqelem_t q) ->
//   g:(i:size_nat{i < n1} -> j:size_nat{j < n2} -> zqelem_t q) -> Lemma
//   (requires (forall (i:size_nat{i < n1}) (j:size_nat{j < n2}). f i j == g i j))
//   (ensures (zqmatrix_create_f q n1 n2 f == zqmatrix_create_f q n1 n2 g))

val matrix_equality:
  #q:size_pos -> #n1:size_pos -> #n2:size_pos ->
  a:zqmatrix_t q n1 n2 -> b:zqmatrix_t q n1 n2 -> Lemma
  (requires (forall (i:size_nat{i < n1}) (j:size_nat{j < n2}). get a i j == get b i j))
  (ensures  (a == b))
let matrix_equality #q #n1 #n2 a b = admit()

val zqadd_distr_right:
  #q:size_pos -> a:zqelem_t q -> b:zqelem_t q -> c:zqelem_t q -> Lemma
  (requires True)
  (ensures (zqmul (zqadd a b) c == zqadd (zqmul a c) (zqmul b c)))
  [SMTPat (zqadd (zqmul a c) (zqmul b c))]
let zqadd_distr_right #q a b c =
  let r = zqmul (zqadd a b) c in
  lemma_mod_mul_distr_l (zqelem_v a + zqelem_v b) (zqelem_v c) q;
  distributivity_add_left (zqelem_v a) (zqelem_v b) (zqelem_v c);
  modulo_distributivity (zqelem_v a * zqelem_v c) (zqelem_v b * zqelem_v c) q

val matrix_distributivity_add_right_get:
  #q:size_pos -> #n1:size_pos -> #n2:size_pos -> #n3:size_pos ->
  a:zqmatrix_t q n1 n2 -> b:zqmatrix_t q n1 n2 -> c:zqmatrix_t q n2 n3 ->
  i:size_nat{i < n1} -> k:size_nat{k < n3} -> Lemma
  (requires True)
  (ensures ( sum q n2 (fun j -> zqmul (zqadd (get a i j) (get b i j)) (get c j k)) (zqelem 0) ==
             zqadd (sum q n2 (fun j -> zqmul (get a i j) (get c j k)) (zqelem 0)) (sum q n2 (fun j -> zqmul (get b i j) (get c j k)) (zqelem 0))))
  [SMTPat (sum q n2 (fun j -> zqmul (zqadd (get a i j) (get b i j)) (get c j k)) (zqelem 0))]
  #reset-options "--z3rlimit 50 --max_fuel 0"
let matrix_distributivity_add_right_get #q #n1 #n2 #n3 a b c i k =
  sum_linearity q n2 (fun j -> zqmul (get a i j) (get c j k)) (zqelem 0) (fun j -> zqmul (get b i j) (get c j k)) (zqelem 0) 0;
  sum_extensionality q n2 (fun j -> zqadd (zqmul (get a i j) (get c j k)) (zqmul (get b i j) (get c j k))) (fun j -> zqmul (zqadd (get a i j) (get b i j)) (get c j k)) (zqelem 0) 0

#reset-options "--z3rlimit 50 --max_fuel 0"
let matrix_distributivity_add_right #q #n1 #n2 #n3 a b c =
  let r1 = zqmatrix_add a b in
  let r2 = zqmatrix_mul r1 c in
  assume (forall (i:size_nat{i < n1}) (k:size_nat{k < n3}). get r2 i k == sum q n2 (fun j -> zqmul (zqadd (get a i j) (get b i j)) (get c j k)) (zqelem 0));
  assume (forall (i:size_nat{i < n1}) (k:size_nat{k < n3}). sum q n2 (fun j -> zqmul (zqadd (get a i j) (get b i j)) (get c j k)) (zqelem 0) ==
	  zqadd (sum q n2 (fun j -> zqmul (get a i j) (get c j k)) (zqelem 0)) (sum q n2 (fun j -> zqmul (get b i j) (get c j k)) (zqelem 0)));
  let r3 = zqmatrix_mul a c in
  let r4 = zqmatrix_mul b c in
  let r5 = zqmatrix_add r3 r4 in
  matrix_equality r2 r5

val zqadd_distr_left:
  #q:size_pos -> a:zqelem_t q -> b:zqelem_t q -> c:zqelem_t q -> Lemma
  (requires True)
  (ensures (zqmul c (zqadd a b) == zqadd (zqmul c a) (zqmul c b)))
  [SMTPat (zqadd (zqmul c a) (zqmul c b))]
let zqadd_distr_left #q a b c =
  let r = zqmul c (zqadd a b) in
  lemma_mod_mul_distr_l (zqelem_v a + zqelem_v b) (zqelem_v c) q;
  distributivity_add_right (zqelem_v c) (zqelem_v a) (zqelem_v b);
  modulo_distributivity (zqelem_v c * zqelem_v a) (zqelem_v c * zqelem_v b) q

val matrix_distributivity_add_left_get:
  #q:size_pos -> #n1:size_pos -> #n2:size_pos -> #n3:size_pos ->
  a:zqmatrix_t q n1 n2 -> b:zqmatrix_t q n1 n2 -> c:zqmatrix_t q n3 n1 ->
  i:size_nat{i < n3} -> k:size_nat{k < n2} -> Lemma
  (requires True)
  (ensures (sum q n1 (fun j -> zqmul (get c i j) (zqadd (get a j k) (get b j k))) (zqelem 0) ==
             zqadd (sum q n1 (fun j -> zqmul (get c i j) (get a j k)) (zqelem 0)) (sum q n1 (fun j -> zqmul (get c i j) (get b j k)) (zqelem 0))))
  #reset-options "--z3rlimit 100 --max_fuel 0"
let matrix_distributivity_add_left_get #q #n1 #n2 #n3 a b c i k =
  sum_linearity q n1 (fun j -> zqmul (get c i j) (get a j k)) (zqelem 0) (fun j -> zqmul (get c i j) (get b j k)) (zqelem 0) 0;
  sum_extensionality q n1 (fun j -> zqadd (zqmul (get c i j) (get a j k)) (zqmul (get c i j) (get b j k))) (fun j -> zqmul (get c i j) (zqadd (get a j k) (get b j k))) (zqelem 0) 0

let matrix_distributivity_add_left #q #n1 #n2 #n3 a b c =
  let r1 = zqmatrix_add a b in
  let r2 = zqmatrix_mul c r1 in
  assume (forall (i:size_nat{i < n3}) (k:size_nat{k < n2}). get r2 i k == sum q n1 (fun j -> zqmul (get c i j) (zqadd (get a j k) (get b j k))) (zqelem 0));
  assume (forall (i:size_nat{i < n3}) (k:size_nat{k < n2}). sum q n1 (fun j -> zqmul (get c i j) (zqadd (get a j k) (get b j k))) (zqelem 0) ==
	 zqadd (sum q n1 (fun j -> zqmul (get c i j) (get a j k)) (zqelem 0)) (sum q n1 (fun j -> zqmul (get c i j) (get b j k)) (zqelem 0)));
  let r3 = zqmatrix_mul c a in
  let r4 = zqmatrix_mul c b in
  let r5 = zqmatrix_add r3 r4 in
  matrix_equality r2 r5

// val matrix_associativity_mul:
//   #q:size_pos -> #n1:size_pos -> #n2:size_pos -> #n3:size_pos -> #n4:size_pos ->
//   a:zqmatrix_t q n1 n2 -> b:zqmatrix_t q n2 n3 -> c:zqmatrix_t q n3 n4 -> Lemma
//   (zqmatrix_mul (zqmatrix_mul a b) c == zqmatrix_mul a (zqmatrix_mul b c))

// zqmul (sum_ q n f tmp0 i) sc == sum_ q n (fun j -> zqmul sc (f j)) (zqmul tmp0 sc) i))
// let rec sum_mul_scalar q n f tmp0 sc i =

val zqmul_assoc:
  #q:size_pos -> a:zqelem_t q -> b:zqelem_t q -> c:zqelem_t q ->
  Lemma (zqmul (zqmul a b) c == zqmul a (zqmul b c))
  [SMTPat (zqmul (zqmul a b) c)]
let zqmul_assoc #q a b c = admit()

val matrix_associativity_mul_get0:
  #q:size_pos -> #n1:size_pos -> #n2:size_pos -> #n3:size_pos -> #n4:size_pos ->
  a:zqmatrix_t q n1 n2 -> b:zqmatrix_t q n2 n3 -> c:zqmatrix_t q n3 n4 ->
  i:size_nat{i < n1} -> k:size_nat{k < n4} -> j:size_nat{j < n3} -> Lemma
  (requires True)
  (ensures (zqmul (sum q n2 (fun l -> zqmul (get a i l) (get b l j)) (zqelem 0)) (get c j k) ==
            sum q n2 (fun l -> zqmul (get a i l) (zqmul (get b l j) (get c j k))) (zqelem 0)))
  #reset-options "--z3rlimit 50 --max_fuel 0"
let matrix_associativity_mul_get0 #q #n1 #n2 #n3 #n4 a b c i k j =
  sum_mul_scalar q n2 (fun l -> zqmul (get a i l) (get b l j)) (zqelem 0) (get c j k) 0;
  assert (zqmul (sum q n2 (fun l -> zqmul (get a i l) (get b l j)) (zqelem 0)) (get c j k) == sum q n2 (fun l -> zqmul (zqmul (get a i l) (get b l j)) (get c j k)) (zqelem 0));
  assume (zqmul (sum q n2 (fun l -> zqmul (get a i l) (get b l j)) (zqelem 0)) (get c j k) == sum q n2 (fun l -> zqmul (get a i l) (zqmul (get b l j) (get c j k))) (zqelem 0))

val matrix_associativity_mul_get1:
  #q:size_pos -> #n1:size_pos -> #n2:size_pos -> #n3:size_pos -> #n4:size_pos ->
  a:zqmatrix_t q n1 n2 -> b:zqmatrix_t q n2 n3 -> c:zqmatrix_t q n3 n4 ->
  i:size_nat{i < n1} -> k:size_nat{k < n4} -> l:size_nat{l < n2} -> Lemma
  (requires True)
  (ensures (sum q n3 (fun j -> zqmul (get a i l) (zqmul (get b l j) (get c j k))) (zqelem 0) ==
	   zqmul (get a i l) (sum q n3 (fun j -> zqmul (get b l j) (get c j k)) (zqelem 0))))
  #reset-options "--z3rlimit 50 --max_fuel 0"
let matrix_associativity_mul_get1 #q #n1 #n2 #n3 #n4 a b c i k l =
  sum_mul_scalar q n3 (fun j -> zqmul (get b l j) (get c j k)) (zqelem 0) (get a i l) 0;
  //assert (sum q n3 (fun j -> zqmul (zqmul (get b l j) (get c j k)) (get a i l)) (zqelem 0) == zqmul (sum q n3 (fun j -> zqmul (get b l j) (get c j k)) (zqelem 0)) (get a i l));
  assume (sum q n3 (fun j -> zqmul (get a i l) (zqmul (get b l j) (get c j k))) (zqelem 0) == zqmul (get a i l) (sum q n3 (fun j -> zqmul (get b l j) (get c j k)) (zqelem 0)))

val matrix_associativity_mul_get:
  #q:size_pos -> #n1:size_pos -> #n2:size_pos -> #n3:size_pos -> #n4:size_pos ->
  a:zqmatrix_t q n1 n2 -> b:zqmatrix_t q n2 n3 -> c:zqmatrix_t q n3 n4 ->
  i:size_nat{i < n1} -> k:size_nat{k < n4} -> Lemma
  (requires True)
  (ensures (sum q n3 (fun j -> zqmul (sum q n2 (fun l -> zqmul (get a i l) (get b l j)) (zqelem 0)) (get c j k)) (zqelem 0) ==
            sum q n2 (fun l -> zqmul (get a i l) (sum q n3 (fun j -> zqmul (get b l j) (get c j k)) (zqelem 0))) (zqelem 0)))
let matrix_associativity_mul_get #q #n1 #n2 #n3 #n4 a b c i k =
  // sum_extensionality q n3 (fun j -> zqmul (sum q n2 (fun l -> zqmul (get a i l) (get b l j)) (zqelem 0)) (get c j k))
  // 			  (fun j -> sum q n2 (fun l -> zqmul (get a i l) (zqmul (get b l j) (get c j k))) (zqelem 0)) (zqelem 0) 0;
  assume (sum q n3 (fun j -> zqmul (sum q n2 (fun l -> zqmul (get a i l) (get b l j)) (zqelem 0)) (get c j k)) (zqelem 0) ==
	  sum q n3 (fun j -> sum q n2 (fun l -> zqmul (get a i l) (zqmul (get b l j) (get c j k))) (zqelem 0)) (zqelem 0));
  assume (sum q n3 (fun j -> sum q n2 (fun l -> zqmul (get a i l) (zqmul (get b l j) (get c j k))) (zqelem 0)) (zqelem 0) ==
	  sum q n2 (fun l -> sum q n3 (fun j -> zqmul (get a i l) (zqmul (get b l j) (get c j k))) (zqelem 0)) (zqelem 0));
  // sum_extensionality q n3 (fun l -> sum q n3 (fun j -> zqmul (get a i l) (zqmul (get b l j) (get c j k))) (zqelem 0))
  //  			  (fun l -> zqmul (get a i l) (sum q n3 (fun j -> zqmul (get b l j) (get c j k)) (zqelem 0))) (zqelem 0) 0;
  assume (sum q n2 (fun l -> sum q n3 (fun j -> zqmul (get a i l) (zqmul (get b l j) (get c j k))) (zqelem 0)) (zqelem 0) ==
	  sum q n2 (fun l -> zqmul (get a i l) (sum q n3 (fun j -> zqmul (get b l j) (get c j k)) (zqelem 0))) (zqelem 0))

let matrix_associativity_mul #q #n1 #n2 #n3 #n4 a b c =
  let r1 = zqmatrix_mul a b in
  //assert (forall (i:size_nat{i < n1}) (j:size_nat{j < n3}). get r1 i j == sum q n2 (fun l -> zqmul (get a i l) (get b l j)) (zqelem 0));
  let r2 = zqmatrix_mul r1 c in
  //assert (forall (i:size_nat{i < n1}) (k:size_nat{k < n4}). get r2 i k == sum q n3 (fun j -> zqmul (get r1 i j) (get c j k)) (zqelem 0));
  assume (forall (i:size_nat{i < n1}) (k:size_nat{k < n4}). get r2 i k == sum q n3 (fun j -> zqmul (sum q n2 (fun l -> zqmul (get a i l) (get b l j)) (zqelem 0)) (get c j k)) (zqelem 0));
  assume (forall (i:size_nat{i < n1}) (k:size_nat{k < n4}). sum q n3 (fun j -> zqmul (sum q n2 (fun l -> zqmul (get a i l) (get b l j)) (zqelem 0)) (get c j k)) (zqelem 0) ==
	 sum q n2 (fun l -> zqmul (get a i l) (sum q n3 (fun j -> zqmul (get b l j) (get c j k)) (zqelem 0))) (zqelem 0));
  let r3 = zqmatrix_mul b c in
  let r4 = zqmatrix_mul a r3 in
  assume (forall (i:size_nat{i < n1}) (k:size_nat{k < n4}). get r4 i k == sum q n2 (fun l -> zqmul (get a i l) (sum q n3 (fun j -> zqmul (get b l j) (get c j k)) (zqelem 0))) (zqelem 0));
  matrix_equality r2 r4

val lemma_zqadd_associativity:
  #q:size_pos -> a:zqelem_t q -> b:zqelem_t q -> c:zqelem_t q -> Lemma
  (requires True)
  (ensures (zqadd (zqadd a b) c == zqadd a (zqadd b c)))
  [SMTPat (zqadd (zqadd a b) c)]
let lemma_zqadd_associativity #q a b c =
  let r = zqadd (zqadd a b) c in
  lemma_mod_plus_distr_l (zqelem_v a + zqelem_v b) (zqelem_v c) q;
  lemma_mod_plus_distr_l (zqelem_v b + zqelem_v c) (zqelem_v a) q

#reset-options "--z3rlimit 50 --max_fuel 0"
let matrix_associativity_add #q #n1 #n2 a b c =
  let r1 = zqmatrix_add a b in
  let r2 = zqmatrix_add r1 c in
  let r3 = zqmatrix_add b c in
  let r4 = zqmatrix_add a r3 in
  matrix_equality r2 r4

let matrix_commutativity_add #q #n1 #n2 a b =
  let r1 = zqmatrix_add a b in
  let r2 = zqmatrix_add b a in
  matrix_equality r1 r2

let matrix_sub_zero #q #n1 #n2 a =
  let r = zqmatrix_sub a a in
  matrix_equality r (zqmatrix_zero #q #n1 #n2)

#reset-options "--z3rlimit 50 --max_fuel 0"
let matrix_add_zero #q #n1 #n2 a =
  let r = zqmatrix_add a (zqmatrix_zero #q #n1 #n2) in
  matrix_equality #q #n1 #n2 r a
