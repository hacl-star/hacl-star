module Spec.BarrettReduction

open FStar.Mul

(*
  Barrett modular reduction:

  let reduce a =
    let q = (a * m) >> k in
    let a = a - q * n in
    if n <= a then a - n else a

  compute a % n where:
  - n = 2^252 + 27742317777372353535851937790883648493
  - k = 33 * 8 = 264
  - m = floor ( 2^k / L )

*)

#set-options "--max_fuel 0 --max_ifuel 0"

let l =
  assert_norm(0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed = pow2 252 +  27742317777372353535851937790883648493);
  0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed
let k = 512
let pow2k : p:nat{p = pow2 512} =
  assert_norm(0x100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = pow2 512);
  0x100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
let m :m:pos{m = pow2 k / l} =
  assert_norm(pow2 512 / 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed
  = 0xfffffffffffffffffffffffffffffffeb2106215d086329a7ed9ce5a30a2c131b);
  0xfffffffffffffffffffffffffffffffeb2106215d086329a7ed9ce5a30a2c131b

let barrett_reduce (a:nat{a < l * l}) : Tot (b:nat{b < l}) =
  let q = (a * m) / pow2k in
  let a = a - q * l in
  if l <= a then a - l else a

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 50"


let p (x:nat{x < l * l}) = (x - ((x * m) / pow2k) * l) % l
let q (x:nat{x < l * l}) = ((x % pow2 264) - (((((x / pow2 248) * m) / pow2 264) * l) % pow2 264)) % l

let test () =
  assert_norm (0x3456781970987134091834079183409813049813740931409870198370987409879999999902938473920 < l * l);
  assert_norm (p (0x3456781970987134091834079183409813049813740931409870198370987409879999999902938473920)
              == q (0x3456781970987134091834079183409813049813740931409870198370987409879999999902938473920))

val lemma_barrett_reduce:
  a:nat{a < l * l} ->
  Lemma (barrett_reduce a = a % l)
let lemma_barrett_reduce a =
  assert_norm(((l * l) * (l - 1) + (pow2k - 1) * l) / pow2k < 2 * l);
  let q = (m * a) / pow2k in
  Math.Lemmas.modulo_lemma (barrett_reduce a) l;
  let a' = a - q * l in
  cut (a' = a - ((a * (pow2k / l)) / pow2k) * l);
  cut (0 <= a');
  cut (a' % l = a % l);
  Math.Lemmas.distributivity_sub_right pow2k a (((a * (pow2k / l)) / pow2k) * l);
  cut (pow2k * a' = pow2k * a - (pow2k * ((a * (pow2k / l)) / pow2k)) * l);
  Math.Lemmas.lemma_div_mod (a * (pow2k / l)) pow2k;
  cut (pow2k * a' = pow2k * a - ((a * (pow2k / l)) - ((a * (pow2k / l)) % pow2k)) * l);
  Math.Lemmas.distributivity_sub_left (a * (pow2k / l)) ((a * (pow2k / l)) % pow2k) l;
  cut (pow2k * a' = pow2k * a - (a * (pow2k / l)) * l + ((a * (pow2k / l)) % pow2k) * l);
  cut (pow2k * a' <= pow2k * a - (a * (pow2k / l)) * l + (pow2k - 1) * l);
  cut (pow2k * a - (a * (pow2k / l)) * l + (pow2k - 1) * l = a * pow2k - a * ((pow2k / l) * l) + (pow2k - 1) * l);
  Math.Lemmas.distributivity_sub_right a pow2k ((pow2k / l) * l);
  Math.Lemmas.lemma_div_mod pow2k l;
  cut (pow2k * a - (a * (pow2k / l)) * l + (pow2k - 1) * l = a * (pow2k % l) + (pow2k - 1) * l);
  cut (pow2k * a - (a * (pow2k / l)) * l + (pow2k - 1) * l <= a * (l - 1) + (pow2k - 1) * l);
  cut (pow2k * a - (a * (pow2k / l)) * l + (pow2k - 1) * l <= (l * l) * (l - 1) + (pow2k - 1) * l);
  cut (a' <= ((l * l) * (l - 1) + (pow2k - 1) * l) / pow2k);
  cut (a' <= 2 * l)

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 10"

private let lemma_mul_div (a:nat) (b:nat) (c:pos) : Lemma ( (a*b) / c = (a / c) * b + ((a % c) * b) / c)
 = let open FStar.Math.Lemmas in
   lemma_div_mod a c;
   distributivity_add_left (c * (a / c)) (a % c) b;
   cut ((a * b) / c = (c * (a / c) * b + (a % c) * b) / c);
   multiple_division_lemma ((a/c)*b) c;
   division_definition ((c * (a / c) * b + (a % c) * b)) c (((a%c) * b) / c + b*(a / c))

private 
val lemma_optimized_barrett_reduce:
  a:nat{a < l * l} ->
  Lemma (a - (((a / pow2 248) * m) / pow2 264) * l < 2 * l
    /\ a - (((a / pow2 248) * m) / pow2 264) * l >= 0)
let lemma_optimized_barrett_reduce a =
  assert_norm (pow2 248 = 0x100000000000000000000000000000000000000000000000000000000000000);
  assert_norm (pow2 264 = 0x1000000000000000000000000000000000000000000000000000000000000000000)  


#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

private
let lemma_mod_sub_ (a:nat) (b:pos{b <= a}) : Lemma ((a - b) % b = a % b) =
  Math.Lemmas.lemma_mod_plus (a-b) 1 b

private
let lemma_mod_sub (a:nat) (b:pos) : Lemma ((a - b) % b = a % b) =
  if a >= b then  lemma_mod_sub_ a b
  else if -(a-b) < b then (
    Math.Lemmas.lemma_mod_sub_1 (b-a) b;
    cut (((a - b)) % b = b - ((b-a)%b)));
    lemma_mod_sub_
    lemma_mod_sub_ (-a) b
  )

private 
let lemma_mod_sub_distr (a:nat) (b:nat{b <= a}) (c:pos) : 
  Lemma ((a - b) % c = ((a % c) - (b % c)) % c)
  = let open FStar.Math.Lemmas in
    lemma_div_mod a c;
    lemma_div_mod b c;
    cut ((a - b) % c = (c * (a/c) + (a%c) - c * (b/c) - (b%c)) % c);
    lemma_div_le b a c;
    distributivity_add_right c (a / c) (b / c);
    (* cut ((a - b) % c = (c * (a/c) + (a%c) - c * (b/c) - (b%c)) % c); *)
    lemma_mod_plus ((a%c) - (b%c)) (a/c - b/c) c


let barrett_reduce_2 (a:nat{a < l * l}) : Tot (b:nat{b < 2 * l}) =
  let q = ((a / pow2 248) * m) / pow2 264 in
  let a' = (a % pow2 264) - (q * l) % pow2 264 in
  lemma_optimized_barrett_reduce a;
  Math.Lemmas.lemma_mod_p
  assert_norm (pow2 264 = 0x1000000000000000000000000000000000000000000000000000000000000000000);
  Math.Lemmas.modulo_lemma (a - q * l) (pow2 264);
  cut ( a - ((a * m) / pow2k) * l < 2 * l);
  Math.Lemmas.modulo_lemma (a - ((a * m) / pow2k) * l) (pow2 264);
  Math.Lemmas.lemma_mod_plus_distr_l a (q * l) (pow2 264);
  Math.Lemmas.lemma_mod_plus_distr_l (q * l) (a % pow2 264) (pow2 264);
  Math.Lemmas.lemma_mod_plus_distr_l a (((a*m)/pow2k) * l) (pow2 264);
  Math.Lemmas.lemma_mod_plus_distr_l (((a*m)/pow2k) * l) (a % pow2 264) (pow2 264);
  (* lemma_barrett_reduce a; *)
  if l <= a' then a' - l else a'
