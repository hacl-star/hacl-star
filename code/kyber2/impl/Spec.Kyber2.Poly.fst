module Spec.Kyber2.Poly

open FStar.Mul
open FStar.IO

open Spec.Kyber2.Params
open Spec.Powtwo.Lemmas
open Spec.Kyber2.Lemmas
open Lib.Poly
open Lib.Poly.NTT2
open Lib.NumericTypes

open Lib.Arithmetic.Group
open Lib.Arithmetic.Ring
open Lib.Arithmetic.Sums
open Spec.Kyber2.Group
open Spec.Kyber2.Ring
open Spec.Kyber2.Reduce

open Lib.Sequence
open Lib.ByteSequence
open Lib.IntTypes
open Lib.NumericTypes

open Lib.ModularArithmetic
open Lib.ModularArithmetic.Lemmas

open Spec.Kyber2.FunctionInstantiation
open Spec.Kyber2.CBD

open FStar.Math.Lemmas

module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators

type num_t = Base Group.t
type poly_t = vector_t #num_t params_n
type vec_t = vector_t #poly_t params_k
type matrix_t = matrix_t #poly_t params_k params_k

type num = Group.t
type poly = vector_i #num_t params_n
type vec = vector_i #poly_t params_k
type matrix = matrix_i #poly_t params_k params_k

#reset-options "--z3rlimit 100 --max_fuel 2 --max_ifuel 2 --using_facts_from '* -FStar.Seq'"
let ring_num = ring_t
let ring_poly = lib_ntt_ring #num #ring_num #params_n 7 (i16 params_zeta)

#reset-options "--z3rlimit 200 --max_fuel 1 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val linf: x:num -> n:nat{let p = sint_v x %+- params_q in n<=params_q/2 /\ (p>=0 ==> n=p) /\ (p<0 ==> n = -p)}

let linf x =
  let p = sint_v x %+- params_q in
  if p < 0 then -p else p

val distance_linf: x1:num -> x2:num -> n:nat{let p = sint_v (x1 -! x2) %+- params_q in n<=params_q/2 /\ (p>=0 ==> n=p) /\ (p<0 ==> n = -p)}

let distance_linf x1 x2 =
  let p = sint_v (x1 -! x2) %+- params_q in
  if p < 0 then -p else p

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val max_elem: #a:Type0 -> #len:size_nat -> f:(a -> Tot nat) -> s:lseq a len -> Tot (m:nat{(forall (i:nat). (i<len ==> f (s.[i]) <= m)) /\ (len = 0 ==> m = 0) /\ (len > 0 ==> (exists (j:nat{j<len}). f (s.[j]) == m))})

let max_elem #a #len f s =
  let max (n:nat{n<= len}) = m:nat{(forall (i:nat). (i<n ==> f (s.[i]) <= m)) /\ (n = 0 ==> m = 0) /\ (n > 0 ==> (exists (j:nat{j<n}). f (s.[j]) == m))} in
  let g (i:nat{i<len}) (acc:max i) : (max (i+1)) =
    let e = f s.[i] in
    let res = if e > acc then e else (acc+0) in
    res
  in
  let res = Loops.repeat_gen len max g 0 in
  res

val max_dist: #a:Type0 -> #len:size_nat -> f:(a -> a -> Tot nat) -> s1:lseq a len -> s2:lseq a len -> Tot (m:nat{(forall (i:nat). (i<len ==> f (s1.[i]) (s2.[i]) <= m)) /\ (len = 0 ==> m = 0) /\ (len > 0 ==> (exists (j:nat{j<len}). f (s1.[j]) (s2.[j]) == m))})

let max_dist #a #len f s1 s2 =
  let max (n:nat{n<= len}) = m:nat{(forall (i:nat). (i<n ==> f (s1.[i]) (s2.[i]) <= m)) /\ (n = 0 ==> m = 0) /\ (n > 0 ==> (exists (j:nat{j<n}). f (s1.[j]) (s2.[j]) == m))} in
  let g (i:nat{i<len}) (acc:max i) : (max (i+1)) =
    let e = f s1.[i] s2.[i] in
    let res = if e > acc then e else (acc+0) in
    res
  in
  let res = Loops.repeat_gen len max g 0 in
  res


val lemma_max_elem_le: #a:Type0 -> #len:size_nat -> f:(a -> Tot nat) -> s:lseq a len -> m:nat{m == max_elem f s} -> b:nat{forall (i:nat{i<len}). f s.[i] <= b} -> Lemma (m <= b)

let lemma_max_elem_le #a #len f s m b =
  if (len>0) then () else assert(m=0)

val lemma_max_dist_le: #a:Type0 -> #len:size_nat -> f:(a -> a -> Tot nat) -> s1:lseq a len -> s2:lseq a len -> m:nat{m == max_dist f s1 s2} -> b:nat{forall (i:nat{i<len}). f s1.[i] s2.[i] <= b} -> Lemma (m <= b)

let lemma_max_dist_le #a #len f s1 s2 m b =
  if (len>0) then () else assert(m=0)


#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

val poly_linf: p:poly -> n:nat{n<=params_q/2 /\ (forall (i:nat). {:pattern (index #_ #params_n p i)} i < params_n ==> linf (index #_ #params_n p i) <= n) /\ (exists (i:nat{i<params_n}). {:pattern (index #_ #params_n p i)} linf (index #_ #params_n p i) == n)}

let poly_linf p =
  let res = max_elem #num #params_n linf p in
  res

val vec_linf: p:vec -> n:nat{n<=params_q/2 /\ (forall (i:nat). {:pattern (index #_ #params_k p i)} i < params_k ==> poly_linf (index #_ #params_k p i) <= n) /\ (params_k=0 ==> n=0) /\ (params_k>0 ==> (exists (i:nat{i<params_k}). {:pattern (index #_ #params_k p i)} poly_linf (index #_ #params_k p i) == n))}

let vec_linf p =
  max_elem #poly #params_k poly_linf p

val poly_distance_linf: p1:poly -> p2:poly -> n:nat{n<=params_q/2 /\ (forall (i:nat). i < params_n ==> distance_linf (index #_ #params_n p1 i) (index #_ #params_n p2 i) <= n) /\ (exists (i:nat{i<params_n}). distance_linf (index #_ #params_n p1 i) (index #_ #params_n p2 i) == n)}

let poly_distance_linf p1 p2 =
  let res = max_dist #num #params_n distance_linf p1 p2 in
  res

val vec_distance_linf: p1:vec -> p2:vec -> n:nat{n<=params_q/2 /\ (forall (i:nat). i < params_k ==> poly_distance_linf (index #_ #params_k p1 i) (index #_ #params_k p2 i) <= n) /\ (params_k=0 ==> n=0) /\ (params_k>0 ==> (exists (i:nat{i<params_k}). poly_distance_linf (index #_ #params_k p1 i) (index #_ #params_k p2 i) == n))}

let poly_array_distance_linf p1 p2 =
  max_dist #poly #params_k poly_distance_linf p1 p2


val compress_lemma: d:size_nat{d < 16 /\ pow2 d < params_q} -> x:field params_q -> Lemma (let c:nat = (x * pow2 d + (params_q /2))/params_q in c <= pow2 d)

let compress_lemma d x =
  let c:nat = (x * pow2 d + (params_q /2))/params_q in
  assert(c * params_q <= x * pow2 d + params_q/2);
  assert(c * params_q <= (params_q) * pow2 d + params_q/2);
  lemma_div_le (c * params_q) ((params_q)*pow2 d + params_q/2) params_q;
  cancel_mul_mod c params_q;
  lemma_div_plus (params_q/2) (pow2 d) params_q;
  assert(c <= pow2 d + (params_q/2)/(params_q))

#reset-options "--z3rlimit 2000 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

val compress:d:size_nat{d < 16 /\ pow2 d < params_q} -> x:num -> Tot (res:num{ sint_v res < pow2 d /\ (sint_v res = ((sint_v x * pow2 d + params_q/2)/ params_q) % pow2 d) /\ (sint_v res > 0 ==> sint_v res = (sint_v x * pow2 d + params_q/2)/ params_q) /\ ((sint_v res <> (sint_v x * pow2 d + params_q/2)/params_q) ==> (sint_v x * pow2 d + params_q/2)/params_q = pow2 d) })

let compress d x =
  let xd: int32 = ((to_i32 x) <<. size d) +! i32 (params_q/2) in
  assert (sint_v xd = sint_v x * pow2 d + (params_q/2));
  let xd_q = division_by_q_int32 xd in
  assert (sint_v xd_q = sint_v xd / params_q);
  let xd_q16 = to_i16 xd_q in
  assert (sint_v xd_q16 = sint_v xd_q @%. S16);
  lemma_mod_sub (sint_v xd_q % pow2 16) (pow2 16) 1;
  assert (sint_v xd_q16 % pow2 16 = sint_v xd_q % pow2 16);
  let res = xd_q16 &. mod_mask (size d) in
  mod_mask_lemma xd_q (size d);
  assert(sint_v res = sint_v xd_q16 % pow2 d);
  assert(sint_v res = sint_v xd_q % pow2 d);
  assert(sint_v res >=0 /\ sint_v res < params_q);
  assert(sint_v res < pow2 d);
  compress_lemma d (sint_v x);
  res

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

let lemma_div_le_ (a:int) (b:int) (d:pos) : Lemma
  (requires (a <= b /\ a / d > b / d))
  (ensures  (False))
  = lemma_div_mod a d;
    lemma_div_mod b d;
    cut (d * (a / d) + a % d <= d * (b / d) + b % d);
    cut (d * (a / d) - d * (b / d) <= b % d - a % d);
    distributivity_sub_right d (a/d) (b/d);
    cut (b % d < d /\ a % d < d);
    cut (d * (a/d - b/d) <= d)

val lemma_div_le: a:int-> b:int -> d:pos ->
  Lemma (requires (a <= b))
        (ensures  (a / d <= b / d))
let lemma_div_le a b d =
  if a / d > b / d then lemma_div_le_ a b d

val lemma_decompress: a:int -> b:int-> d:pos -> Lemma (requires (a < b * d)) (ensures (a / d < b))

let lemma_decompress a b d =
  lemma_div_le a (b * d) d;
  if a / d = b then
    (assert((a/d)*d = b * d);
    assert (((a/d)*d < a) /\ (a < b*d));
    assert(false))


#reset-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"


val decompress: d:size_nat{pow2 d < params_q /\ d < 16} -> x:num{sint_v x < pow2 d} -> Tot (res':num{ sint_v res' = (2*params_q * sint_v x + pow2 d) / pow2 (d+1)})


let decompress d x =
  let a:int32 = i32 2 *! to_i32 x *! i32 params_q +! (i32 1 <<. size d) in
  pow2_double_mult d;
  assert (sint_v a < params_q * pow2 (d+1));
  let a2:int32 = a >>. size (d+1) in
  lemma_decompress (sint_v a) (params_q) (pow2 (d+1));
  assert_norm(range (sint_v a2) S16);
  to_i16 a2

#reset-options "--z3rlimit 500 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

val sub_lemma1: d:size_nat{d < 16 /\ pow2 d < params_q} -> x:num -> x':num{sint_v x' == sint_v (decompress d (compress d x))} -> c:num{sint_v c < pow2 d /\ sint_v c == sint_v (compress d x)} -> Lemma (sint_v x' * pow2 (d+1) <= 2*params_q * sint_v c + pow2 d)

let sub_lemma1 d x x' c =
  assert (sint_v x' == sint_v (decompress d c));
  division_propriety (2*params_q * sint_v c + pow2 d) (pow2 (d+1));
  pow2_double_mult d;
  assert ((2*params_q * sint_v c - pow2 d) < sint_v x' * pow2 (d+1))

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val lemma_le_inv: a:nat->b:pos->c:pos{b<=c} -> Lemma (a / b >= a / c)

let lemma_le_inv a b c = 
  calc (<=) {
    (a/c) * b;
      <= {}
    (a/c) * c;
      <= {}
    a;};
  division_definition_lemma_2 a b (a/c)

#reset-options "--z3rlimit 300 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val sub_lemma2: d:size_nat{d > 0 /\ d < 16 /\ pow2 d < params_q} -> x:num -> x':num{sint_v x' == sint_v (decompress d (compress d x))} -> c:num{sint_v c < (pow2 d) /\ sint_v c == sint_v (compress d x) /\ (sint_v c = ((sint_v x * pow2 d + (params_q /2))/params_q)) /\ (sint_v x' * pow2 (d+1) <= 2*params_q * sint_v c + pow2 d)} -> Lemma (let p = (sint_v x' - sint_v x) %+- params_q in let b = (params_q + pow2 d) / pow2 (d+1) in -b <= p /\ p <= b)
  
let sub_lemma2 d x x' c =
  let p = (sint_v x' - sint_v x) %+- params_q in
  let b = (params_q + pow2 d) / pow2 (d+1) in
  calc (>) {
    sint_v x' * pow2 (d+1);
      > {pow2_double_mult d; ()}
    2 * params_q * ((sint_v x * pow2 d + (params_q /2))/params_q) - pow2 d;
      >= { assert((sint_v x * pow2 d + (params_q/2))/params_q * params_q > (sint_v x * pow2 d + (params_q/2)) - params_q); ()}
    2 * (sint_v x * pow2 d - params_q/2 - 1) - pow2 d +1;
      >= {pow2_double_mult d; ()}
    sint_v x * pow2 (d+1) - params_q - pow2 d;
  };
  
  calc (>=) {
    sint_v x' - sint_v x;
      = {cancel_mul_div (sint_v x' - sint_v x) (pow2 (d+1))}
    ((sint_v x' - sint_v x)*pow2 (d+1))/pow2 (d+1);
      >= {lemma_decompress (- params_q - pow2 d) (sint_v x' - sint_v x) (pow2 (d+1))}
      (-params_q - pow2 d)/pow2(d+1)+1;
      >= {}
    -(params_q+pow2 d)/pow2(d+1);  
  };
  
  calc (<=) {
    sint_v x' * pow2 (d+1);
      <= {pow2_double_mult d; ()}
    2 * params_q * ((sint_v x * pow2 d + (params_q /2))/params_q) + pow2 d;
      <= {assert(params_q * ((sint_v x * pow2 d + (params_q /2))/params_q) <= sint_v x * pow2 d + (params_q /2)); ()}
    2 * ((sint_v x * pow2 d + (params_q/2))) + pow2 d;
      <= {pow2_double_mult d; ()}
    sint_v x * pow2 (d+1) + params_q + pow2 d;
  };

  calc (<=) {
    sint_v x' - sint_v x;
      = {cancel_mul_div (sint_v x' - sint_v x) (pow2 (d+1))}
    ((sint_v x' - sint_v x)*pow2 (d+1))/pow2 (d+1);
      <= {lemma_div_le ((sint_v x' - sint_v x) * pow2 (d+1)) (params_q + pow2 d) (pow2 (d+1))}
    (params_q + pow2 d)/pow2(d+1);
  };
  
  lemma_div_le (params_q+pow2 d) (2*params_q) (pow2 (d+1));
  pow2_multiplication_modulo_lemma_2 params_q (d+1) 1;
  assert(b <= params_q/ pow2 d);
  pow2_le_compat (d+1) 1;
  lemma_le_inv params_q 2 (pow2 (d+1));
  assert(b<=params_q /2);
  assert(-params_q/2 <= ( sint_v x' - sint_v x) /\ (sint_v x' - sint_v x) <= params_q / 2);
  lemma_mod_plus_minus_injective params_q (sint_v x' - sint_v x) (sint_v x' - sint_v x);
  assert(p = (sint_v x' - sint_v x))


#reset-options "--z3rlimit 500 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val sub_lemma3: d:size_nat{d > 0 /\ d < 16 /\ pow2 d < params_q} -> x:num{sint_v (compress d x) = 0 /\ sint_v (compress d x) <> (sint_v x * pow2 d + params_q/2)/params_q} -> Lemma (let x' = decompress d (compress d x) in let p = (sint_v x' - sint_v x) %+- params_q in let b = (params_q + pow2 d) / pow2 (d+1) in -b <= p /\ p <= b)

let sub_lemma3 d x =
  let x' = decompress d (compress d x) in
  let a = (sint_v x * pow2 d + (params_q /2))/params_q in
  let b = (params_q + pow2 d)/pow2 (d+1) in
  let p = (sint_v x' - sint_v x) %+- params_q in
  assert(sint_v x' = 0);
  assert(a = pow2 d);
  calc (<=) {
      params_q;
      <= {cancel_mul_div params_q (pow2 d)}
      (params_q*a)/pow2 d;
      <= {assert(a*params_q <= sint_v x * pow2 d + (params_q/2)); lemma_div_le (pow2 d * params_q) (sint_v x * pow2 d + (params_q/2)) (pow2 d); () }
      (sint_v x * pow2 d + (params_q/2))/ pow2 d;
      <= {division_addition_lemma (params_q/2) (params_q) (pow2 d); division_multiplication_lemma params_q 2 (pow2 d); pow2_double_mult d; ()}
      sint_v x + params_q / pow2 (d+1);
    };

    assert (sint_v x <= params_q /\ params_q <= sint_v x + params_q / pow2 (d+1));
    assert(params_q / pow2 (d+1) <= params_q / 2);
    assert(0 <= sint_v x' - sint_v x + params_q /\ sint_v x' - sint_v x + params_q <= params_q / pow2 (d+1));
    assert(p= sint_v x' - sint_v x + params_q);
    lemma_div_le params_q (params_q+pow2 d) (pow2 (d+1));
    assert(params_q/pow2 (d+1) <= b)
    

#reset-options "--z3rlimit 500 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val decompress_compress_lemma: d:size_nat{d < 16 /\ pow2 d < params_q} -> x:num -> x':num{sint_v x' == sint_v (decompress d (compress d x))} -> Lemma (let p = distance_linf x' x in let b = (params_q + pow2 d) / pow2 (d+1) in p <= b)

let decompress_compress_lemma d x x' =
  let c = compress d x in
  sub_lemma1 d x x' c;
  let a = (sint_v x * pow2 d + (params_q /2))/params_q in
  let b = (params_q + pow2 d)/pow2 (d+1) in
  if d = 0 then
    assert(params_q/2 <= b)    
  else if(sint_v c > 0 || (sint_v c = a)) then
    sub_lemma2 d x x' c
  else
    sub_lemma3 d x


#reset-options "--z3rlimit 1000 --max_fuel 2 --max_ifuel 2 --using_facts_from '* -FStar.Seq'"

val poly_compress: d:size_nat{d < 16 /\ pow2 d < params_q} -> p:poly -> Tot (p':poly{(forall (i:nat). {:pattern (index #_ #params_n p' i)} i < params_n ==> sint_v #S16 #SEC (index #_ #params_n p' i) == sint_v (compress d (index #_ #params_n p i)) /\ sint_v #S16 #SEC (index #_ #params_n p' i) < pow2 d)})

let poly_compress d p = Seq.map #_ #_ #params_n (compress d) p

val poly_decompress: d:size_nat{d < 16 /\ pow2 d < params_q} -> p:poly{forall (i:nat). {:pattern (index #_ #params_n p i)} i < params_n ==> sint_v #S16 #SEC (index #_ #params_n p i) < pow2 d} -> Tot (p':poly{(forall (i:nat). {:pattern (index #_ #params_n p' i)} i < params_n ==> sint_v #S16 #SEC (index #_ #params_n p' i) == sint_v #S16 #SEC (decompress d (index #_ #params_n p i)))})

let poly_decompress d p = 
  assert (interp_numeric #0 num_t == num);
  let l:lseq (x:num{sint_v x < pow2 d}) params_n = createi params_n (fun i -> let x:(x:num{sint_v x < pow2 d}) = index #_ #params_n p i in x) in
  Seq.map #(x:num{sint_v x <pow2 d}) #num #params_n (decompress d) l

#reset-options "--z3rlimit 100 --max_fuel 2 --max_ifuel 2 --using_facts_from '* -FStar.Seq'"

val poly_decompress_compress_lemma: d:size_nat{d < 16 /\ pow2 d < params_q} -> p:poly -> p':poly{p' == poly_decompress d (poly_compress d p)} -> Lemma (let m = poly_distance_linf p' p in let b = (params_q + pow2 d) / pow2 (d+1) in m <= b)

let poly_decompress_compress_lemma d p p' =
  let m = poly_distance_linf p' p in
  let b = (params_q + pow2 d) / pow2 (d+1) in
  let customprop (i:nat{i<params_n}) : GTot Type0 =
    distance_linf (index #_ #params_n p' i) (index #_ #params_n p i) <= b in
  let g (i:nat{i<params_n}) : Lemma (customprop i) =
    assert(index #_ #params_n p' i == decompress d (compress d (index #_ #params_n p i))); 
    decompress_compress_lemma d (index #_ #params_n p i) (index #_ #params_n p' i)
  in 
  FStar.Classical.forall_intro g;
  lemma_max_dist_le #_ #params_n distance_linf p' p m b

val vec_compress: d:size_nat{d < 16 /\ pow2 d < params_q} -> p:vec -> Tot (p':vec{(forall (i:nat). {:pattern (index #_ #params_k p' i)} i < params_k ==> index #_ #params_k p' i == poly_compress d (index #_ #params_k p i))})

let vec_compress d p = Seq.map #_ #_ #params_k (poly_compress d) p

#reset-options "--z3rlimit 100 --max_fuel 2 --max_ifuel 2 --using_facts_from '* -FStar.Seq'"

val vec_decompress: d:size_nat{d < 16 /\ pow2 d < params_q} -> p:vec{forall (i:nat{i<params_k}). forall (j:nat{j<params_n}). sint_v #S16 #SEC (index #_ #params_n (index #_ #params_k p i) j) < pow2 d} -> Tot (p':vec{(forall (i:nat). {:pattern (index #_ #params_k p' i)} i < params_k ==> index #_ #params_k p' i == poly_decompress d (index #_ #params_k p i))})

let vec_decompress d p = 
  let l:lseq (x:poly{forall (i:nat). {:pattern (index #_ #params_n x i)} i < params_n ==> sint_v #S16 #SEC (index #_ #params_n x i) < pow2 d}) params_k = createi params_k (fun i -> let x:(x:poly{forall (i:nat). {:pattern (index #_ #params_n x i)} i < params_n ==> sint_v #S16 #SEC (index #_ #params_n x i) < pow2 d}) = index #_ #params_k p i in x) in
  Seq.map #_ #_ #params_k (poly_decompress d) l


#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

val vec_decompress_compress_lemma: d:size_nat{d < 16 /\ pow2 d < params_q} -> p:vec -> p':vec{p' == vec_decompress d (vec_compress d p)} -> Lemma (let m = poly_array_distance_linf p' p in let b = (params_q + pow2 d) / pow2 (d+1) in m <= b)

let vec_decompress_compress_lemma d p p' =
  let m = poly_array_distance_linf p' p in
  let b = (params_q + pow2 d) / pow2 (d+1) in
  let customprop (i:nat{i<params_k}) : GTot Type0 =
    poly_distance_linf (index #_ #params_k p' i) (index #_ #params_k p i) <= b in
  let g (i:nat{i<params_k}) : Lemma (customprop i) =
    assert((index #_ #params_k p' i) == poly_decompress d (poly_compress d (index #_ #params_k p i))); 
    poly_decompress_compress_lemma d (index #_ #params_k p i) (index #_ #params_k p' i)
  in 
  FStar.Classical.forall_intro g;
  lemma_max_dist_le #_ #params_k poly_distance_linf p' p m b


