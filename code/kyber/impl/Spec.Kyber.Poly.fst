module Spec.Kyber.Poly

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open FStar.Mul
open FStar.Math.Lemmas
open FStar.Classical

open Spec.Kyber.Params
open Spec.Kyber.Lemmas
open Spec.Powtwo.Lemmas

module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators

unfold inline_for_extraction
type poly (#t:inttype) (#l:secrecy_level) (m:nat) = lseq (x:(uint_t t l){uint_v x < m}) params_n
unfold inline_for_extraction
type pub_poly (#t:inttype) = poly #t #PUB
unfold inline_for_extraction
type sec_poly (#t:inttype) = poly #t #SEC

unfold inline_for_extraction
type pub_poly16 = pub_poly #U16

unfold inline_for_extraction
type poly_array (#t:inttype) (#l:secrecy_level) (k:size_nat) (m:nat) = lseq (poly #t #l m) k
unfold inline_for_extraction
type pub_poly_array (#t:inttype) (k:size_nat) (m:nat) = lseq (pub_poly #t m) k
unfold inline_for_extraction
type sec_poly_array (#t:inttype) (k:size_nat) (m:nat) = lseq (sec_poly #t m) k

unfold inline_for_extraction
type pub_poly_array16 (k:size_nat) (m:nat) = lseq (pub_poly16 m) k


#reset-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val linf: #t:inttype -> #l:secrecy_level -> x:uint_t t l -> n:nat{let p = uint_v x %+- params_q in n<=params_q/2 /\ (p>=0 ==> n=p) /\ (p<0 ==> n = -p)}

let linf #t #l x =
  let p = uint_v x %+- params_q in
  if p < 0 then -p else p

val distance_linf: #t:inttype -> #l:secrecy_level -> x1:uint_t t l -> x2:uint_t t l -> n:nat{let p = (uint_v x1 - uint_v x2) %+- params_q in n<=params_q/2 /\ (p>=0 ==> n=p) /\ (p<0 ==> n = -p)}

let distance_linf #t #l x1 x2 =
  let p = (uint_v x1 - uint_v x2) %+- params_q in
  if uint_v x1 > uint_v x2 then 
    let l = linf (x1-.x2) in
    (assert(uint_v (x1-.x2) = uint_v x1 - uint_v x2); assert( l<=params_q/2 /\ (p>=0 ==> l=p) /\ (p<0 ==> l = -p)); l)
    else 
      let l = linf (x2-.x1) in
      (assert(uint_v (x2-.x1) = uint_v x2 - uint_v x1); lemma_mod_plus_minus_opposite params_q (uint_v x2 - uint_v x1); assert( l<=params_q/2 /\ (-p>=0 ==> l= -p) /\ (-p<0 ==> l = -(-p))); l)
  
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



val poly_linf: #t:inttype -> #l:secrecy_level -> #m:nat -> p:poly #t #l m -> n:nat{n<=params_q/2 /\ (forall (i:nat). {:pattern (index p i)} i < params_n ==> linf (index p i) <= n) /\ (exists (i:nat{i<params_n}). {:pattern (index p i)} linf (index p i) == n)}

let poly_linf #t #l #m p = 
  let res = max_elem #(x:(uint_t t l){uint_v x < m}) #params_n linf p in
  res

val poly_array_linf: #t:inttype -> #l:secrecy_level -> #k:size_nat -> #m:nat -> p:poly_array #t #l k m -> n:nat{n<=params_q/2 /\ (forall (i:nat). {:pattern (index p i)} i < k ==> poly_linf (index p i) <= n) /\ (k=0 ==> n=0) /\ (k>0 ==> (exists (i:nat{i<k}). {:pattern (index p i)} poly_linf (index p i) == n))}

let poly_array_linf #t #l #k #m p =
  max_elem poly_linf p

val poly_distance_linf: #t:inttype -> #l:secrecy_level -> #m:nat -> p1:poly #t #l m -> p2:poly #t #l m -> n:nat{n<=params_q/2 /\ (forall (i:nat). i < params_n ==> distance_linf (index p1 i) (index p2 i) <= n) /\ (exists (i:nat{i<params_n}). distance_linf (index p1 i) (index p2 i) == n)}

let poly_distance_linf #t #l #m p1 p2 = 
  let res = max_dist #(x:(uint_t t l){uint_v x < m}) #params_n distance_linf p1 p2 in
  res

val poly_array_distance_linf: #t:inttype -> #l:secrecy_level -> #k:size_nat -> #m:nat -> p1:poly_array #t #l k m -> p2:poly_array #t #l k m -> n:nat{n<=params_q/2 /\ (forall (i:nat). i < k ==> poly_distance_linf (index p1 i) (index p2 i) <= n) /\ (k=0 ==> n=0) /\ (k>0 ==> (exists (i:nat{i<k}). poly_distance_linf (index p1 i) (index p2 i) == n))}

let poly_array_distance_linf #t #l #k #m p1 p2 =
  max_dist poly_distance_linf p1 p2


let pub_u32 = uint #U32 #PUB

val compress_lemma_:d:size_nat{d < 16 /\ pow2 d < params_q} -> x:pub_uint16{uint_v x < params_q} -> c:pub_uint32{ c = (((cast U32 PUB x) <<. size d ) +. pub_u32 (params_q / 2)) /. pub_u32 params_q } -> Lemma (uint_v c == (uint_v x * pow2 d + (params_q /2))/params_q)

let compress_lemma_ d x c =
  let a1 = (cast U32 PUB x) <<. size d in
  let a2 = a1 +. pub_u32 (params_q/2) in
  let a3 = a2 /. pub_u32 params_q in
  assert (uint_v a1 = uint_v x * pow2 d);
  assert (uint_v a2 = uint_v a1 + params_q /2);
  assert (uint_v a3 = uint_v a2 / params_q);
  assert (uint_v c = uint_v a3);
  assert(uint_v c = (uint_v a1 +params_q / 2 ) / params_q)

val compress_lemma: d:size_nat{d < 16 /\ pow2 d < params_q} -> x:pub_uint16{uint_v x < params_q} -> c:pub_uint32{c = (((cast U32 PUB x) <<. size d ) +. pub_u32 (params_q / 2)) /. pub_u32 params_q} -> Lemma (uint_v c == (uint_v x * pow2 d + (params_q /2))/params_q /\ uint_v c <= pow2 d)

let compress_lemma d x c =
  compress_lemma_ d x c;
  assert(uint_v c * params_q <= uint_v x * pow2 d + params_q/2);
  assert(uint_v c * params_q <= (params_q) * pow2 d + params_q/2);
  lemma_div_le (uint_v c * params_q) ((params_q)*pow2 d + params_q/2) params_q;
  cancel_mul_mod (uint_v c) params_q;
  lemma_div_plus (params_q/2) (pow2 d) params_q;
  assert(uint_v c <= pow2 d + (params_q/2)/(params_q))
  
#reset-options "--z3rlimit 300 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val compress:d:size_nat{d < 16 /\ pow2 d < params_q} -> x:pub_uint16{uint_v x < params_q} -> Tot (res:pub_uint16{(uint_v res < pow2 d) /\ (uint_v res == ((uint_v x * pow2 d + params_q/2)/ params_q) % pow2 d) /\ (uint_v res > 0 ==> uint_v res = (uint_v x * pow2 d + params_q/2)/ params_q) /\ ((uint_v res =!= (uint_v x * pow2 d + params_q/2)/params_q) ==> (uint_v x * pow2 d + params_q/2)/params_q == pow2 d) })

let compress d x =
  let a = (((cast U32 PUB x) <<. size d ) +. pub_u32 (params_q / 2)) /. pub_u32 params_q in
  compress_lemma d x a;
  assert (uint_v a == (uint_v x * pow2 d + (params_q /2))/params_q);
  let a4 = a &. ((pub_u32 1 <<. size d) -. pub_u32 1) in
  modulo_pow2_pub_u32 a d;
  assert (uint_v a4 == uint_v a % pow2 d);
  cast U16 PUB a4
  
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


val decompress: d:size_nat{pow2 d < params_q /\ d < 16} -> x:pub_uint16{uint_v x < pow2 d} -> Tot (res':pub_uint16{uint_v res' < params_q /\ uint_v res' == (2*params_q * uint_v x+pow2 d) / pow2 (d+1)})


let decompress d x =
  let q = pub_u32 params_q in
  let a1 = cast U32 PUB x *. q in
  assert(uint_v a1 == uint_v x * params_q);
  let a2 = (a1 <<. size 1) +. (pub_u32 1 <<. size d) in
  assert(uint_v (a1<<.size 1) == 2*uint_v a1);
  assert(uint_v a2 == 2*uint_v a1 + pow2 d);
  assert(uint_v a2 == 2*uint_v x*params_q + pow2 d);
  pow2_double_mult d;
  assert (uint_v a2 < params_q * pow2 (d+1));
  let a3 = a2 >>. size (d+1) in
  assert(uint_v a3 = uint_v a2 / pow2 (d+1));
  lemma_decompress (uint_v a2) (params_q) (pow2 (d+1));
  cast U16 PUB a3

#reset-options "--z3rlimit 150 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val sub_lemma1: d:size_nat{d < 16 /\ pow2 d < params_q} -> x:pub_uint16{uint_v x < params_q} -> x':pub_uint16{x' == decompress d (compress d x)} -> c:pub_uint16{c = compress d x} -> Lemma (uint_v x' * pow2 (d+1) <= 2*params_q * uint_v c + pow2 d)

let sub_lemma1 d x x' c =
  assert (x' = decompress d c);
  division_propriety (2*params_q * uint_v c + pow2 d) (pow2 (d+1));
  pow2_double_mult d;
  assert ((2*params_q * uint_v c - pow2 d) < uint_v x' * pow2 (d+1))

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

val sub_lemma2: d:size_nat{d > 0 /\ d < 16 /\ pow2 d < params_q} -> x:pub_uint16{uint_v x < params_q} -> x':pub_uint16{x' == decompress d (compress d x)} -> c:pub_uint16{c==compress d x /\ (uint_v c == ((uint_v x * pow2 d + (params_q /2))/params_q)) /\ (uint_v x' * pow2 (d+1) <= 2*params_q * uint_v c + pow2 d)} -> Lemma (let p = (uint_v x' - uint_v x) %+- params_q in let b = (params_q + pow2 d) / pow2 (d+1) in -b <= p /\ p <= b)
  
let sub_lemma2 d x x' c =
  let p = (uint_v x' - uint_v x) %+- params_q in
  let b = (params_q + pow2 d) / pow2 (d+1) in
  calc (>) {
    uint_v x' * pow2 (d+1);
      > {pow2_double_mult d; ()}
    2 * params_q * ((uint_v x * pow2 d + (params_q /2))/params_q) - pow2 d;
      >= { assert((uint_v x * pow2 d + (params_q/2))/params_q * params_q > (uint_v x * pow2 d + (params_q/2)) - params_q); ()}
    2 * (uint_v x * pow2 d - params_q/2 - 1) - pow2 d +1;
      >= {pow2_double_mult d; ()}
    uint_v x * pow2 (d+1) - params_q - pow2 d;
  };
  
  calc (>=) {
    uint_v x' - uint_v x;
      == {cancel_mul_div (uint_v x' - uint_v x) (pow2 (d+1))}
    ((uint_v x' - uint_v x)*pow2 (d+1))/pow2 (d+1);
      >= {lemma_decompress (- params_q - pow2 d) (uint_v x' - uint_v x) (pow2 (d+1))}
      (-params_q - pow2 d)/pow2(d+1)+1;
      >= {}
    -(params_q+pow2 d)/pow2(d+1);  
  };
  
  calc (<=) {
    uint_v x' * pow2 (d+1);
      <= {pow2_double_mult d; ()}
    2 * params_q * ((uint_v x * pow2 d + (params_q /2))/params_q) + pow2 d;
      <= {assert(params_q * ((uint_v x * pow2 d + (params_q /2))/params_q) <= uint_v x * pow2 d + (params_q /2)); ()}
    2 * ((uint_v x * pow2 d + (params_q/2))) + pow2 d;
      <= {pow2_double_mult d; ()}
    uint_v x * pow2 (d+1) + params_q + pow2 d;
  };

  calc (<=) {
    uint_v x' - uint_v x;
      == {cancel_mul_div (uint_v x' - uint_v x) (pow2 (d+1))}
    ((uint_v x' - uint_v x)*pow2 (d+1))/pow2 (d+1);
      <= {lemma_div_le ((uint_v x'-uint_v x) * pow2 (d+1)) (params_q + pow2 d) (pow2 (d+1))}
    (params_q + pow2 d)/pow2(d+1);
  };
  
  lemma_div_le (params_q+pow2 d) (2*params_q) (pow2 (d+1));
  pow2_multiplication_modulo_lemma_2 params_q (d+1) 1;
  assert(b <= params_q/ pow2 d);
  pow2_le_compat (d+1) 1;
  lemma_le_inv params_q 2 (pow2 (d+1));
  assert(b<=params_q /2);
  assert(-params_q/2 <= (uint_v x' - uint_v x) /\ (uint_v x' - uint_v x) <= params_q / 2);
  lemma_mod_plus_minus_injective params_q (uint_v x' - uint_v x) (uint_v x' - uint_v x);
  assert(p = (uint_v x' - uint_v x))


#reset-options "--z3rlimit 500 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val sub_lemma3: d:size_nat{d > 0 /\ d < 16 /\ pow2 d < params_q} -> x:pub_uint16{uint_v x < params_q /\ uint_v (compress d x) == 0 /\ uint_v (compress d x) =!= (uint_v x * pow2 d + params_q/2)/params_q} -> Lemma (let x' = decompress d (compress d x) in let p = (uint_v x' - uint_v x) %+- params_q in let b = (params_q + pow2 d) / pow2 (d+1) in -b <= p /\ p <= b)

let sub_lemma3 d x =
  let x' = decompress d (compress d x) in
  let a = (uint_v x * pow2 d + (params_q /2))/params_q in
  let b = (params_q + pow2 d)/pow2 (d+1) in
  let p = (uint_v x' - uint_v x) %+- params_q in
  assert(uint_v x' = 0);
  assert(a = pow2 d);
  calc (<=) {
      params_q;
      <= {cancel_mul_div params_q (pow2 d)}
      (params_q*a)/pow2 d;
      <= {assert(a*params_q <= uint_v x * pow2 d + (params_q/2)); lemma_div_le (pow2 d * params_q) (uint_v x * pow2 d + (params_q/2)) (pow2 d); () }
      (uint_v x * pow2 d + (params_q/2))/ pow2 d;
      <= {division_addition_lemma (params_q/2) (params_q) (pow2 d); division_multiplication_lemma params_q 2 (pow2 d); pow2_double_mult d; ()}
      uint_v x + params_q / pow2 (d+1);
    };

    assert (uint_v x <= params_q /\ params_q <= uint_v x + params_q / pow2 (d+1));
    assert(params_q / pow2 (d+1) <= params_q / 2);
    assert(0 <= uint_v x' - uint_v x + params_q /\ uint_v x' - uint_v x + params_q <= params_q / pow2 (d+1));
    assert(p== uint_v x' -uint_v x + params_q);
    lemma_div_le params_q (params_q+pow2 d) (pow2 (d+1));
    assert(params_q/pow2 (d+1) <= b)
    

#reset-options "--z3rlimit 500 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val decompress_compress_lemma: d:size_nat{d < 16 /\ pow2 d < params_q} -> x:pub_uint16{uint_v x < params_q} -> x':pub_uint16{x' == decompress d (compress d x)} -> Lemma (let p = distance_linf x' x in let b = (params_q + pow2 d) / pow2 (d+1) in p <= b)

let decompress_compress_lemma d x x' =
  let c = compress d x in
  sub_lemma1 d x x' c;
  let a = (uint_v x * pow2 d + (params_q /2))/params_q in
  let b = (params_q + pow2 d)/pow2 (d+1) in
  let p = (uint_v x' - uint_v x) %+- params_q in
  let p2 = linf (x'-. x) in
  if d = 0 then
    assert(params_q/2 <= b)    
  else if(uint_v c > 0 || (uint_v c = a)) then
    sub_lemma2 d x x' c
  else
    sub_lemma3 d x


#reset-options "--z3rlimit 500 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val poly_compress: d:size_nat{d < 16 /\ pow2 d < params_q} -> p:(pub_poly16 params_q)-> Tot (p':(pub_poly16 (pow2 d)){(forall (i:nat). {:pattern (index p' i)} i < params_n ==> index p' i == compress d p.[i])})

let poly_compress d p = map (compress d) p

val poly_decompress: d:size_nat{d < 16 /\ pow2 d < params_q} -> p:(pub_poly16 (pow2 d)) -> Tot (p':(pub_poly16 params_q){(forall (i:nat). {:pattern (index p' i)} i < params_n ==> index p' i == decompress d (index p i))})

let poly_decompress d p = map (decompress d) p

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val poly_decompress_compress_lemma: d:size_nat{d < 16 /\ pow2 d < params_q} -> p:pub_poly16 params_q -> p':(pub_poly16 params_q){p' == poly_decompress d (poly_compress d p)} -> Lemma (let m = poly_distance_linf p p' in let b = (params_q + pow2 d) / pow2 (d+1) in m <= b)

let poly_decompress_compress_lemma d p p' =
  let m = poly_distance_linf p p' in
  let b = (params_q + pow2 d) / pow2 (d+1) in
  let customprop (i:nat{i<params_n}) : GTot Type0 =
    distance_linf p.[i] p'.[i] <= b in
  let g (i:nat{i<params_n}) : Lemma (customprop i) =
    assert(p'.[i] = decompress d (compress d p.[i])); 
    decompress_compress_lemma d p.[i] p'.[i] 
  in 
  forall_intro g;
  lemma_max_dist_le distance_linf p p' m b

val poly_array_compress: #k:size_nat -> d:size_nat{d < 16 /\ pow2 d < params_q} -> p:(pub_poly_array16 k params_q)-> Tot (p':(pub_poly_array16 k (pow2 d)){(forall (i:nat). {:pattern (index p' i)} i < k ==> index p' i == poly_compress d p.[i])})

let poly_array_compress #k d p = map (poly_compress d) p

val poly_array_decompress: #k:size_nat -> d:size_nat{d < 16 /\ pow2 d < params_q} -> p:(pub_poly_array16 k (pow2 d)) -> Tot (p':(pub_poly_array16 k params_q){(forall (i:nat). {:pattern (index p' i)} i < k ==> index p' i == poly_decompress d (index p i))})

let poly_array_decompress #k d p = map (poly_decompress d) p


#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val poly_array_decompress_compress_lemma: #k:size_nat -> d:size_nat{d < 16 /\ pow2 d < params_q} -> p:pub_poly_array16 k params_q -> p':(pub_poly_array16 k params_q){p' == poly_array_decompress d (poly_array_compress d p)} -> Lemma (let m = poly_array_distance_linf p p' in let b = (params_q + pow2 d) / pow2 (d+1) in m <= b)

let poly_array_decompress_compress_lemma #k d p p' =
  let m = poly_array_distance_linf p p' in
  let b = (params_q + pow2 d) / pow2 (d+1) in
  let customprop (i:nat{i<k}) : GTot Type0 =
    poly_distance_linf p.[i] p'.[i] <= b in
  let g (i:nat{i<k}) : Lemma (customprop i) =
    assert(p'.[i] == poly_decompress d (poly_compress d p.[i])); 
    poly_decompress_compress_lemma d p.[i] p'.[i] 
  in 
  forall_intro g;
  lemma_max_dist_le poly_distance_linf p p' m b
