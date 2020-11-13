module Spec.Dilithium.Poly

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators

open Spec.Dilithium.Params
open Spec.Dilithium.Stream
open Spec.Dilithium.Montgomery

module SHA3 = Spec.SHA3
module Seq = FStar.Seq


type poly = lseq uint32 param_n
type modq = x:nat{x < param_q}
type polyq = lseq modq param_n
let poly4 = p:poly {forall (i:nat{i<param_n}). {:pattern p.[i]} v p.[i] < 16}
let poly4veck = lseq poly4 param_k

type polyveck = lseq poly param_k
type polyvecl = lseq poly param_l

let new_poly:poly = create param_n (u32 0)
let new_polyveck:polyveck = create param_k new_poly
let new_polyvecl:polyvecl = create param_l new_poly

let new_bytes: lbytes 0 = Seq.empty



val fa: #a:Type -> #len:size_nat -> f:(a -> Tot bool) -> x:lseq a len -> bool

let fa #a #len f x = Seq.for_all #a f x


val for_all_lemma:#a:Type -> #len:size_nat -> f:(a -> Tot bool) -> (x:lseq a len) ->
  (Lemma ((fa #a #len f x) ==> (forall (i: nat {i < len} ) . f (x.[i]))))

let for_all_lemma #a #len f x =
  assert (fa #a #len f x == Seq.for_all f x);
  assert (Seq.for_all f x ==> (forall (i: nat {i < len} ) . f (x.[i])))


val exp_modq:
    x:nat{x < param_q}
  -> y:nat{y < param_q}
  -> z:nat{z < param_q}

let rec exp_modq x y =
  if y = 0 then 1
  // else if y % 2 = 0 then exp_modq ((x*x) % param_q) (y/2)
  else (x * (exp_modq x (y-1))) % param_q

val abs_modq:
    x:nat{x < param_q}
  -> Tot (y:nat{2 * y <= param_q})

let abs_modq x =
  if 2 * x > param_q then (param_q - x) else x

(****************    poly math    ****************)
(* structured similarly to kyber *)

let modq_mul (x:uint32) (y:uint32) = u32 ((v x * v y) % param_q)
let mont_mul (x:uint32) (y:uint32) = montgomery_reduce (to_u64 x *. to_u64 y)
let poly_pointwise_mont (p1:poly) (p2:poly) : poly = map2 mont_mul p1 p2
let poly_add (p1:poly) (p2:poly) : poly = map2 (fun x y -> u32 ((v x + v y) % param_q)) p1 p2
let poly_sub (p1:poly) (p2:poly) : poly = map2 (fun x y -> x +. u32 (2 * param_q) -. y) p1 p2

// stdreps = standard representatives in Z_q
let poly_is_stdreps (p:poly) = forall (i:nat{i<param_n}). {:pattern p.[i]} v p.[i] < param_q
let polyveck_is_stdreps (p:polyveck) = forall (i:nat{i<param_k}). {:pattern p.[i]} poly_is_stdreps p.[i]
let polyvecl_is_stdreps (p:polyvecl) = forall (i:nat{i<param_l}). {:pattern p.[i]} poly_is_stdreps p.[i]

let poly_modq (p:poly) : (p':poly {poly_is_stdreps p'}) = map (fun (x:uint32) -> u32 ((v x) % param_q)) p
let poly_freeze = poly_modq
let poly_reduce = poly_modq

let center_q (x:nat{x < param_q}) = if x <= param_q/2 then x else x - param_q
let norm_q (x:nat{x < param_q}) = let c = center_q x in if c < 0 then -c else c

let poly_bound (p:poly) (b:nat) = forall (i:nat{i<param_n}). {:pattern p.[i]} v p.[i] < b
let poly_norm_bound (p:poly) (b:nat) = forall (i:nat{i<param_n}). {:pattern p.[i]} v p.[i] < param_q /\ norm_q (v p.[i]) < b
let polyveck_bound (vec:polyveck) (b:nat) = forall (i:nat{i<param_k}). {:pattern vec.[i]} poly_bound vec.[i] b
let polyvecl_bound (vec:polyvecl) (b:nat) = forall (i:nat{i<param_l}). {:pattern vec.[i]} poly_bound vec.[i] b
let polyveck_norm_bound (vec:polyveck) (b:nat) = forall (i:nat{i<param_k}). {:pattern vec.[i]} poly_norm_bound vec.[i] b
let polyvecl_norm_bound (vec:polyvecl) (b:nat) = forall (i:nat{i<param_l}). {:pattern vec.[i]} poly_norm_bound vec.[i] b

let poly_is_4bit (p:poly) = poly_bound p 16
let polyveck_is_4bit (vec:polyveck) = polyveck_bound vec 16

let nth_root = 6644104
let inv_root = 6125690
let inv_n = 8347681

let polyvecl_add = map2 #poly #poly #poly #param_l poly_add
let polyvecl_sub = map2 #poly #poly #poly #param_l poly_sub
let polyvecl_modq = map #poly #poly #param_l poly_modq
let polyveck_add = map2 #poly #poly #poly #param_k poly_add
let polyveck_sub = map2 #poly #poly #poly #param_k poly_sub
let polyveck_modq = map #poly #poly #param_k poly_modq

let polyveck_freeze: (polyveck -> vec:polyveck{polyveck_is_stdreps vec}) = map #poly #poly #param_k poly_freeze
let polyvecl_freeze: (polyvecl -> vec:polyvecl{polyvecl_is_stdreps vec}) = map #poly #poly #param_l poly_freeze

val polyvecl_pointwise_acc: polyvecl -> polyvecl -> poly

let polyvecl_pointwise_acc v1 v2 =
  repeati param_l
    (fun i w -> (poly_add w (poly_pointwise_mont v1.[i] v2.[i])))
    new_poly


val poly_le_norm_bounded':
    i:nat {i < param_n}
  -> b:nat
  -> p:poly{poly_is_stdreps p /\ (forall (j: nat {j < i}) . norm_q (v p.[j]) <= b)}
  -> Tot (r:bool{r <==> poly_norm_bound p (b+1)}) (decreases (param_n - i))

let rec poly_le_norm_bounded' i b p =
  if norm_q (v p.[i]) <= b
  then if i+1 < param_n
    then poly_le_norm_bounded' (i+1) b p
    else true
  else false


// in theory we should get a bidirectional implication...
// can't get it to work
val poly_le_norm_bounded:
    p:poly{poly_is_stdreps p}
  -> b:nat
  -> Tot (r:bool{r ==> poly_norm_bound p (b+1)})

let poly_le_norm_bounded p b =
  poly_le_norm_bounded' 0 b p


val polyveck_le_norm_bounded':
    i:nat {i < param_k}
  -> b:nat
  -> vec:polyveck{polyveck_is_stdreps vec /\ (forall (j: nat {j < i}) . poly_norm_bound vec.[j] (b+1))}
  -> Tot (r:bool{r <==> polyveck_norm_bound vec (b+1)}) (decreases (param_k - i))

let rec polyveck_le_norm_bounded' i b vec =
  if poly_le_norm_bounded vec.[i] b
  then if i+1 < param_k
    then polyveck_le_norm_bounded' (i+1) b vec
    else true
  else false


val polyveck_le_norm_bounded:
    p:polyveck{polyveck_is_stdreps p}
  -> b:nat
  -> Tot (r:bool{r ==> polyveck_norm_bound p (b+1)})

let polyveck_le_norm_bounded p b =
  polyveck_le_norm_bounded' 0 b p


val polyvecl_le_norm_bounded':
    i:nat {i < param_l}
  -> b:nat
  -> vec:polyvecl{polyvecl_is_stdreps vec /\ (forall (j: nat {j < i}) . poly_norm_bound vec.[j] (b+1))}
  -> Tot (r:bool{r <==> polyvecl_norm_bound vec (b+1)}) (decreases (param_l - i))

let rec polyvecl_le_norm_bounded' i b vec =
  if poly_le_norm_bounded vec.[i] b
  then if i+1 < param_l
    then polyvecl_le_norm_bounded' (i+1) b vec
    else true
  else false

val polyvecl_le_norm_bounded:
    p:polyvecl{polyvecl_is_stdreps p}
  -> b:nat
  -> Tot (r:bool{r ==> polyvecl_norm_bound p (b+1)})

let polyvecl_le_norm_bounded p b =
  polyvecl_le_norm_bounded' 0 b p


let poly_chknorm (p:poly{poly_is_stdreps p}) b = not (poly_le_norm_bounded p b)
let polyveck_chknorm (vec:polyveck{polyveck_is_stdreps vec}) b = not (polyveck_le_norm_bounded vec b)
let polyvecl_chknorm (vec:polyvecl{polyvecl_is_stdreps vec}) b = not (polyvecl_le_norm_bounded vec b)


val decompose:
    a: uint32 {v a < param_q}
  -> a': (uint32 & uint32) {
      let a0, a1 = a' in
        v a1 < 16 /\ v a0 <= param_q + gamma2 /\ v a0 >= param_q - gamma2}

let decompose a =
  assert (alpha = (param_q-1)/16);
  assert (gamma2 = alpha/2);

  assert (v a <= 16 * alpha);
  let a1 = v a / alpha in
  assert (a1 <= 16);
  //calc (<) {v a1; = {} v a / alpha; <= {} 16};
  let a0 = v a % alpha in
  assert (a0 < alpha);
  let a0, a1 = if a0 > gamma2 then (a0 - alpha), (a1+1) else a0, a1 in
  let a0, a1 = if a1 = 16 then v a - param_q, 0 else a0, a1 in
  assert (a0 <= gamma2 /\ a0 >= -gamma2);
  u32 (param_q + a0), u32 a1


val polyveck_decompose':
    i:nat{i < param_k}
  -> j:nat{j < param_n}
  -> v0:polyveck
  -> v1:polyveck {polyveck_is_4bit v1}
  -> vec:polyveck {polyveck_is_stdreps vec}
  -> Tot (vecs:(polyveck & polyveck) {let _,v1' = vecs in polyveck_is_4bit v1'})
      (decreases %[param_k-i;param_n-j])

let rec polyveck_decompose' i j v0 v1 vec =
  let a0, a1 = decompose vec.[i].[j] in
  let v0 = (v0.[i] <- (v0.[i]).[j] <- a0) in
  assert(v a1 < 16);
  assert (poly_is_4bit v1.[i]);
  let v1' = (v1.[i] <- (v1.[i]).[j] <- a1) in
  assert (forall (k:nat{k < param_n}). v (v1.[i]).[k] < 16);
  assert (poly_is_4bit v1'.[i]);
  assert (forall k. k < param_n /\ k <> i ==> v1.[k] == v1'.[k]);
  assert (polyveck_is_4bit v1');
  let v1 = v1' in
  if j+1 < param_n then
    polyveck_decompose' i (j+1) v0 v1 vec
  else if i+1 < param_k then
    polyveck_decompose' (i+1) 0 v0 v1 vec
  else (v0, v1)


let polyveck_decompose = polyveck_decompose' 0 0 new_polyveck new_polyveck


let polyveck_shiftl (vec:polyveck) =
  map (fun p -> map (fun x -> x <<. size param_d) p) vec


val polyveck_use_hint: a:polyveck {polyveck_is_stdreps a} -> h:polyveck {polyveck_bound h 2}
  -> (r:polyveck {polyveck_is_4bit r})

let polyveck_use_hint a h =
  let apply_hint i j : (x:uint32 {v x < 16}) =
    let a0, a1 = decompose a.[i].[j] in
      logand_le (a1 +. u32 1) (u32 0xf);
      logand_le (a1 -. u32 1) (u32 0xf);
      if v h.[i].[j] = 0 then a1 else
      if v a0 > param_q then (a1 +. u32 1) &. u32 0xf else (a1 -. u32 1) &. u32 0xf in
  let apply_hint_poly i : (p:poly {poly_is_4bit p}) = createi param_n (apply_hint i) in
  let vec: polyveck = createi param_k apply_hint_poly in vec


// maps x where |x| < gamma1 to a value <= 2 * gamma1 - 2 for packing
let spec_map_2gamma1 (x:uint32{v x < param_q /\ norm_q (v x) < gamma1}) : (y:uint32 {v y < 2 * gamma1}) =
  u32 (gamma1 - 1 - center_q (v x))


let map_2gamma1 (x:uint32 {range (v x) S32}) : uint32 =
  let (y:int32) = i32 (gamma1 - 1) -! to_i32 x in
  let z = u32 param_q &. to_u32 (y >>. size 31) in
  to_u32 y +. z


let map_2gamma1_spec_equiv (x:uint32 {v x < param_q /\ norm_q (v x) < gamma1})
  : Lemma (map_2gamma1 x == spec_map_2gamma1 x) =
  let (y:int32) = i32 (gamma1 - 1) -! to_i32 x in
  let z = u32 param_q &. to_u32 (y >>. size 31) in
  assert (to_u32 y +. z == map_2gamma1 x);

  // these asserts can probably be pruned down
  let cx = center_q (v x) in
  assert (cx < 0 ==> to_u32 (y >>. size 31) == ones U32 SEC);
  logand_ones (u32 param_q);
  assert (cx < 0 ==> v z = param_q);

  assert (cx >= 0 ==> v x <= param_q/2);
  assert (v x <= param_q/2 ==> v y >= 0);
  assert (v y >= 0 ==> v (to_u32 (y >>. size 31)) = 0);
  assert (v y >= 0 ==> v (y >>. size 31) = 0);

  assert (z == (u32 param_q &. to_u32 (y >>. size 31)));
  logand_le (u32 param_q) (to_u32 (y >>. size 31));
  assert (cx >= 0 ==> v z = 0);

  assert (cx < 0 ==> (v y) + (v z) = param_q + gamma1 - 1 - (v x));
  assert ((v y) + (v z) = gamma1 - 1 - cx);

  assert (u32 ((v y) + (v z)) == spec_map_2gamma1 x);
  assert ((v y) + (v z) = v (spec_map_2gamma1 x));
  assert ( v (to_u32 y +. u32 (v z)) = (v y) + (v z));
  assert (to_u32 y +. z == u32 ((v y) + (v z)))


val power2_round: a:nat {a < param_q} ->
  (a': (nat & int) {let a1, a2 = a' in let pow2d = pow2 param_d in
    (a1 <= param_q/pow2d /\ a = a1 * pow2d + a2 - param_q /\ param_q-pow2d/2 < a2 /\ a2 <= param_q+pow2d/2)})

let power2_round a =
  let pow2d = pow2 param_d in
  let a1 = (a + pow2d / 2 - 1) / pow2d in
  let a2 = a - (a1 * pow2d) in
  assert (a = a1 * pow2d + a2);
  assert (a2 <= pow2d/2);
  assert (a2 > -pow2d/2);
  a1, param_q + a2

let poly_power2_round (p:poly {poly_is_stdreps p}) =
  repeati param_n (fun i (p1, p2) ->
    let a1, a2 = power2_round (v p.[i]) in
    let p1 = p1.[i] <- u32 a1 in
    let p2 = p2.[i] <- u32 a2 in
    p1, p2) (new_poly, new_poly)

let polyveck_power2_round (vec:polyveck {polyveck_is_stdreps vec}) =
  repeati param_k (fun i (v1, v2) ->
    let p1, p2 = poly_power2_round vec.[i] in
    let v1 = v1.[i] <- p1 in
    let v2 = v2.[i] <- p2 in
    v1, v2) (new_polyveck, new_polyveck)


(* Given y in s ==> p(y) and p(x), then y in s ==> p(y) still holds after s.[i] <- x *)

val lemma_seq_assignment_predicate:
    #n: size_nat
  -> #a: Type
  -> s: lseq a n
  -> i: nat {i < n}
  -> x: a
  -> p: (a -> (Tot Type0))
  -> Lemma (requires (p x /\ (forall j. p s.[j]))) (ensures (forall j. p (s.[i] <- x).[j]))

let lemma_seq_assignment_predicate #n #a s i x p =
  let s' = s.[i] <- x in
  assert (forall j. j <> i ==> s'.[j] == s.[j]);
  assert (forall j. j <> i ==> p s'.[j]);
  assert (p s'.[i]);
  assert (forall j. p s'.[j])
