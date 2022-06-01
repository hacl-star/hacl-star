module Spec.ECC.WNAF

open FStar.Mul

open Lib.ByteSequence
open Lib.IntTypes
open Lib.Sequence

open Lib.LoopCombinators 
open Lib.Loops

open Spec.ECC.Curves
open Spec.ECC
open Spec.ECC.Radix

open FStar.Math.Lib

open FStar.Mul

#set-options "--z3rlimit 100"

let w = 4 
let m = pow2 w


val test: n: nat{n > w} -> d: nat {d < pow2 n} -> Lemma (
  let d_i = d % (2 * m) - m in 
  let d = div (d - d_i) m in 
  d < pow2 (n - w))

let test n d = 
  let di = d % (2 * m) - m in 
  assert(d % (2 * m) < 2 * m);

  assert(d - di < pow2 n + pow2 w);
  FStar.Math.Lemmas.pow2_plus (n - w) w;
  assert((d - di) / pow2 w < pow2 w * (pow2 (n - w)))


val to_wnaf_scalar_step: d: int -> Tot 
  (r: tuple2 int int {
    let d_i, d_upd = r in 
      d = d_i + d_upd * m /\ d_upd == div (d - (d % (2 * m) - m)) m})

let to_wnaf_scalar_step d = 
  let d_i = d % (2 * m) - m in 
  let d = div (d - d_i) m in 
  d_i, d


open FStar.Seq

val to_wnaf_: d: int -> l: seq int -> Tot (seq int)
  (decreases d)

let rec to_wnaf_ d l = 
  if d <= m then
    begin
      cons d l
    end
  else
    let d', di = to_wnaf_scalar_step d in 
    assume (d' << d);
    to_wnaf_ d' (cons di l)


val from_wnaf_: l: seq int -> i: nat -> Tot int
  (decreases (Seq.length l - i))

let rec from_wnaf_ l i  =
  if i >= Seq.length l then 0 
  else 
    Seq.index l i + from_wnaf_ l (i + 1) * m


val from_wnaf: l: seq int -> Tot int

let from_wnaf l = from_wnaf_ l 0

val lemma_from_0_: l: nat -> i: nat {i < l} -> s: seq int {length s == l /\
  (forall (j: nat {j < Seq.length s /\ j >= l - i}). index s j == 0)} -> Lemma (from_wnaf_ s (l - i) == 0)

let rec lemma_from_0_ l i s = 
  match i with
  | 0 -> ()
  | _ -> lemma_from_0_ l (i - 1) s


val lemma_from_0: l: nat -> i: pos {i < l} 
  -> s: seq int{length s == l /\ (forall (j: nat {j < l /\ j >= i}). index s j == 0)} -> Lemma
  (from_wnaf_ s i == 0)

let lemma_from_0 l i s = lemma_from_0_ l (l - i) s


val to_wnaf2_: n0: nat -> d: int -> l: seq int {Seq.length l == n0 / w + 1}
  -> i: nat{i < Seq.length l /\ d < pow2 (n0 - i * w) /\ (
    forall (j: nat {j < Seq.length l /\ j > i}). index l j == 0)}
  -> Tot (r: seq int {Seq.length r == n0 / w + 1 /\
    from_wnaf_ r i == d /\ (
    forall (j: nat {j < i}). index r j == index l j) /\ (
    if d <= m then index r i == d /\ (forall (j: nat {j < Seq.length r /\ j > i}). index r j == 0)
    else index r i == d % (2 * m) - m)})
  (decreases (Seq.length l - i))


let rec to_wnaf2_ n0 d l i = 
  if d <= m then 
    begin
      let r = upd l i d in
      if (i + 1 < length l) then 
	  lemma_from_0 (length l) (i + 1) r;
      r
    end
  else
    begin
      let di, d' = to_wnaf_scalar_step d in 
      let r = upd l i di in 
	test (n0 - i * w) d;  
      to_wnaf2_ n0  d' r (i + 1)
    end


val to_wnaf: n: nat -> d: nat {d < pow2 n} -> Tot (r: seq int {Seq.length r == n / w + 1 /\ from_wnaf r == d})

let to_wnaf n d = 
  let s = Seq.Base.create #int (n / w + 1) 0 in 
  to_wnaf2_ n d s 0


val getPrecomputed: #c: curve -> g: point #c #Jacobian -> s: int -> Tot (p: point #c #Jacobian)

let getPrecomputed #c g s = 
    point_mult s g


val wnaf_step: #c: curve 
  -> p0: point #c #Jacobian {~ (isPointAtInfinity p0)}
  -> s: seq int
  -> i: nat{i < Seq.length s} 
  -> q: point #c #Jacobian ->  
  Tot (point #c #Jacobian)

let wnaf_step #c p0 s i q = 
  let q = getPointDoubleNTimes #c q w in 
  let bits = index s (length s - (i + 1)) in 
  pointAdd q (getPrecomputed p0 bits)


val from_wnaf_lemma_0: l: seq int -> Lemma (from_wnaf_ l (Seq.length l) == 0)

let from_wnaf_lemma_0 l = ()



#push-options "--z3rlimit 200"


val pred0: #c: curve -> l: seq int 
  -> p0: point #c #Jacobian {~ (isPointAtInfinity p0)}
  -> i: nat {i < length l} -> x: point #c #Jacobian -> Lemma (
    let len = length l in 
    let f = wnaf_step p0 l in 
    let pred (i: nat {i <= length l}) (p: point #c #Jacobian) : Type0 = 
      let partialScalar = from_wnaf_ l (len - i) in  
      pointEqual p (point_mult partialScalar p0) in 
    pred i x ==> pred (i + 1) (f i x))


let pred0 #c l p0 i x = 
  let len = length l in 
  let partialScalar_i = from_wnaf_ l (len - i) in  
  if pointEqual x (point_mult partialScalar_i p0) then begin
    let f_i_x = (wnaf_step p0 l) i x in 
    let q = getPointDoubleNTimes #c x w in 


    assert(pointEqual x (point_mult partialScalar_i p0));
    assert(pointEqual q (point_mult m x));


    let k = index l (len - (i + 1)) in 

    curve_multiplication_distributivity #c p0 partialScalar_i x m (getPointDoubleNTimes #c x w);
    assert(pointEqual #c q (point_mult #c (partialScalar_i * m) p0));
    
    curve_compatibility_with_translation_lemma #c q (point_mult #c (m * partialScalar_i) p0) (point_mult k p0);
    lemmaApplPointAdd #c p0 (m * partialScalar_i) (point_mult #c (m * partialScalar_i) p0) k (point_mult k p0);

    assert(pointEqual f_i_x (pointAdd (point_mult (partialScalar_i * m) p0) (point_mult k p0)));

    assert(pointEqual f_i_x (point_mult (from_wnaf_ l (len - i) * m + k) p0));



    assert(from_wnaf_ l (len - (i + 1)) == index l (len - (i + 1)) + from_wnaf_ l (len - i) * m)

   end


val wnaf_spec_pred0: #c: curve -> l: seq int -> p0: point #c #Jacobian {~ (isPointAtInfinity p0)} -> Lemma (
    let len = length l in 
    let f = wnaf_step p0 l in 
    let pred (i: nat {i <= length l}) (p: point #c #Jacobian) : Type0 = 
      let partialScalar = from_wnaf_ l (len - i) in  
      pointEqual p (point_mult partialScalar p0) in 
    forall (i:nat{i < length l}) (x:point #c #Jacobian). pred i x ==> pred (i + 1) (f i x))

let wnaf_spec_pred0 #c l p0 = 
  let pred = pred0 #c in 
  Classical.forall_intro_4 pred


val wnaf_spec: #c: curve 
  -> s: scalar_bytes #c {scalar_as_nat s < getOrder #c}
  -> p0: point #c #Jacobian {~ (isPointAtInfinity p0)}
  -> r: point #c #Jacobian {
    pointEqual r (point_mult #c (scalar_as_nat #c s) p0)}

let wnaf_spec #c s p0 = 
  let scalarNat = scalar_as_nat #c s in 
  
  let scalar_as_wnaf = to_wnaf (getPower c) scalarNat in 
  let len = Seq.length scalar_as_wnaf in 

  let pred (i: nat {i <= len}) (p: point #c #Jacobian) : Type0 = 
    let partialScalar = from_wnaf_ scalar_as_wnaf (len - i) in  
    pointEqual p (point_mult partialScalar p0) in 

  let q = 0, 0, 0 in 
  let f = wnaf_step p0 scalar_as_wnaf in 
  
  (* pred 0 holds *)
  from_wnaf_lemma_0 scalar_as_wnaf; 
  point_mult_0 p0 0;  

  wnaf_spec_pred0 #c scalar_as_wnaf p0;
  repeati_inductive' #(point #c #Jacobian) len pred f q
  
