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


open FStar.Seq
open FStar.Math.Lib

open FStar.Mul


#set-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

let w = 5
let m = pow2 w

val from_wnaf_: l: seq int -> i: nat {i <= Seq.length l} -> Tot int
  (decreases Seq.length l -  i)

let rec from_wnaf_ l i  =
  if i = Seq.length l then 0
  else 
    Seq.index l i + from_wnaf_ l (i + 1) * m

val from_wnaf: l: seq int {Seq.length l > 0} -> Tot int

let from_wnaf l = from_wnaf_ l 0


#push-options "--max_ifuel 2 --max_fuel 2"

val lemma_from_wnaf_last: l: seq int {Seq.length l > 0} 
  -> Lemma (from_wnaf_ l (Seq.length l - 1) == Seq.index l (Seq.length l - 1))

let lemma_from_wnaf_last l = ()


val lemma_from_wnaf_next: l: seq int -> i: nat {i < Seq.length l} -> Lemma (
  from_wnaf_ l i == Seq.index l i + from_wnaf_ l (i + 1) * m)

let lemma_from_wnaf_next l i = ()


val to_wnaf_: d: nat {d % 2 == 1} -> n: nat {d < pow2 n} -> l: seq int {Seq.length l == n / w + 1}
  -> i: nat{i < Seq.length l}
  -> Tot (r: seq int {Seq.length r == n / w + 1 /\ from_wnaf_ r i == d / pow2 (i * w + 1) * 2 + 1 /\ (
    forall (k: nat {k < i}). index r k == index l k) /\ (
    if i = Seq.length l - 1 then 
      index r i == d / pow2 (n / w * w + 1) * 2 + 1
    else ((
      forall (j: nat {j >= i /\ j < Seq.length l - 1}).
	index r j == (2 * (d / pow2 (w * j + 1)) + 1) % (2 * m) - m) /\
      index r (Seq.length l - 1) == d / pow2 (n / w * w + 1) * 2 + 1))})
  (decreases (Seq.length l - i))

let rec to_wnaf_ d n l i = 
  if i = Seq.length l - 1 then 
    begin
      let w_i = d / pow2 (n / w * w + 1) * 2 + 1 in
      upd l i w_i
    end
  else 
    begin
      let w_i = (2 * (d / pow2 (w * i + 1)) + 1) % (2 * m) - m in 
      let l0 = upd l i w_i in 
      let r = to_wnaf_ d n l0 (i + 1) in 

      assert(from_wnaf_ r (i + 1) == d / pow2 ((i + 1) * w + 1) * 2 + 1 /\ (
	forall (j: nat {j >= i + 1 /\ j < Seq.length l0 - 1}).
	  index r j == (2 * (d / pow2 (w * j + 1)) + 1) % (2 * m) - m) /\
	index r (Seq.length l - 1) == d / pow2 (n / w * w + 1) * 2 + 1);


      assert(from_wnaf_ r (i + 1) == d / pow2 ((i + 1) * w + 1) * 2 + 1);
      assert(from_wnaf_ r i == (d / pow2 (w * i + 1) * 2 + 1) % (2 * m) + d / pow2 ((i + 1) * w + 1) * 2 * m);

      assert(d / pow2 (i * w + 1) * 2 + 1 == (d / pow2 (i * w + 1) * 2 + 1) % (2 * m) + (d / pow2 (i * w + 1) * 2 + 1) / (2 * m) * (2 * m));


      FStar.Math.Lemmas.division_multiplication_lemma d ( pow2 (i * w + 1)) (pow2 w);
      FStar.Math.Lemmas.pow2_plus (i * w + 1) w;

      assert((d / pow2 (i * w + 1) * 2) / (2 * m) == (d / (pow2 (i * w + 1 +  w)))); 

      assert (
	 d / pow2 ((i + 1) * w + 1) ==	(d / pow2 (i * w + 1) * 2 + 1) / (2 * m));

      r
    end
    
#pop-options


val to_wnaf: n: nat -> d: nat {d < pow2 n /\ d % 2 == 1} -> 
  Tot (r: seq int {Seq.length r == n / w + 1 /\ from_wnaf r == d /\ (
    forall (j: nat {j < n / w}).
      index r j == (2 * (d / pow2 (w * j + 1)) + 1) % (2 * m) - m) /\
    index r (n / w) == d / pow2 (n / w * w + 1) * 2 + 1})

let to_wnaf n d = 
  let s = Seq.Base.create #int (n / w + 1) 0 in 
  to_wnaf_ d n s 0


val getPrecomputed: #c: curve -> g: point #c #Jacobian -> s: int -> Tot (point #c #Jacobian)

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


val wnaf_step2: #c: curve 
  -> p0: point #c #Jacobian {~ (isPointAtInfinity p0)}
  -> s: seq int
  -> i: nat{i < Seq.length s} 
  -> q: point #c #Jacobian ->  
  Tot (point #c #Jacobian)

let wnaf_step2 #c p0 s i q =
  let i = length s - (i + 1) in 
  let bits = index s i * pow2 (w * i) in 
  pointAdd q (getPrecomputed p0 bits)


#push-options "--max_ifuel 1 --max_fuel 1"

val from_wnaf_lemma_0: l: seq int -> Lemma (from_wnaf_ l (Seq.length l) == 0)

let from_wnaf_lemma_0 l = ()

#pop-options


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


val pred1: #c: curve -> l: seq int 
  -> p0: point #c #Jacobian {~ (isPointAtInfinity p0)}
  -> i: nat {i < length l} -> x: point #c #Jacobian -> Lemma (
    let len = length l in 
    let f = wnaf_step2 p0 l in 
    let pred (i: nat {i <= length l}) (p: point #c #Jacobian) : Type0 = 
      let partialScalar = from_wnaf_ l (len - i) * pow2 (w * (len - i)) in  
      pointEqual p (point_mult partialScalar p0) in 
    pred i x ==> pred (i + 1) (f i x))


#push-options "--max_fuel 1 --max_ifuel 1"

let pred1 #c l p0 i x = 
  let len = length l in 
  let partialScalar_i = from_wnaf_ l (len - i) * pow2 (w * (len - i)) in  
  if pointEqual x (point_mult partialScalar_i p0) then begin
    let f_i_x = wnaf_step2 p0 l i x in 
    let i' = len - (i + 1) in 


      assert(pointEqual f_i_x (pointAdd x (point_mult (index l i' * pow2 (w * i')) p0)));
    curve_compatibility_with_translation_lemma x (point_mult partialScalar_i p0) (point_mult (index l i' * pow2 (w * i')) p0);
      assert(pointEqual f_i_x (pointAdd (point_mult partialScalar_i p0) (point_mult (index l i' * pow2 (w * i')) p0)));
    lemmaApplPointAdd p0 partialScalar_i (point_mult partialScalar_i p0) (index l i' * pow2 (w * i')) (point_mult (index l i' * pow2 (w * i')) p0);
      assert (pointEqual f_i_x (point_mult (partialScalar_i + index l i' * pow2 (w * i')) p0));
      assert (pointEqual f_i_x (point_mult (from_wnaf_ l (i' + 1) * pow2 (w * (i' + 1)) + index l i' * pow2 (w * i')) p0));

    let open FStar.Tactics in 
    let open FStar.Tactics.Canon in 

    assert_by_tactic (from_wnaf_ l (i' + 1) * (pow2 (w * i') * pow2 w) == pow2 (w * i') * (from_wnaf_ l (i' + 1) * pow2 w)) canon;

    
    calc (==) {
      from_wnaf_ l (i' + 1) * pow2 (w * (i' + 1)) + index l i' * pow2 (w * i');
    (==) {FStar.Math.Lemmas.pow2_plus (i' * w) w }
      from_wnaf_ l (i' + 1) * (pow2 (w * i') * pow2 w) + index l i' * pow2 (w * i');
    (==) {assert_by_tactic (from_wnaf_ l (i' + 1) * (pow2 (w * i') * pow2 w) == pow2 (w * i') * (from_wnaf_ l (i' + 1) * pow2 w)) canon}
      pow2 (w * i') * (from_wnaf_ l (i' + 1) * pow2 w) + pow2 (w * i') * index l i';
    (==) {FStar.Math.Lemmas.distributivity_add_right (pow2 (w * i')) (from_wnaf_ l (i' + 1) * pow2 w) ( index l i')}
      pow2 (w * i') * (from_wnaf_ l (i' + 1) * pow2 w + index l i');};

    assert(from_wnaf_ l i' == index l i' + from_wnaf_ l (i' + 1) * m);
    assert (pointEqual f_i_x (point_mult ((index l i' + from_wnaf_ l (i' + 1) * m) * pow2 (w * i')) p0))

   end


val wnaf_spec_pred0: #c: curve -> l: seq int -> p0: point #c #Jacobian {~ (isPointAtInfinity p0)} -> Lemma (
    let len = length l in 
    let f = wnaf_step2 p0 l in 
    let pred (i: nat {i <= length l}) (p: point #c #Jacobian) : Type0 = 
      let partialScalar = from_wnaf_ l (len - i) * pow2 (w * (len - i)) in  
      pointEqual p (point_mult partialScalar p0) in 
    forall (i:nat{i < length l}) (x:point #c #Jacobian). pred i x ==> pred (i + 1) (f i x))

let wnaf_spec_pred0 #c l p0 = 
  let pred = pred1 #c in 
  Classical.forall_intro_4 pred



val wnaf_spec: #c: curve 
  -> s: scalar_bytes #c {scalar_as_nat s < getOrder #c /\ scalar_as_nat s % 2 == 1} 
  -> p0: point #c #Jacobian {~ (isPointAtInfinity p0)}
  -> r: point #c #Jacobian {
    pointEqual r (point_mult #c (scalar_as_nat #c s) p0)}

let wnaf_spec #c s p0 = 
  let scalarNat = scalar_as_nat #c s in 
  
  let scalar_as_wnaf = to_wnaf (getPower c) scalarNat in 
  let len = Seq.length scalar_as_wnaf in 

  let pred (i: nat {i <= len}) (p: point #c #Jacobian) : Type0 = 
    let partialScalar = from_wnaf_ scalar_as_wnaf (len - i) * pow2 (w * (len - i)) in  
    pointEqual p (point_mult partialScalar p0) in 

  let q = 0, 0, 0 in
  let f = wnaf_step2 p0 scalar_as_wnaf in 
  (* pred 0 holds *)
  from_wnaf_lemma_0 scalar_as_wnaf; 
  point_mult_0 p0 0;  

  wnaf_spec_pred0 #c scalar_as_wnaf p0;


  repeati_inductive' #(point #c #Jacobian) len pred f q



assume val lemma_from_domain: #c: curve -> d: nat {d < pow2 (getPower c) /\ d % 2 == 1} ->
  Lemma (
    let n = (getPower c)in 
    let s = to_wnaf n d in  
    forall (i: nat {i < Seq.length s}).
      from_wnaf_ s i == d / pow2 (i * w + 1) * 2 + 1)


val lemma_test: #c: curve
  -> s: scalar_bytes #c {scalar_as_nat s < getOrder #c /\ scalar_as_nat s % 2 == 1}
  -> i: nat {
    let scalarNat = scalar_as_nat #c s in 
    let scalar_as_wnaf = to_wnaf (getPower c) scalarNat in 
    let len = Seq.length scalar_as_wnaf in 
    i < len - 1 /\ i > 0} -> 
  Lemma (
    let len = getPower c / w in 
    let scalarNat = scalar_as_nat #c s in 
    let scalar_as_wnaf = to_wnaf (getPower c) scalarNat in 
    let len = length scalar_as_wnaf in 
    let i' = len - (i + 1) in 
    from_wnaf_ scalar_as_wnaf (len - i) * pow2 (w * (len - i)) <> index scalar_as_wnaf i' * pow2 (w * i'))


let lemma_test #c s i = 
  let len = getPower c / w in 
  let d = scalar_as_nat #c s in 
  let scalar_as_wnaf = to_wnaf (getPower c) d in 
  let len = length scalar_as_wnaf in 
  let i' = len - (i + 1) in 

  let o = getOrder #c in 


  FStar.Math.Lemmas.pow2_plus (w * (len - 1 - i)) w;
  assert (pow2 (w * (len - i)) == pow2 (w * (len - 1 - i)) * pow2 w);

  lemma_from_domain #c d;

  assert(from_wnaf_ scalar_as_wnaf (len - i) == d / pow2 ((getPower c / w - i) * w + 1) * 2 + 1);

  
  

  assume ((d / pow2 ((len - i) * w + 1) * 2 + 1) * pow2 w % o <> index scalar_as_wnaf i' % o);
  assert (from_wnaf_ scalar_as_wnaf (len - i) * pow2 w % o <> index scalar_as_wnaf i' % o);

  assume(from_wnaf_ scalar_as_wnaf (len - i) * (pow2 (w * (len - 1 - i)) * pow2 w) % o <> index scalar_as_wnaf i' * pow2 (w * (len - i - 1)) % o)
