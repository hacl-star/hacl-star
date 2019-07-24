module Lib.Arithmetic.Sums

open FStar.Tactics.Typeclasses

open Lib.Arithmetic.Group
open Lib.Arithmetic.Ring

open FStar.Math.Lemmas

open Spec.Powtwo.Lemmas
open FStar.Mul
open FStar.UInt
open FStar.Seq
open Lib.Sequence

module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators

#reset-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0"

let br i x =
  let v = UInt.to_vec #i x in
  let vbr = Seq.createi i (fun p -> (Seq.index #_ #i v (i-1-p))) in
  UInt.from_vec #i vbr

#reset-options "--z3rlimit 200 --max_fuel 1 --max_ifuel 1"

let rec to_vec_equal_lemma (i:size_nat) (p:size_nat{p > 0 /\ i+p <= max_size_t}) (x:nat{x<pow2 i /\ x<pow2 (i+p)}) : Lemma (ensures (Seq.sub #_ #(i+p) (UInt.to_vec #(i+p) x) p i == UInt.to_vec #i x)) (decreases (i+p)) =
  let vp : lseq bool (i+p) = UInt.to_vec #(i+p) x in
  let v1 : lseq bool i = Seq.sub #_ #(i+p) vp p i in
  let v2 : lseq bool i = UInt.to_vec #i x in
  if (i=0) then eq_intro v1 v2
  else begin
    let s1 : lseq bool (i+p-1) = (UInt.to_vec #(i+p-1) (x/2)) in
    let s2 : lseq bool (i-1) = (UInt.to_vec #(i-1) (x/2)) in
    let s = create 1 (x%2=1) in
    Seq.Properties.lemma_slice_first_in_append s1 s p;
    assert(v1 == Seq.concat (Seq.slice s1 p (i+p-1)) s);
    to_vec_equal_lemma (i-1) p (x/2);
    eq_intro v1 v2
  end

let br_lemma_rec i x =
  if (i=0) then begin
    assert(x=0);
    assert(br 0 0 = 0);
    let v = UInt.to_vec #1 x in
    let vbr = Seq.createi 1 (fun p -> (Seq.index #_ #1 v (1-1-p))) in
    assert_norm(from_vec #1 vbr == br 1 x);
    eq_intro #_ #1 v (BitVector.zero_vec #1);
    eq_intro #_ #1 v vbr;
    zero_from_vec_lemma #1
    end
  else begin
  let v1:lseq bool i = UInt.to_vec #i x in
  let v1br = Seq.createi i (fun p -> (Seq.index #_ #i v1 (i-1-p))) in
  assert(from_vec #i v1br == br i x);
  let v2:lseq bool (i+1) = UInt.to_vec #(i+1) x in
  let v2br = Seq.createi (i+1) (fun p -> (Seq.index #_ #(i+1) v2 ((i+1)-1-p))) in
  assert_norm(from_vec #(i+1) v2br == br (i+1) x);
  to_vec_equal_lemma i 1 x;
  from_vec_propriety #(i+1) v2 1;
  assert(from_vec #1 (slice v2 0 1) = 0);
  zero_from_vec_lemma #1;
  assert(v2.[0] = false);
  assert(v2br.[i] = false);
  from_vec_propriety #(i+1) v2br i;
  eq_intro v1br (Seq.sub v2br 0 i)
  end

let rec br_lemma_zero i : Lemma (ensures br i 0 = 0) (decreases i) =
  if i = 0 then ()
  else (br_lemma_zero (i-1); br_lemma_rec (i-1) 0)

let rec br_lemma_one (i:size_nat{i>0}) : Lemma (ensures br i 1 = pow2 (i-1)) (decreases i) =
  if (i = 1) then
    let v = UInt.to_vec #1 1 in
    let vbr = Seq.createi 1 (fun p -> (Seq.index #_ #1 v (1-1-p))) in
    assert_norm(from_vec #1 vbr == br 1 1);
    eq_intro #_ #1 v (BitVector.ones_vec #1);
    eq_intro #_ #1 v vbr;
    ones_from_vec_lemma #1
  else
    (br_lemma_one (i-1); br_lemma_rec (i-1) 1)

let br_lemma_n2_1 i x =
  if (i=0) then begin
    assert(x=0);
    br_lemma_zero 1;
    br_lemma_one 1
    end
  else begin
  let v0:lseq bool i = UInt.to_vec #i x in
  let v0br = Seq.createi i (fun p -> (Seq.index #_ #i v0 (i-1-p))) in
  assert(from_vec #i v0br == br i x);
  let v1:lseq bool (i+1) = UInt.to_vec #(i+1) (x+pow2 i) in
  let v1br:lseq bool (i+1) = Seq.createi (i+1) (fun p -> (Seq.index #_ #(i+1) v1 ((i+1)-1-p))) in
  assert_norm(from_vec #(i+1) v1br == br (i+1) (x+pow2 i));
  let v2:lseq bool (i+1) = UInt.to_vec #(i+1) x in
  let v2br:lseq bool (i+1) = Seq.createi (i+1) (fun p -> (Seq.index #_ #(i+1) v2 ((i+1)-1-p))) in
  assert_norm(from_vec #(i+1) v2br == br (i+1) x);
  to_vec_equal_lemma i 1 x;
  from_vec_propriety #(i+1) v2 1;
  zero_from_vec_lemma #1;
  assert(v2br.[i] = false);
  eq_intro v0br (Seq.sub v2br 0 i);
  from_vec_lemma_1 #i v0br (Seq.sub v2br 0 i);
  let v :lseq bool (i+1) = Seq.concat #_ #1 #i (BitVector.ones_vec #1) (Seq.sub v2 1 i) in
  append_lemma #1 #i (BitVector.ones_vec #1) (Seq.sub v2 1 i);
  assert(from_vec #(i+1) v == (x+pow2 i));
  from_vec_lemma_1 #(i+1) v1 v;
  Seq.Properties.lemma_append_inj (Seq.sub v1 0 1) (Seq.sub v1 1 i) (Seq.sub v 0 1) (Seq.sub v2 1 i);
  from_vec_lemma_1 #1 (Seq.sub v1 0 1) (Seq.sub v 0 1);
  assert(v1br.[i] = true);
  eq_intro (Seq.sub v1br 0 i) (Seq.sub v2br 0 i);
  from_vec_lemma_1 #i (Seq.sub v1br 0 i) (Seq.sub v2br 0 i);
  from_vec_propriety #(i+1) v1br i;
  assert(from_vec #1 (Seq.sub v1br i 1) == 1)
  end

let rec br_lemma_pow (i:size_nat{i>0}) (p:size_nat{p < i /\ pow2 p < pow2 i}) : Lemma (ensures br i (pow2 p) = pow2 (i-1-p)) (decreases i) =
  if (i = 1 || p = 0) then br_lemma_one i
  else if (p = i - 1) then (br_lemma_n2_1 (i-1) 0; br_lemma_zero i)
  else (pow2_lt_compat (i-1) p; br_lemma_rec (i-1) (pow2 p); br_lemma_pow (i-1) p; pow2_double_mult ((i-1)-1-p))

let br_involutive i x =
  let v1 = UInt.to_vec #i x in
  let v1br = Seq.createi i (fun p -> (index #_ #i v1 (i-1-p))) in
  assert (forall (j:nat{j<i}). index #_ #i v1br j = index #_ #i v1 (i-1-j));
  let xbr:(y:nat{y<pow2 i}) = UInt.from_vec #i v1br in
  assert(xbr = br i x);
  let v2 = UInt.to_vec #i xbr in
  assert (Seq.equal v2 v1br);
  let v2br = Seq.createi i (fun p -> (index #_ #i v2 (i-1-p))) in
  assert (forall (j:nat{j<i}). index #_ #i v2br j = index #_ #i v2 (i-1-j));
  let x' = UInt.from_vec #i v2br in
  assert_norm (x' = br i xbr);
  assert (forall (j:nat{j<i}). index #_ #i v2br j = index #_ #i v2 (i-1-j));
  assert (forall (j:nat{j<i}). index #_ #i v2br j = index #_ #i v1br (i-1-j));
  assert (forall (j:nat{j<i}). index #_ #i v2br j = index #_ #i v1 (i-1-(i-1-j)));
  assert(Seq.equal v2br v1);
  assert (x' = br i (br i x));
  assert (x' = x)

let br_lemma_n2_2 i x =
  pow2_lt_compat (i+1) i;
  pow2_double_sum i;
  let customlemma (y:nat{y<pow2 i}) : Lemma (br (i+1) y + 1 < pow2 (i+1) /\ br (i+1) ((br (i+1) y) + 1) = y + pow2 i) =
    br_lemma_n2_1 i y;
    br_involutive (i+1) (y+pow2 i)
  in
  let x2br = br i (x/2) in
  br_lemma_rec i x2br;
  br_involutive i (x/2);
  div_exact_r x 2;
  assert(x = br (i+1) x2br);
  br_involutive (i+1) x2br;
  customlemma (br (i+1) x);
  br_involutive (i+1) x

let br_lemma_div_even (i:size_nat{i>0}) (x:nat{x<pow2 i /\ x%2 = 0}) : Lemma (br i (x/2) = (2 * br i x) % pow2 i) =
  let v1:lseq bool i = UInt.to_vec #i x in
  let v1br = Seq.createi i (fun p -> (Seq.index #_ #i v1 (i-1-p))) in
  assert(from_vec #i v1br == br i x);
  let v2:lseq bool i = UInt.to_vec #i (x/2) in
  let v2br = Seq.createi i (fun p -> (Seq.index #_ #i v2 (i-1-p))) in
  assert_norm(from_vec #i v2br == br i (x/2));
  let v0 = BitVector.shift_right_vec #i v1 1 in
  UInt.shift_right_value_lemma #i x 1;
  assert(from_vec #i v0 == (x/2));
  UInt.inverse_vec_lemma #i v0;
  assert(v0 == v2);
  let v0br :lseq bool i = Seq.createi i (fun p -> (Seq.index #_ #i v0 (i-1-p))) in
  let v0br' :lseq bool i = BitVector.shift_left_vec #i v1br 1 in
  UInt.shift_left_value_lemma #i (br i x) 1;
  assert_norm(from_vec #i v0br' == (2 * br i x) % pow2 i);
  let customprop (k:nat{k<i}) : GTot Type0 = (v2br.[k] == v0br'.[k]) in
  let customlemma (k:nat{k<i}) : Lemma (customprop k) =
    if(k=i-1) then (BitVector.shift_left_vec_lemma_1 #i v1br 1 k; BitVector.shift_right_vec_lemma_1 #i v1 1 0)
    else (BitVector.shift_left_vec_lemma_2 #i v1br 1 k; BitVector.shift_right_vec_lemma_2 #i v1 1 (i-1-k); assert(v1br.[k+1] == v1.[i-1-k-1]))
  in FStar.Classical.forall_intro customlemma;
  eq_intro v2br v0br';
  from_vec_lemma_1 #i v2br v0br'

let br_lemma_mul i x =
  pow2_double_mult (i-1);
  cancel_mul_div x 2;
  br_lemma_div_even i (2*x)

let br_lemma_div_odd (i:size_nat{i>0}) (x:nat{x<pow2 i /\ x%2 = 1}) : Lemma (br i (x/2) = (2 * br i x) % pow2 i) =
  euclidean_division_definition x 2;
  br_lemma_mul i (x/2);
  br_lemma_n2_2 (i-1) (x-1);
  assert (br i (x/2) = (2 * (br i x - pow2 (i-1))) % pow2 i);
  distributivity_sub_right 2 (br i x) (pow2 (i-1));
  pow2_double_mult (i-1);
  lemma_mod_sub (2*br i x) (pow2 i) 1

let br_lemma_div i x : Lemma (br i (x/2) = (2 * br i x) % pow2 i) =
  if(x%2=0) then br_lemma_div_even i x else br_lemma_div_odd i x


let reorg #a #n i p =
  Seq.createi n (fun x -> p.[br i x])


let reorg_involutive #a #n i p =
  let p1 = reorg i p in
  let p' = reorg i p1 in
  let customprop (k:nat{k<n}) : Type0 = p'.[k] == p.[k] in
  let customlemma (k:nat{k<n}) : Lemma (customprop k) =
    assert (p'.[k] == p.[br i (br i k)]);
    br_involutive i k
  in FStar.Classical.forall_intro customlemma;
  eq_intro p' p;
  eq_elim p' p

let split_seq #a #n p =
  let peven = createi (n/2) (fun i -> p.[2*i]) in
  let podd = createi (n/2) (fun i -> p.[2*i+1]) in
  peven,podd

let join_seq #a [|ring a|] #n peven podd =
  let f (i:nat{i<n}) : a =
    plus #a (Ring.mul (repeat_plus Ring.one ((i+1)%2)) peven.[i/2]) (Ring.mul (repeat_plus Ring.one (i%2)) podd.[i/2]) in
  let p = createi n f in
  let customprop (k:nat{k<n/2}) : Type0 = ((==) #a p.[2*k] peven.[k] /\ (==) #a p.[2*k+1] podd.[k]) in
  let customlemma (k:nat{k<n/2}) : Lemma (customprop k) =
    let m = (add_ag #a).g.m in
    //assert (p.[2*k] == peven.[k]);
    cancel_mul_mod k 2;
    lemma_repeat_op_zero #a Ring.one;
    lemma_zero_absorb1 #a podd.[(2*k)/2];
    lemma_mod_plus 1 k 2;
    lemma_repeat_op_succ1 #a Ring.one 0;
    lemma_zero2 #a Ring.one;
    cancel_mul_div k 2;
    lemma_one1 #a peven.[k];
    lemma_zero2 #a peven.[k];
    //assert (p.[2*k+1] == podd.[k]);
    distributivity_add_left k 1 2;
    cancel_mul_mod (k+1) 2;
    lemma_zero_absorb1 #a peven.[(2*k+1)/2];
    lemma_div_plus 1 k 2;
    lemma_one1 #a podd.[k];
    lemma_zero1 #a podd.[k]
    in
  FStar.Classical.forall_intro customlemma;
  p

let lemma_split_join #a [| ring a |] #n p =
  let peven,podd = split_seq p in
  let p' = join_seq peven podd in
  let customprop (k:nat{k<n}) : Type0 = (p'.[k] == p.[k]) in
  let customlemma (k:nat{k<n}) : Lemma (customprop k) =
    let i = k/2 in
    assert(i<n/2);
    if (k%2=0) then
    begin assert (k=2*i);
    calc (==) {
      p'.[k];
	== {}
      p'.[2*i];
	== {}
      peven.[i];
	== {}
      p.[2*i];
	== {}
      p.[k];
    } end else
    begin assert (k=2*i+1);
    calc (==) {
      p'.[k];
	== {}
      p'.[2*i+1];
	== {}
      podd.[i];
	== {}
      p.[2*i+1];
	== {}
      p.[k];
    } end
  in FStar.Classical.forall_intro customlemma;
  eq_intro p' p;
  eq_elim p' p

let lemma_join_split #a [| ring a |] #n p1 p2 =
  let p = join_seq p1 p2 in
  let peven,podd = split_seq p in
  lemma_split_join p;
  assert(join_seq peven podd == p);
  eq_intro p1 peven;
  eq_elim p1 peven;
  eq_intro p2 podd;
  eq_elim p2 podd

#reset-options "--z3rlimit 1000 --max_fuel 2 --max_ifuel 2"

unfold
let recursive_split_customprop #a (#n:size_nat) (p:lseq a n) (i:size_nat{i>0}) (pow:size_nat{pow == pow2 i /\ n % pow == 0}) (p':lseq (lseq a (n/pow)) pow) (k:size_nat{k<n}) : GTot Type0 = ((k/pow < n/pow) /\ p'.[br i (k%pow)].[k/pow] == p.[k]) //l == (p'.[br i (k % pow)]) /\ l.[(k/pow)] == p.[k])

#reset-options "--z3rlimit 1000 --max_fuel 1 --max_ifuel 1"

let index_lemma #a (#n:size_nat) (pow:size_nat{pow > 0 /\ pow=2*(pow/2)}) (l1:lseq a (n/pow)) (l2:lseq a (n/pow)) (k:size_nat{k<n}) :
  Lemma (requires k/pow < n/pow /\ (k/2)/(pow/2) < n/pow /\ l1 == l2) (ensures l1.[k/pow] == l2.[(k/2)/(pow/2)]) =
    division_multiplication_lemma k 2 (pow/2)


#reset-options "--z3rlimit 2000 --max_fuel 1 --max_ifuel 1"

let recursive_lemma #a (#n:size_nat) (i:size_nat{i>1}) (pow:size_nat{pow == pow2 i /\ pow/2 == pow2 (i-1) /\ pow == 2*(pow/2) /\ n % pow == 0 /\ (n/2) % (pow/2) = 0 /\ (n/pow == (n/2)/(pow/2))}) (p:lseq a (n/2)) (p':lseq (lseq a (n/pow)) (pow/2)) (k:size_nat{k<n}) (l:lseq a (n/pow)) : Lemma (requires recursive_split_customprop p (i-1) (pow/2) p' (k/2) /\ p'.[br (i-1) ((k/2)%(pow/2))] == l /\ (k/pow == (k/2)/(pow/2))) (ensures l.[k/pow] == p.[k/2]) = index_lemma pow l (p'.[br (i-1) ((k/2)%(pow/2))]) k

#reset-options "--z3rlimit 1000 --max_fuel 2 --max_ifuel 2"

val recursive_split_seq2_lemma_base:
  #a:Type0
  -> #n:size_nat{n%2=0}
  -> p:lseq a n
  -> p':(lseq (lseq a (n/2)) 2)
  -> Lemma (ensures (let (p1,p2) = split_seq p in let p' = Seq.concat (Seq.create 1 p1) (Seq.create 1 p2) in forall (k:nat{k<n}). recursive_split_customprop p 1 2 p' k))

#reset-options "--z3rlimit 1000 --max_fuel 1 --max_ifuel 0"

let recursive_split_seq2_lemma_base #a #n p p' =
  let (p1,p2) = split_seq p in
  let p' = Seq.concat (Seq.create 1 p1) (Seq.create 1 p2) in
  Seq.Base.lemma_index_app1 (Seq.create 1 p1) (Seq.create 1 p2) 0;
  Seq.Base.lemma_index_app2 (Seq.create 1 p1) (Seq.create 1 p2) 1;
  assert(p'.[0] == Seq.index (Seq.create 1 p1) 0);
  assert(p'.[1] == Seq.index (Seq.create 1 p2) 0);
  assert(p'.[0] == p1);
  assert(p'.[1] == p2);
  let customlemma (k:nat{k<n}) : Lemma (recursive_split_customprop p 1 2 p' k) =
    lemma_div_exact n 2;
    euclidean_div_axiom k 2;
    if (n/2 <= k/2) then lemma_mult_le_left 2 (n/2) (k/2);
    br_lemma_zero 1;
    br_lemma_one 1;
    euclidean_division_definition k 2;
    if (k % 2 = 0) then
      (div_exact_r k 2;
      assert(p'.[0].[k/2] == p1.[k/2]); assert(p1.[k/2] == p.[k]))
    else
      (assert(k = 2*(k/2) + 1); assert(p'.[1].[k/2] == p2.[k/2]); assert(p2.[k/2] == p.[k]))
  in FStar.Classical.forall_intro customlemma


#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

val recursive_split_seq2_lemma_inductive_1:
  #a:Type0
  -> #n:size_nat
  -> i:size_nat{i>1}
  -> pow:size_nat {pow = pow2 i /\ pow/2 = pow2 (i-1) /\ pow = 2*(pow/2)}
  -> p1:lseq (lseq a (n/pow)) (pow/2)
  -> p2:lseq (lseq a (n/pow)) (pow/2)
  -> k:size_nat{k<n}
  -> Lemma (requires k % pow < pow2 (i-1) /\ (k % pow) % 2 = 0 /\ k/pow < n/pow /\ k/2 < n/2 /\ (n/2)/(pow/2) == n/pow) (ensures (let p':lseq (lseq a (n/pow)) pow = Seq.concat p1 p2 in p'.[br i (k % pow)] == p1.[br (i-1) ((k/2) % (pow/2))] ))

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"


let recursive_split_seq2_lemma_inductive_1 #a #n i pow p1 p2 k =
  let p' = Seq.concat p1 p2 in
  pow2_modulo_division_lemma_1 k 1 i;
  modulo_lemma (k % pow) (pow2 (i-1));
  br_lemma_rec (i-1) (k % pow);
  let m = br i (k % pow) in
  br_lemma_div (i-1) (k % pow);
  assert( m % pow2 (i-1) == br (i-1) ((k/2) % (pow/2)));
  pow2_lt_compat i (i-1);
  br_lemma_n2_2 (i-1) (k%pow);
  pow2_double_sum (i-1);
  assert(m < pow2 (i-1));
  modulo_lemma m (pow2 (i-1));
  Seq.Base.lemma_index_app1 p1 p2 m;
  assert (m == br (i-1) ((k/2) % (pow/2)));
  assert (p'.[br i (k%pow)] == p1.[br (i-1) ((k/2)%(pow/2))])

val recursive_split_seq2_lemma_inductive_2:
  #a:Type0
  -> #n:size_nat
  -> i:size_nat{i>1}
  -> pow:size_nat {pow = pow2 i /\ pow/2 = pow2 (i-1) /\ pow = 2*(pow/2)}
  -> p1:lseq (lseq a (n/pow)) (pow/2)
  -> p2:lseq (lseq a (n/pow)) (pow/2)
  -> k:size_nat{k<n}
  -> Lemma (requires k % pow < pow2 (i-1) /\ (k % pow) % 2 = 1 /\ k/pow < n/pow /\ (k/2)/(pow/2) < n/pow) (ensures (let p':lseq (lseq a (n/pow)) pow = Seq.concat p1 p2 in p'.[br i (k % pow)] == p2.[br (i-1) ((k/2) % (pow/2))] ))

let recursive_split_seq2_lemma_inductive_2 #a #n i pow p1 p2 k =
  let p' = Seq.concat p1 p2 in
  modulo_lemma (k % pow) (pow2 (i-1));
  pow2_modulo_division_lemma_1 k 1 i;
  br_lemma_rec (i-1) (k % pow);
  let m = br i (k % pow) in
  br_lemma_div (i-1) (k % pow);
  assert( m % pow2 (i-1) == br (i-1) ((k/2) % (pow/2)));
  pow2_lt_compat i (i-1);
  br_lemma_n2_2 (i-1) (k%pow - 1);
  assert(m >= pow2 (i-1) /\ m < pow2 i);
  pow2_double_sum (i-1);
  lemma_mod_sub m (pow/2) 1;
  modulo_lemma (m - (pow/2)) (pow/2);
  assert(m = pow2 (i-1) + br (i-1) ((k/2) % (pow/2)));
  Seq.Base.lemma_index_app2 p1 p2 m;
  assert (p'.[br i (k%pow)] == p2.[br (i-1) ((k/2)%(pow/2))])

val recursive_split_seq2_lemma_inductive_3:
  #a:Type0
  -> #n:size_nat
  -> i:size_nat{i>1}
  -> pow:size_nat {pow = pow2 i /\ pow/2 = pow2 (i-1) /\ pow = 2*(pow/2)}
  -> p1:lseq (lseq a (n/pow)) (pow/2)
  -> p2:lseq (lseq a (n/pow)) (pow/2)
  -> k:size_nat{k<n}
  -> Lemma (requires k % pow >= pow2 (i-1) /\ ((k-pow/2) % pow) % 2 = 0 /\ k/pow < n/pow /\ (k/2)/(pow/2) < n/pow) (ensures (let p':lseq (lseq a (n/pow)) pow = Seq.concat p1 p2 in p'.[br i (k % pow)] == p1.[br (i-1) ((k/2) % (pow/2))] ))

let recursive_split_seq2_lemma_inductive_3 #a #n i pow p1 p2 k =
  let p' = Seq.concat p1 p2 in
  lemma_mod_sub_distr_l k (pow/2) pow;
  modulo_lemma ((k % pow) - pow/2) pow;
  assert((k % pow - (pow/2)) == (k - pow/2) % pow);
  br_lemma_rec (i-1) (k % pow - pow/2);
  br_lemma_n2_1 (i-1) (k % pow - pow/2);
  assert(br i (k % pow) == 2 * br (i-1) ((k - pow/2) % pow) + 1);
  let m = br i (k % pow) in
  pow2_double_mult (i-2);
  assert(pow/2 = 2*pow2 (i-2));
  assert(((k-pow/2) % pow) /2 = (k % pow - 2*pow2 (i-2)) /2);
  lemma_div_plus (k % pow) (- pow2 (i-2)) 2;
  assert(((k-pow/2) % pow) /2 = (k % pow) /2  - pow2 (i-2));
  pow2_modulo_division_lemma_1 k 1 i;
  br_lemma_div (i-1) ((k - pow/2) % pow);
  assert( (m-1) % pow2 (i-1) == br (i-1) ((k/2)%(pow/2) - pow2 (i-2)));
  br_lemma_n2_1 (i-2) ((k/2)%(pow/2) - pow2 (i-2));
  assert ((m-1) % pow2 (i-1) == br (i-1) ((k/2)%(pow/2)) - 1);
  let m2 = br i ((k - pow/2) % pow) in
  assert (m2 % pow2 (i-1) == br (i-1) ((k/2)%(pow/2)) - 1);
  pow2_lt_compat i (i-1);
  br_lemma_n2_2 (i-1) ((k-pow/2)%pow);
  assert(m2 < pow2 (i-1));
  modulo_lemma m2 (pow/2);
  assert(m = br (i-1) ((k/2) % (pow/2)));
  Seq.Base.lemma_index_app1 p1 p2 m;
  assert (p'.[br i (k%pow)] == p1.[br (i-1) ((k/2)%(pow/2))])

val recursive_split_seq2_lemma_inductive_4:
  #a:Type0
  -> #n:size_nat
  -> i:size_nat{i>1}
  -> pow:size_nat {pow = pow2 i /\ pow/2 = pow2 (i-1) /\ pow = 2*(pow/2)}
  -> p1:lseq (lseq a (n/pow)) (pow/2)
  -> p2:lseq (lseq a (n/pow)) (pow/2)
  -> k:size_nat{k<n}
  -> Lemma (requires k % pow >= pow2 (i-1) /\ ((k-pow/2) % pow) % 2 = 1 /\ k/pow < n/pow /\ (k/2)/(pow/2) < n/pow) (ensures (let p':lseq (lseq a (n/pow)) pow = Seq.concat p1 p2 in p'.[br i (k % pow)] == p2.[br (i-1) ((k/2) % (pow/2))] ))

let recursive_split_seq2_lemma_inductive_4 #a #n i pow p1 p2 k =
  let p' = Seq.concat p1 p2 in
  lemma_mod_sub_distr_l k (pow/2) pow;
  modulo_lemma ((k % pow) - pow/2) pow;
  assert((k % pow - (pow/2)) == (k - pow/2) % pow);
  br_lemma_rec (i-1) (k % pow - pow/2);
  br_lemma_n2_1 (i-1) (k % pow - pow/2);
  assert(br i (k % pow) == 2 * br (i-1) ((k - pow/2) % pow) + 1);
  let m = br i (k % pow) in
  pow2_double_mult (i-2);
  assert(pow/2 = 2*pow2 (i-2));
  assert(((k-pow/2) % pow) /2 = (k % pow - 2*pow2 (i-2)) /2);
  lemma_div_plus (k % pow) (- pow2 (i-2)) 2;
  assert(((k-pow/2) % pow) /2 = (k % pow) /2  - pow2 (i-2));
  pow2_modulo_division_lemma_1 k 1 i;
  br_lemma_div (i-1) ((k - pow/2) % pow);
  assert( (m-1) % pow2 (i-1) == br (i-1) ((k/2)%(pow/2) - pow2 (i-2)));
  br_lemma_n2_1 (i-2) ((k/2)%(pow/2) - pow2 (i-2));
  assert ((m-1) % pow2 (i-1) == br (i-1) ((k/2)%(pow/2)) - 1);
  let m2 = br i ((k - pow/2) % pow) in
  assert (m2 % pow2 (i-1) == br (i-1) ((k/2)%(pow/2)) - 1);
  pow2_lt_compat i (i-1);
  br_lemma_n2_2 (i-1) ((k-pow/2)%pow - 1);
  assert(m2 >= pow2 (i-1) /\ m2 < pow2 i);
  pow2_double_sum (i-1);
  lemma_mod_sub m2 (pow/2) 1;
  modulo_lemma (m2 - (pow/2)) (pow/2);
  assert(m = pow2 (i-1) + br (i-1) ((k/2) % (pow/2)));
  Seq.Base.lemma_index_app2 p1 p2 m;
  assert (p'.[br i (k%pow)] == p2.[br (i-1) ((k/2)%(pow/2))])

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

let lemma_preconditions (n:size_nat) (i:size_nat{i>1}) (pow:size_nat{pow = pow2 i /\ pow/2 == pow2 (i-1) /\ pow = 2 * (pow/2) /\ n % pow == 0 }) (k:size_nat{k<n}) : Lemma (k/pow < n/pow /\ (k/2)/(pow/2) < n/pow /\ k % 2 = (k % pow) % 2 /\ k %2 = ((k - pow/2) % pow) % 2 /\ k = 2*(k/2)+(k%2) /\ n % pow == 0 /\ (n/2) % (pow/2) = 0 /\ (n/pow == (n/2)/(pow/2))) =
  lemma_div_exact n pow;
  euclidean_div_axiom k pow;
  if (n/pow <= k/pow) then lemma_mult_le_left pow (n/pow) (k/pow);
  assert(k/pow < n/pow);
  division_multiplication_lemma k 2 (pow/2);
  division_multiplication_lemma n 2 (pow/2);
  pow2_modulo_modulo_lemma_1 k 1 i;
  pow2_modulo_division_lemma_1 n 1 i;
  assert(((k % pow) %2) == k % 2);
  lemma_mod_sub_distr k (pow/2) 2;
  pow2_double_mult (i-2);
  assert((pow/2) % 2 == 0);
  modulo_modulo_lemma (k-pow/2) 2 (pow/2);
  assert((((k - pow/2) % pow) %2) == k % 2);
  euclidean_division_definition k 2


val recursive_split_seq2_lemma_inductive:
  #a:Type0
  -> #n:size_nat
  -> p:lseq a n
  -> p1:lseq a (n/2)
  -> p2:lseq a (n/2)
  -> i:size_nat{i>1}
  -> pow:size_nat {pow = pow2 i /\ pow/2 = pow2 (i-1) /\ pow = 2*(pow/2)}
  -> p':lseq (lseq a (n/pow)) pow
  -> p1':lseq (lseq a (n/pow)) (pow/2)
  -> p2':lseq (lseq a (n/pow)) (pow/2)
  -> k:size_nat{k<n}
  -> Lemma (requires n % 2 = 0 /\ n % pow == 0 /\ (n/2) % (pow/2) == 0 /\ (p1,p2) == split_seq p /\ recursive_split_customprop p1 (i-1) (pow/2) p1' (k/2) /\ recursive_split_customprop p2 (i-1) (pow/2) p2' (k/2) /\ (p1,p2) == split_seq p /\ p' == Seq.concat p1' p2') (ensures recursive_split_customprop p i pow p' k)

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1"

let recursive_split_seq2_lemma_inductive #a #n p p1 p2 i pow p' p1' p2' k =
  lemma_preconditions n i pow k;
  let l:lseq a (n/pow) = p'.[br i (k%pow)] in
  if (k % pow < pow/2) then
    if (k % 2 = 0) then
      (assert((k % pow) % 2 == 0); recursive_split_seq2_lemma_inductive_1 i pow p1' p2' k; admit(); recursive_lemma i pow p1 p1' k l; admit(); assert(l.[k/pow] == p.[k]))
    else
      (assert((k % pow) % 2 == 1); recursive_split_seq2_lemma_inductive_2 i pow p1' p2' k; recursive_lemma i pow p2 p2' k l; admit())
  else
    if (k % 2 = 0) then
      (assert(((k - pow/2) %pow) % 2 = 0); recursive_split_seq2_lemma_inductive_3 i pow p1' p2' k; admit(); recursive_lemma i pow p1 p1' k l; admit(); assert(k % 2 = 0); admit(); assert(l.[k/pow] == p.[k]))
    else
      (assert(((k - pow/2) %pow) % 2 = 1); recursive_split_seq2_lemma_inductive_4 i pow p1' p2' k; admit(); recursive_lemma i pow p2 p2' k l)

val recursive_split_seq2:
   #a:Type0
   -> #n:size_nat
   -> p:lseq a n
   -> i:size_nat{i>0}
   -> pow:size_nat{pow = pow2 i}
   -> Ghost (lseq (lseq a (n/pow)) pow) (requires n % pow == 0) (ensures fun p' -> forall (k:nat{k<n}). recursive_split_customprop p i pow p' k p'.[br i (k%pow)]) (decreases i)

let rec recursive_split_seq2 #a #n p i pow =
  pow2_modulo_modulo_lemma_1 n 1 i;
  assert(pow2 1 = 2);
  let customlemma0 (k:nat{k<n}) : Lemma (k/pow < n/pow) =
    lemma_div_exact n pow;
    euclidean_div_axiom k pow;
    if (n/pow <= k/pow) then lemma_mult_le_left pow (n/pow) (k/pow)
  in FStar.Classical.forall_intro #(k:nat{k<n}) #(fun k -> k/pow < n/pow) customlemma0;
  let (p1,p2) = split_seq p in
  if (i=1) then
     let p':lseq (lseq a (n/2)) 2 = Seq.concat (Seq.create 1 p1) (Seq.create 1 p2) in
     recursive_split_seq2_lemma_base p p';
     p'
  else
    begin
      pow2_minus i 1;
      pow2_modulo_division_lemma_1 n 1 i;
      assert(pow2 1 == 2);
      pow2_double_mult (i-1);
      division_multiplication_lemma n 2 (pow2 (i-1));
      assert(n/2 % (pow/2) = 0);
      pow2_lt_compat i 1;
      pow2_le_compat (i-1) 1;
      div_exact_r n 2;
      assert(i-1>0 /\ i-1 <= max_size_t);
      assert(pow = 2*(pow/2) /\ (n/2)/(pow2 (i-1)) == n / pow);
      pow2_lt_compat i (i-1);
      division_multiplication_lemma n 2 (pow/2);
      let p1':lseq (lseq a (n/pow)) (pow/2) = recursive_split_seq2 p1 (i-1) (pow/2) in
      let p2':lseq (lseq a (n/pow)) (pow/2) = recursive_split_seq2 p2 (i-1) (pow/2) in
      let p':lseq (lseq a (n/pow)) pow = Seq.concat p1' p2' in
      let customlemma0 (k:nat{k<n}) : Lemma (k/pow < n/pow) =
        lemma_div_exact n pow;
        euclidean_div_axiom k pow;
        if (n/pow <= k/pow) then lemma_mult_le_left pow (n/pow) (k/pow)
        in FStar.Classical.forall_intro #(k:nat{k<n}) #(fun k -> k/pow < n/pow) customlemma0;
        admit();
      let customlemma (k:nat{k<n}) : Lemma (recursive_split_customprop p i pow p' k) =
        customlemma0 k;
        pow2_modulo_division_lemma_1 k 1 i;
        assert(k/pow == (k/2)/(pow/2));
        assert((k/2)/(pow/2) < (n/pow));
        if (k % pow < pow2 (i-1)) then
          if ((k % pow) % 2 = 0) then
            begin admit();
              recursive_split_seq2_lemma_inductive_1 i pow p1' p2' k;
            admit()
          end
          else admit()
        else admit()
      in FStar.Classical.forall_intro customlemma; p'
    end

let rec sum_n_spec #a [|monoid a|] #n (l:lseq a n) =
  if n=0 then id
  else let s = sum_n_spec (sub l 1 (n-1)) in
  op #a l.[0] s

inline_for_extraction
val simpl_seq_sub_sub_lemma:
  #a:Type
  -> #len:size_nat
  -> l:lseq a len
  -> start1:size_nat
  -> n1:size_nat{start1+n1<=len}
  -> start2:size_nat
  -> n2:size_nat{start2+n2<=n1}
  -> Lemma(sub (sub l start1 n1) start2 n2 == sub l (start1+start2) n2)

let simpl_seq_sub_sub_lemma #a #len l start1 n1 start2 n2 =
  let s = sub (sub l start1 n1) start2 n2 in
  assert ((forall (k:nat{k<n2}). index s k == index (sub l start1 n1) (k+start2)));
  assert ((forall (k:nat{k<n2}). index s k == index l (start1+start2+k)));
  eq_intro s (sub l (start1+start2) n2);
  eq_elim s (sub l (start1+start2) n2)

#push-options "--max_fuel 2"
val sum_n_spec_simple_lemma1:
  #a:Type0
  -> #[FStar.Tactics.Typeclasses.tcresolve ()] r:monoid a
  -> #n:size_nat{n>=1}
  -> l:lseq a n
  -> Lemma (ensures sum_n_spec l == op l.[0] (sum_n_spec (sub l 1 (n-1))))
	  (decreases n)

let sum_n_spec_simple_lemma1 #a [|monoid a|] #n l = ()

val sum_n_spec_simple_lemma2:
  #a:Type0
  -> #[FStar.Tactics.Typeclasses.tcresolve ()] r:monoid a
  -> #n:size_nat{n>=1}
  -> l:lseq a n
  -> Lemma (ensures sum_n_spec l == op (sum_n_spec (sub l 0 (n-1))) (l.[n-1]))
	  (decreases n)

let rec sum_n_spec_simple_lemma2 #a [|monoid a|] #n l =
  if n = 1 then (lemma_id1 #a l.[0]; lemma_id2 #a l.[0])
  else begin
    sum_n_spec_simple_lemma1 l;
    sum_n_spec_simple_lemma2 (sub l 1 (n-1));
    simpl_seq_sub_sub_lemma l 1 (n-1) 0 (n-2);
    lemma_assoc l.[0] (sum_n_spec (sub l 1 (n-2))) l.[n-1];
    simpl_seq_sub_sub_lemma l 0 (n-1) 1 (n-2);
    sum_n_spec_simple_lemma1 (sub l 0 (n-1))
    end

let rec sum_n_inner #a [|monoid a|] #n acc (l:lseq a n) =
  if n=0 then acc
  else sum_n_inner (op #a acc l.[0]) (sub l 1 (n-1))

let rec sum_n_inner_lemma #a [|monoid a|] #n acc (l:lseq a n) (i:nat{i<=n}) : Lemma (requires acc == sum_n_spec (sub l 0 i)) (ensures sum_n_inner acc (sub l i (n-i)) == sum_n_spec l) (decreases (n-i)) =
  if (i=n) then (assert(sum_n_inner acc (sub l n 0) == acc); eq_intro (sub l 0 n) l)
  else begin
    assert (op #a acc (sub l i (n-i)).[0] == op #a acc l.[i]);
    sum_n_spec_simple_lemma2 (sub l 0 (i+1));
    simpl_seq_sub_sub_lemma l 0 (i+1) 0 i;
    assert(op #a acc (sub l i (n-i)).[0] == sum_n_spec (sub l 0 (i+1)));
    simpl_seq_sub_sub_lemma l i (n-i) 1 (n-i-1);
    sum_n_inner_lemma (op #a acc (sub l i (n-i)).[0]) l (i+1)
    end

let rec sum_n #a [|monoid a|] #n l =
  sum_n_inner id l

let sum_n_lemma #a [|monoid a|] #n (l:lseq a n) : Lemma (sum_n l == sum_n_spec l) =
  sum_n_inner_lemma id l 0; eq_intro (sub l 0 n) l
//  if n=0 then id
//  else
//  let s=sum_n (sub l 1 (n-1)) in
//  op #a l.[0] s

let sum_n_zero_elements_is_id #a [|monoid a|] p = assert_norm(sum_n p == id)

#reset-options "--z3rlimit 200 --max_fuel 2 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

let rec sum_n_simple_lemma2 #a [|monoid a|] #n l =
  sum_n_lemma (sub l 0 (n-1));
  sum_n_inner_lemma (sum_n (sub l 0 (n-1))) l (n-1);
  sum_n_lemma l

let rec sum_n_simple_lemma1 #a [|monoid a|] #n l =
  if n=1 then (lemma_id1 #a l.[0]; lemma_id2 #a l.[0])
  else begin
    sum_n_simple_lemma2 l;
    sum_n_simple_lemma1 (sub l 0 (n-1));
    simpl_seq_sub_sub_lemma l 0 (n-1) 1 (n-2);
    lemma_assoc l.[0] (sum_n (sub l 1 (n-2))) l.[n-1];
    simpl_seq_sub_sub_lemma l 1 (n-1) 0 (n-2);
    sum_n_simple_lemma2 (sub l 1 (n-1))
    end

let rec sum_n_split_lemma #a [| ring a |] #n l leven lodd =
  let m = (add_ag #a).g.m in
  if (n = 0) then (sum_n_zero_elements_is_id l; sum_n_zero_elements_is_id leven; sum_n_zero_elements_is_id lodd; lemma_zero1 #a zero) else begin
    sum_n_simple_lemma2 l;
    sum_n_simple_lemma2 (Seq.sub l 0 (n-1));
    Seq.eq_intro (Seq.sub (Seq.sub l 0 (n-1)) 0 (n-2)) (Seq.sub l 0 (n-2));
    let (l1,l2) = split_seq (Seq.sub l 0 (n-2)) in
    sum_n_split_lemma (Seq.sub l 0 (n-2)) l1 l2;
    eq_intro l1 (Seq.sub leven 0 (n/2 - 1));
    eq_intro l2 (Seq.sub lodd 0 (n/2 - 1));
    lemma_plus_assoc (sum_n l1) (sum_n l2) l.[n-2];
    lemma_plus_swap (sum_n l2) l.[n-2];
    lemma_plus_assoc (sum_n l1) l.[n-2] (sum_n l2);
    sum_n_simple_lemma2 leven;
    lemma_plus_assoc (sum_n leven) (sum_n l2) l.[n-1];
    sum_n_simple_lemma2 lodd
    end

val map_sub_commutativity_lemma:
  #a:Type0
  -> #b:Type0
  -> #n:size_nat
  -> l:lseq a n
  -> f:(a -> b)
  -> i:size_nat
  -> len:size_nat{i+len<=n}
  -> Lemma (ensures sub (Seq.map f l) i len == Seq.map f (sub l i len))

#reset-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

let rec map_sub_commutativity_lemma #a #b #n l f i len =
  assert(forall (k:nat{k<len}). (sub (Seq.map f l) i len).[k] == (Seq.map f l).[i+k]);
  assert(forall (k:nat{k<len}). (sub (Seq.map f l) i len).[k] == f l.[i+k]);
  assert(forall (k:nat{k<len}). (sub (Seq.map f l) i len).[k] == f (sub l i len).[k]);
  assert(forall (k:nat{k<len}). f (sub l i len).[k] == (Seq.map f (sub l i len)).[k]);
  eq_intro (sub (Seq.map f l) i len) (Seq.map f (sub l i len));
  eq_elim (sub (Seq.map f l) i len) (Seq.map f (sub l i len))

#reset-options "--z3rlimit 200 --max_fuel 2 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

let rec sum_n_mul_distrib_l_lemma #a [|ring a|] #n l k =
  let m = (add_ag #a).g.m in
  if n=0 then lemma_zero_absorb2 k
  else begin
    sum_n_simple_lemma1 l;
    assert(mul k (sum_n l) == mul k (plus l.[0] (sum_n (sub l 1 (n-1)))));
    lemma_distr_left k l.[0] (sum_n (sub l 1 (n-1)));
    assert(mul k (sum_n l) == plus (mul k l.[0]) (mul k (sum_n (sub l 1 (n-1)))));
    sum_n_mul_distrib_l_lemma (sub l 1 (n-1)) k;
    assert((Seq.map (fun x -> mul k x) l).[0] == mul k l.[0]);
    assert (mul k (sum_n l) == plus (Seq.map (fun x -> mul k x) l).[0] (sum_n (Seq.map (fun x -> mul k x) (sub l 1 (n-1)))));
    map_sub_commutativity_lemma l (fun x -> mul k x) 1 (n-1);
    assert (mul k (sum_n l) == plus (Seq.map (fun x -> mul k x) l).[0] (sum_n (sub (Seq.map (fun x -> mul k x) l) 1 (n-1))));
    sum_n_simple_lemma1 (Seq.map (fun x -> mul k x) l)
  end



let rec sum_n_mul_distrib_r_lemma #a [|ring a|] #n l k =
  let m = (add_ag #a).g.m in
  if n=0 then lemma_zero_absorb1 k
  else begin
    sum_n_simple_lemma1 l;
    assert(mul (sum_n l) k == mul (plus l.[0] (sum_n (sub l 1 (n-1)))) k);
    lemma_distr_right k l.[0] (sum_n (sub l 1 (n-1)));
    assert(mul (sum_n l) k == plus (mul l.[0] k) (mul (sum_n (sub l 1 (n-1))) k));
    sum_n_mul_distrib_r_lemma (sub l 1 (n-1)) k;
    assert((Seq.map (fun x -> mul x k) l).[0] == mul l.[0] k);
    assert (mul (sum_n l) k == plus (Seq.map (fun x -> mul x k) l).[0] (sum_n (Seq.map (fun x -> mul x k) (sub l 1 (n-1)))));
    map_sub_commutativity_lemma l (fun x -> mul x k) 1 (n-1);
    assert (mul (sum_n l) k == plus (Seq.map (fun x -> mul x k) l).[0] (sum_n (sub (Seq.map (fun x -> mul x k) l) 1 (n-1))));
    sum_n_simple_lemma1 (Seq.map (fun x -> mul x k) l)
  end

#reset-options "--z3rlimit 200 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

let rec sum_n_all_id #a [|monoid a|] #n l =
  if n = 0 then ()
  else(
    sum_n_simple_lemma1 l;
    assert(sum_n #a l == op l.[0] (sum_n (sub l 1 (n-1))));
    sum_n_all_id (Lib.Sequence.sub l 1 (n-1));
    assert(sum_n l == op #a l.[0] id);
    lemma_id2 #a l.[0])


let rec sum_n_one_non_id_coeff #a [|monoid a|] #n k l =
  if k = 0 then begin
    sum_n_all_id (sub l 1 (n-1));
    sum_n_simple_lemma1 l;
    assert (sum_n l == op l.[0] (sum_n (sub l 1 (n-1))));
    lemma_id2 #a l.[0]
    end
  else begin
    sum_n_simple_lemma1 l;
    assert(sum_n l == op l.[0] (sum_n (sub l 1 (n-1))));
    assert(l.[0] == id #a);
    sum_n_one_non_id_coeff (k-1) (sub l 1 (n-1));
    assert(sum_n (sub l 1 (n-1)) == l.[k]);
    assert(sum_n l == op #a id l.[k]);
    lemma_id1 #a l.[k]
  end


let rec sum_n_all_c_is_repeat_c_n #a [|monoid a|] #n c l =
  if n = 0 then ()
  else begin
    sum_n_simple_lemma1 l;
    assert(sum_n l == op l.[0] (sum_n (sub l 1 (n-1))));
    sum_n_all_c_is_repeat_c_n c (sub l 1 (n-1));
    assert(sum_n l == op c (repeat_op c (n-1)));
    lemma_repeat_op_succ1 c (n-1)
  end



#reset-options "--z3rlimit 200 --max_fuel 2 --max_ifuel 2 --using_facts_from '* -FStar.Seq'"

(**fubini lemma *)
(*
val modular_fubini_lemma_:
  #n1:size_nat
  -> #n2:size_nat
  -> #q:nat{q>0}
  -> l1: set n1 q
  -> l2: set n2 q
  -> Lemma (ensures modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> x *% y) l2)) l1) = modular_sum_n (Seq.map (fun y -> modular_sum_n (Seq.map (fun x -> x *% y) l1)) l2))

let modular_fubini_lemma_ #n1 #n2 #q l1 l2 =
  let s1 = Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> x *% y) l2)) l1 in
  assert(forall (k:nat{k<n1}). s1.[k] = modular_sum_n (Seq.map (fun y -> l1.[k] *% y) l2));
  let customprop1 (k:nat{k<n1}) : GTot Type0 =
    l1.[k] *% modular_sum_n l2 = modular_sum_n (Seq.map (fun y -> l1.[k]*%y) l2)
  in
  let g1 (k:nat{k<n1}) : Lemma (customprop1 k) =
    modular_sum_n_mult_distrib_l_lemma l2 l1.[k]
  in
  FStar.Classical.forall_intro g1;
  assert(forall (k:nat{k<n1}). s1.[k] = l1.[k] *% modular_sum_n l2);
  eq_intro s1 (Seq.map (fun x -> x *% (modular_sum_n l2)) l1);
  eq_elim s1 (Seq.map (fun x -> x *% (modular_sum_n l2)) l1);
  modular_sum_n_mult_distrib_r_lemma l1 (modular_sum_n l2);
  assert (modular_sum_n s1 = modular_sum_n l1 *% (modular_sum_n l2));

  let s2 = Seq.map (fun y -> modular_sum_n (Seq.map (fun x -> x *% y) l1)) l2 in
  let customprop2 (k:nat{k<n2}) : GTot Type0 =
    (modular_sum_n l1) *% l2.[k] = modular_sum_n (Seq.map (fun x -> x *% l2.[k]) l1)
  in
  let g2 (k:nat{k<n2}) : Lemma (customprop2 k) =
    modular_sum_n_mult_distrib_r_lemma l1 l2.[k]
  in
  FStar.Classical.forall_intro g2;
  eq_intro s2 (Seq.map (fun y -> (modular_sum_n l1) *% y) l2);
  eq_elim s2 (Seq.map (fun y -> (modular_sum_n l1) *% y) l2);
  modular_sum_n_mult_distrib_l_lemma l2 (modular_sum_n l1);
  assert (modular_sum_n s2 = modular_sum_n l1 *% (modular_sum_n l2))

*)
#reset-options "--z3rlimit 200 --max_fuel 2 --max_ifuel 2 --using_facts_from '* -FStar.Seq'"

val dummy_sum_n_fubini_sublemma:
  #a:Type0
  -> #b:Type0
  -> #n:size_nat{n>0}
  -> g:(a -> b)
  -> l:lseq a n
  -> Lemma((Seq.map g l).[0] == g l.[0])

let dummy_sum_n_fubini_sublemma #n #q1 #q2 g l =
  ()


val sum_n_fubini_sublemma:
  #a:Type0
  -> #b:Type0
  -> #c:Type0
  -> #[tcresolve ()] mc: commutative_monoid c
  -> #n1:size_nat
  -> #n2:size_nat{n2>0}
  -> f: (a -> b -> c)
  -> l1: lseq a n1
  -> l2: lseq b n2
  -> Lemma(ensures (let m = (bm #c) in sum_n (Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) l2)) l1) == op (sum_n (Seq.map (fun x -> f x l2.[0]) l1)) (sum_n (Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) l1)))) (decreases n1)

let rec sum_n_fubini_sublemma #a #b #c [|commutative_monoid c|] #n1 #n2 f l1 l2 (*:
Lemma(ensures modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) l2)) l1) = modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) l1) +% modular_sum_n (Seq.map (fun x -> f x l2.[0]) l1)) (decreases n1)
by (tadmit ())*)
=
  let m = bm #c in
  let s = sum_n (Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) l2)) l1) in
  if n1 = 0 then lemma_id1 #c id
  else begin
    sum_n_simple_lemma1 (Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) l2)) l1);
    assert(s == op (Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) l2)) l1).[0] (sum_n (sub (Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) l2)) l1) 1 (n1-1))));
    dummy_sum_n_fubini_sublemma (fun x -> sum_n (Seq.map (fun y -> f x y) l2)) l1;
    map_sub_commutativity_lemma l1 (fun x -> sum_n (Seq.map (fun y -> f x y) l2)) 1 (n1-1);
    sum_n_fubini_sublemma f (sub l1 1 (n1-1)) l2;
    assert(s == op (sum_n (Seq.map (fun y -> f l1.[0] y) l2)) (op (sum_n (Seq.map (fun x -> f x l2.[0]) (sub l1 1 (n1-1)))) (sum_n (Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) (sub l1 1 (n1-1))))));
    lemma_assoc (sum_n (Seq.map (fun y -> f l1.[0] y) l2)) (sum_n (Seq.map (fun x -> f x l2.[0]) (sub l1 1 (n1-1)))) (sum_n (Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) (sub l1 1 (n1-1))));
    sum_n_simple_lemma1 (Seq.map (fun y -> f l1.[0] y) l2);
    dummy_sum_n_fubini_sublemma (fun y -> f l1.[0] y) l2;
    map_sub_commutativity_lemma l2 (fun y -> f l1.[0] y) 1 (n2-1);
    lemma_assoc (f l1.[0] l2.[0]) (sum_n (Seq.map (fun y -> f l1.[0] y) (sub l2 1 (n2-1)))) (sum_n (Seq.map (fun x -> f x l2.[0]) (sub l1 1 (n1-1))));
    lemma_swap_m (sum_n (Seq.map (fun y -> f l1.[0] y) (sub l2 1 (n2-1)))) (sum_n (Seq.map (fun x -> f x l2.[0]) (sub l1 1 (n1-1))));
    lemma_assoc (f l1.[0] l2.[0]) (sum_n (Seq.map (fun x -> f x l2.[0]) (sub l1 1 (n1-1)))) (sum_n (Seq.map (fun y -> f l1.[0] y) (sub l2 1 (n2-1))));
    dummy_sum_n_fubini_sublemma (fun x -> f x l2.[0]) l1;
    map_sub_commutativity_lemma l1 (fun x -> f x l2.[0]) 1 (n1-1);
    sum_n_simple_lemma1 (Seq.map (fun x -> f x l2.[0]) l1);
    assert(s == op (op (sum_n (Seq.map (fun x -> f x l2.[0]) l1)) (sum_n (Seq.map (fun y -> f l1.[0] y) (sub l2 1 (n2-1))))) (sum_n (Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) (sub l1 1 (n1-1)))));
    lemma_assoc (sum_n (Seq.map (fun x -> f x l2.[0]) l1)) (sum_n (Seq.map (fun y -> f l1.[0] y) (sub l2 1 (n2-1)))) (sum_n (Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) (sub l1 1 (n1-1))));
    dummy_sum_n_fubini_sublemma (fun x -> sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) l1;
    map_sub_commutativity_lemma l1 (fun x -> sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) 1 (n1-1);
    sum_n_simple_lemma1 (Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) l1)
    end

#reset-options "--z3rlimit 300 --max_fuel 2 --max_ifuel 2 --print_implicits"

let rec sum_n_fubini #a #b #c [|commutative_monoid c|] #n1 #n2 f l1 l2 =
 let m = bm #c in
 let s1 = Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) l2)) l1 in
 let s2 = Seq.map (fun y -> sum_n (Seq.map (fun x -> f x y) l1)) l2 in
  if n2 = 0 then begin
    assert (forall (k:nat{k<n1}). s1.[k] == sum_n (Seq.map (fun y -> f l1.[k] y) l2));
    assert (forall (k:nat{k<n1}). length (Seq.map (fun y -> f l1.[k] y) l2) = 0);
    assert (forall (k:nat{k<n1}). s1.[k] == id #c);
    sum_n_all_id s1;
    assert (sum_n s2 == id)
    end
  else begin
  sum_n_fubini_sublemma f l1 l2;
  assert(sum_n s1 == op (sum_n (Seq.map (fun x -> f x l2.[0]) l1)) (sum_n (Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) l1)));
  sum_n_fubini f l1 (sub l2 1 (n2-1));// (Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) l1) (Seq.map (fun y -> sum_n (Seq.map (fun x -> f x y) l1)) (sub l2 1 (n2-1)));
  assert(sum_n s1 == op ((fun y -> sum_n (Seq.map (fun x -> f x y) l1)) l2.[0]) (sum_n (Seq.map (fun y -> sum_n (Seq.map (fun x -> f x y) l1)) (sub l2 1 (n2-1)))));
  map_sub_commutativity_lemma l2 (fun y -> sum_n (Seq.map (fun x -> f x y) l1)) 1 (n2-1);
  dummy_sum_n_fubini_sublemma (fun y -> sum_n (Seq.map (fun x -> f x y) l1)) l2;
  assert(sum_n s1 == op ((Seq.map (fun y -> sum_n (Seq.map (fun x -> f x y) l1)) l2).[0]) (sum_n (sub (Seq.map (fun y -> sum_n (Seq.map (fun x -> f x y) l1)) l2) 1 (n2-1))));
  sum_n_simple_lemma1 (Seq.map (fun y -> sum_n (Seq.map (fun x -> f x y) l1)) l2)
  end

val sum_n_fubini_sublemma_ring:
  #a:Type0
  -> #b:Type0
  -> #c:Type0
  -> #[tcresolve ()] r: ring c
  -> #n1:size_nat
  -> #n2:size_nat{n2>0}
  -> f: (a -> b -> c)
  -> l1: lseq a n1
  -> l2: lseq b n2
  -> Lemma(ensures (let m = (add_ag #c).g.m in sum_n (Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) l2)) l1) == op (sum_n (Seq.map (fun x -> f x l2.[0]) l1)) (sum_n (Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) l1)))) (decreases n1)

let rec sum_n_fubini_sublemma_ring #a #b #c [|ring c|] #n1 #n2 f l1 l2 (*:
Lemma(ensures modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) l2)) l1) = modular_sum_n (Seq.map (fun x -> modular_sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) l1) +% modular_sum_n (Seq.map (fun x -> f x l2.[0]) l1)) (decreases n1)
by (tadmit ())*)
=
  let m = (add_ag #c).g.m in
  let s = sum_n (Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) l2)) l1) in
  if n1 = 0 then lemma_id1 #c id
  else begin
    sum_n_simple_lemma1 (Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) l2)) l1);
    assert(s == op (Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) l2)) l1).[0] (sum_n (sub (Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) l2)) l1) 1 (n1-1))));
    dummy_sum_n_fubini_sublemma (fun x -> sum_n (Seq.map (fun y -> f x y) l2)) l1;
    map_sub_commutativity_lemma l1 (fun x -> sum_n (Seq.map (fun y -> f x y) l2)) 1 (n1-1);
    sum_n_fubini_sublemma_ring f (sub l1 1 (n1-1)) l2;
    assert(s == op (sum_n (Seq.map (fun y -> f l1.[0] y) l2)) (op (sum_n (Seq.map (fun x -> f x l2.[0]) (sub l1 1 (n1-1)))) (sum_n (Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) (sub l1 1 (n1-1))))));
    lemma_assoc (sum_n (Seq.map (fun y -> f l1.[0] y) l2)) (sum_n (Seq.map (fun x -> f x l2.[0]) (sub l1 1 (n1-1)))) (sum_n (Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) (sub l1 1 (n1-1))));
    sum_n_simple_lemma1 (Seq.map (fun y -> f l1.[0] y) l2);
    dummy_sum_n_fubini_sublemma (fun y -> f l1.[0] y) l2;
    map_sub_commutativity_lemma l2 (fun y -> f l1.[0] y) 1 (n2-1);
    lemma_assoc (f l1.[0] l2.[0]) (sum_n (Seq.map (fun y -> f l1.[0] y) (sub l2 1 (n2-1)))) (sum_n (Seq.map (fun x -> f x l2.[0]) (sub l1 1 (n1-1))));
    lemma_plus_swap (sum_n (Seq.map (fun y -> f l1.[0] y) (sub l2 1 (n2-1)))) (sum_n (Seq.map (fun x -> f x l2.[0]) (sub l1 1 (n1-1))));
    lemma_assoc (f l1.[0] l2.[0]) (sum_n (Seq.map (fun x -> f x l2.[0]) (sub l1 1 (n1-1)))) (sum_n (Seq.map (fun y -> f l1.[0] y) (sub l2 1 (n2-1))));
    dummy_sum_n_fubini_sublemma (fun x -> f x l2.[0]) l1;
    map_sub_commutativity_lemma l1 (fun x -> f x l2.[0]) 1 (n1-1);
    sum_n_simple_lemma1 (Seq.map (fun x -> f x l2.[0]) l1);
    assert(s == op (op (sum_n (Seq.map (fun x -> f x l2.[0]) l1)) (sum_n (Seq.map (fun y -> f l1.[0] y) (sub l2 1 (n2-1))))) (sum_n (Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) (sub l1 1 (n1-1)))));
    lemma_assoc (sum_n (Seq.map (fun x -> f x l2.[0]) l1)) (sum_n (Seq.map (fun y -> f l1.[0] y) (sub l2 1 (n2-1)))) (sum_n (Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) (sub l1 1 (n1-1))));
    dummy_sum_n_fubini_sublemma (fun x -> sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) l1;
    map_sub_commutativity_lemma l1 (fun x -> sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) 1 (n1-1);
    sum_n_simple_lemma1 (Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) l1)
    end

let rec sum_n_fubini_ring #a #b #c [|ring c|] #n1 #n2 f l1 l2 =
 let m = (add_ag #c).g.m in
 let s1 = Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) l2)) l1 in
 let s2 = Seq.map (fun y -> sum_n (Seq.map (fun x -> f x y) l1)) l2 in
  if n2 = 0 then begin
    assert (forall (k:nat{k<n1}). s1.[k] == sum_n (Seq.map (fun y -> f l1.[k] y) l2));
    assert (forall (k:nat{k<n1}). length (Seq.map (fun y -> f l1.[k] y) l2) = 0);
    assert (forall (k:nat{k<n1}). s1.[k] == id #c);
    sum_n_all_id s1;
    assert (sum_n s2 == id)
    end
  else begin
  sum_n_fubini_sublemma_ring f l1 l2;
  assert(sum_n s1 == op (sum_n (Seq.map (fun x -> f x l2.[0]) l1)) (sum_n (Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) l1)));
  sum_n_fubini_ring f l1 (sub l2 1 (n2-1));// (Seq.map (fun x -> sum_n (Seq.map (fun y -> f x y) (sub l2 1 (n2-1)))) l1) (Seq.map (fun y -> sum_n (Seq.map (fun x -> f x y) l1)) (sub l2 1 (n2-1)));
  assert(sum_n s1 == op ((fun y -> sum_n (Seq.map (fun x -> f x y) l1)) l2.[0]) (sum_n (Seq.map (fun y -> sum_n (Seq.map (fun x -> f x y) l1)) (sub l2 1 (n2-1)))));
  map_sub_commutativity_lemma l2 (fun y -> sum_n (Seq.map (fun x -> f x y) l1)) 1 (n2-1);
  dummy_sum_n_fubini_sublemma (fun y -> sum_n (Seq.map (fun x -> f x y) l1)) l2;
  assert(sum_n s1 == op ((Seq.map (fun y -> sum_n (Seq.map (fun x -> f x y) l1)) l2).[0]) (sum_n (sub (Seq.map (fun y -> sum_n (Seq.map (fun x -> f x y) l1)) l2) 1 (n2-1))));
  sum_n_simple_lemma1 (Seq.map (fun y -> sum_n (Seq.map (fun x -> f x y) l1)) l2)
  end
