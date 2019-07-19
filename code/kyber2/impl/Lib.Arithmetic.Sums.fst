module Lib.Arithmetic.Sums

open FStar.Tactics.Typeclasses

open Lib.Arithmetic.Group
open Lib.Arithmetic.Ring

open FStar.Math.Lemmas

open FStar.Mul

module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators

#reset-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

let br i x =
  let v = UInt.to_vec #i x in
  let vbr = Seq.createi i (fun p -> (index #_ #i v (i-1-p))) in
  UInt.from_vec #i vbr

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
    plus #a (mul (repeat_plus one ((i+1)%2)) peven.[i/2]) (mul (repeat_plus one (i%2)) podd.[i/2]) in
  let p = createi n f in
  let customprop (k:nat{k<n/2}) : Type0 = ((==) #a p.[2*k] peven.[k] /\ (==) #a p.[2*k+1] podd.[k]) in
  let customlemma (k:nat{k<n/2}) : Lemma (customprop k) =
    let m = (add_ag #a).g.m in
    //assert (p.[2*k] == peven.[k]);
    cancel_mul_mod k 2;
    lemma_repeat_op_zero #a one;
    lemma_zero_absorb1 #a podd.[(2*k)/2];
    lemma_mod_plus 1 k 2;
    lemma_repeat_op_succ1 #a one 0;
    lemma_zero2 #a one;
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
