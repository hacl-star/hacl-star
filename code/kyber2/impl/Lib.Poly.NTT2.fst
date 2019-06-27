module Lib.Poly.NTT2

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open FStar.Mul
open FStar.Math.Lemmas
open FStar.Classical
open FStar.Tactics
open FStar.Tactics.Typeclasses

//open Lib.ModularArithmetic
//open Lib.ModularArithmetic.Lemmas

open Lib.Arithmetic.Group
open Lib.Arithmetic.Ring
open Lib.Arithmetic.Sums
open Lib.Poly.NTT


//friend Lib.ModularArithmetic.Lemmas

module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators


#reset-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val br: i:size_nat -> x:nat{x<pow2 i} -> y:nat{y<pow2 i}
let br i x = 
  let v = UInt.to_vec #i x in
  let vbr = Seq.createi i (fun p -> (index #_ #i v (i-1-p))) in
  UInt.from_vec #i vbr
  
val br_involutive: i:size_nat -> x:nat{x<pow2 i} -> Lemma (br i (br i x) = x)

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

val reorg: #a:Type0 -> #n:size_nat -> i:size_nat{n = pow2 i} -> p:lib_poly a n -> lib_poly a n
let reorg #a #n i p =
  Seq.createi n (fun x -> p.[br i x])

val reorg_involutive: #a:Type0 -> #n:size_nat -> i:size_nat{n = pow2 i} -> p:lib_poly a n -> Lemma (reorg i (reorg i p) == p)

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
  
val split_seq:
   #a:Type0
   -> #n:size_nat{n%2=0}
   -> p:lib_poly a n 
   -> Tot (p':((lib_poly a (n / 2)) & (lib_poly a (n / 2))){let (peven,podd)=p' in forall(k:nat{k < n / 2}). peven.[k] == p.[2*k] /\ podd.[k] == p.[2*k+1]})

let split_seq #a #n p =
  let peven = createi (n/2) (fun i -> p.[2*i]) in
  let podd = createi (n/2) (fun i -> p.[2*i+1]) in
  peven,podd

val join_seq:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat{n%2=0}
  -> peven:lib_poly a (n/2) 
  -> podd:lib_poly a (n/2)
  -> p:lib_poly a n{forall(k:nat{k<n/2}). p.[2*k] == peven.[k] /\ p.[2*k+1] == podd.[k]}

let join_seq #a [|ring a|] #n peven podd =
  let f (i:nat{i<n}) : a =
    plus #a (mul (repeat_plus one ((i+1)%2)) peven.[i/2]) (mul (repeat_plus one (i%2)) podd.[i/2]) in
  let p = createi n f in
  let customprop (k:nat{k<n/2}) : Type0 = ((==) #a p.[2*k] peven.[k] /\ (==) #a p.[2*k+1] podd.[k]) in
  let customlemma (k:nat{k<n/2}) : Lemma (customprop k) =
    let m = add_ag.g.m in
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

val lemma_split_join: 
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat{n%2=0}
  -> p:lib_poly a n 
  -> Lemma (let peven,podd = split_seq p in join_seq peven podd == p)

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

val lemma_join_split:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat{n%2=0}
  -> p1:lib_poly a (n/2)
  -> p2:lib_poly a (n/2)
  -> Lemma (let peven,podd = split_seq (join_seq p1 p2) in peven == p1 /\ podd == p2)

let lemma_join_split #a [| ring a |] #n p1 p2 =
  let p = join_seq p1 p2 in
  let peven,podd = split_seq p in
  lemma_split_join p;
  assert(join_seq peven podd == p);
  eq_intro p1 peven;
  eq_elim p1 peven;
  eq_intro p2 podd;
  eq_elim p2 podd


let lib_ntt #a [| ring a |] #n i zeta p = 
  let (peven, podd) = split_seq p in
  join_seq (reorg i (Lib.Poly.NTT.lib_ntt (exp #a zeta 2) zeta peven)) (reorg i (Lib.Poly.NTT.lib_ntt (exp #a zeta 2) zeta podd))


//let lib_ntt_lemma #n #m omega psi p p' = ()

let lib_nttinv #a [| ring a |] #n i halfninv zetainv p = 
  let (peven, podd) = split_seq p in
  join_seq (Lib.Poly.NTT.lib_nttinv halfninv (exp #a zetainv 2) zetainv (reorg i peven)) (Lib.Poly.NTT.lib_nttinv halfninv (exp #a zetainv 2) zetainv (reorg i podd))

//let lib_nttinv_lemma #n #m ninv omegainv psiinv p p' = ()

  
#reset-options "--z3rlimit 200 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"


let lib_ntt_inversion_lemma1 #a [| ring a |] #n i halfninv zeta zetainv p =
  let zeta2 = exp #a zeta 2 in
  let zetainv2 = exp #a zetainv 2 in
  let (peven, podd) = split_seq p in
  let p1 = Lib.Poly.NTT.lib_ntt zeta2 zeta peven in
  let p2 = Lib.Poly.NTT.lib_ntt zeta2 zeta podd in
  let pntt = lib_ntt i zeta p in
  let p' = lib_nttinv i halfninv zetainv pntt in
  //assert(pntt == join_list p1 p2);
  //lemma_join_split p1 p2;
  let (pntt1:lib_poly a (n/2)),(pntt2:lib_poly a (n/2)) = split_seq pntt in
  let peven' = Lib.Poly.NTT.lib_nttinv halfninv zetainv2 zetainv (reorg i pntt1) in
  let podd' = Lib.Poly.NTT.lib_nttinv halfninv zetainv2 zetainv (reorg i pntt2) in
  let p1' = Lib.Poly.NTT.lib_nttinv halfninv zetainv2 zetainv p1 in
  let p2' = Lib.Poly.NTT.lib_nttinv halfninv zetainv2 zetainv p2 in
  lemma_join_split (reorg i p1) (reorg i p2);
  assert(pntt1 == (reorg i p1) /\ pntt2 == (reorg i p2));
  reorg_involutive i p1;
  reorg_involutive i p2;
  eq_intro p1' peven';
  eq_elim p1' peven';
  eq_intro p2' podd';
  eq_elim p2' podd';
  
  lemma_exp_exp #a zeta 2 (n/2);
  assert (exp zeta2 (n/2) == one);  
  let customprop (nn:nat{nn<(n/2)}) : Type0 = (exp #a zeta2 nn == one ==> nn = 0) /\ ((~(is_invertible(minus (exp #a zeta2 nn) one)) ==> nn = 0)) in
  let customlemma (nn:nat{nn<(n/2)}) : Lemma (customprop nn) =
     lemma_exp_exp #a zeta 2 (nn)
  in
  FStar.Classical.forall_intro customlemma;
  lemma_exp_inv zeta zetainv 2;
  lib_ntt_inversion_lemma1 halfninv zeta2 zetainv2 zeta zetainv peven;
  lib_ntt_inversion_lemma1 halfninv zeta2 zetainv2 zeta zetainv podd; 
  assert(peven == peven'); 
  assert(podd == podd');

  lemma_split_join p;

  eq_intro p (join_seq peven' podd');
  eq_elim p (join_seq peven' podd');

  eq_intro p' p;
  eq_elim p' p

let lib_ntt_inversion_lemma2 #a [| ring a |] #n i halfninv zeta zetainv p =
  let zeta2 = exp #a zeta 2 in
  let zetainv2 = exp #a zetainv 2 in
  let (peven, podd) = split_seq p in
  let p1 = Lib.Poly.NTT.lib_nttinv halfninv zetainv2 zetainv (reorg i peven) in
  let p2 = Lib.Poly.NTT.lib_nttinv halfninv zetainv2 zetainv (reorg i podd) in
  let pnttinv = lib_nttinv i halfninv zetainv p in
  let p' = lib_ntt i zeta pnttinv in
  //assert(pnttinv == join_list p1 p2);
  //lemma_join_split p1 p2;
  let (pnttinv1:lib_poly a (n/2)),(pnttinv2:lib_poly a (n/2)) = split_seq pnttinv in
  let peven' = Lib.Poly.NTT.lib_ntt zeta2 zeta pnttinv1 in
  let podd' = Lib.Poly.NTT.lib_ntt zeta2 zeta pnttinv2 in
  let p1' = Lib.Poly.NTT.lib_ntt zeta2 zeta p1 in
  let p2' = Lib.Poly.NTT.lib_ntt zeta2 zeta p2 in
  lemma_join_split p1 p2;
  assert(pnttinv1 == p1 /\ pnttinv2 == p2);
  eq_intro p1' peven';
  eq_elim p1' peven';
  eq_intro p2' podd';
  eq_elim p2' podd';

  lemma_exp_exp #a zeta 2 (n/2);
  assert (exp zeta2 (n/2) == one);  
  let customprop (nn:nat{nn<(n/2)}) : Type0 = (exp #a zeta2 nn == one ==> nn = 0) /\ ((~(is_invertible(minus (exp #a zeta2 nn) one)) ==> nn = 0)) in
  let customlemma (nn:nat{nn<(n/2)}) : Lemma (customprop nn) =
     lemma_exp_exp #a zeta 2 (nn)
  in
  FStar.Classical.forall_intro customlemma;
  lemma_exp_inv zetainv zeta 2;
  lib_ntt_inversion_lemma2 halfninv zeta2 zetainv2 zeta zetainv (reorg i peven);
  lib_ntt_inversion_lemma2 halfninv zeta2 zetainv2 zeta zetainv (reorg i podd); 
  assert(reorg i peven == peven'); 
  assert(reorg i podd == podd');

  lemma_split_join p;

  reorg_involutive i peven;
  reorg_involutive i podd;
  
  eq_intro p (join_seq (reorg i peven') (reorg i podd'));
  eq_elim p (join_seq (reorg i peven') (reorg i podd'));

  eq_intro p' p;
  eq_elim p' p


val lib_ntt_plus:
  #a:Type0
  -> #[tcresolve ()] r: ring a
  -> #n:size_nat{n%2=0}
  -> p1:lib_poly a n
  -> p2:lib_poly a n
  -> p:lib_poly a n

let lib_ntt_plus #a [| ring a |] #n =
  Seq.map2 plus

val lib_ntt_zero:
  #a:Type0
  -> #[tcresolve ()] r: ring a
  -> #n:size_nat{n%2=0}
  -> p:lib_poly a n

let lib_ntt_zero #a [| ring a |] #n = 
  Lib.Arithmetic.Group.Sequence.id_lseq #a #add_ag.g.m #n

val lib_ntt_lemma_plus_assoc:
  #a:Type0
  -> #[tcresolve ()] r: ring a
  -> #n:size_nat{n%2=0}
  -> p1:lib_poly a n
  -> p2:lib_poly a n
  -> p3:lib_poly a n
  -> Lemma (lib_ntt_plus (lib_ntt_plus p1 p2) p3 == lib_ntt_plus p1 (lib_ntt_plus p2 p3))

let lib_ntt_lemma_plus_assoc #a [| ring a |] #n = Lib.Arithmetic.Group.Sequence.lemma_assoc_lseq #a #add_ag.g.m #n

val lib_ntt_lemma_zero1:
  #a:Type0
  -> #[tcresolve ()] r: ring a
  -> #n:size_nat{n%2=0}
  -> p:lib_poly a n
  -> Lemma (lib_ntt_plus lib_ntt_zero p == p)

let lib_ntt_lemma_zero1 #a [| ring a |] #n =
  Lib.Arithmetic.Group.Sequence.lemma_id1_lseq #a #add_ag.g.m #n

val lib_ntt_lemma_zero2:
  #a:Type0
  -> #[tcresolve ()] r: ring a
  -> #n:size_nat{n%2=0}
  -> p:lib_poly a n
  -> Lemma (lib_ntt_plus p lib_ntt_zero == p)

let lib_ntt_lemma_zero2 #a [| ring a |] #n =
  Lib.Arithmetic.Group.Sequence.lemma_id2_lseq #a #add_ag.g.m #n

instance lib_ntt_plus_monoid : (#a:Type0) -> (#[tcresolve ()] r:ring a) -> (#n:size_nat{n%2=0}) -> monoid (lib_poly a n) =
  fun #a #r #n ->
    {
      id = lib_ntt_zero;
      op = lib_ntt_plus;
      lemma_assoc = lib_ntt_lemma_plus_assoc;
      lemma_id1 = lib_ntt_lemma_zero1;
      lemma_id2 = lib_ntt_lemma_zero2;
    }

val lib_ntt_opp:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat{n%2=0}
  -> p:lib_poly a n
  -> p':lib_poly a n

let lib_ntt_opp #a [| ring a |] #n =
  Seq.map opp

val lib_ntt_lemma_opp1:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat{n%2=0}
  -> p:lib_poly a n
  -> Lemma (plus p (opp p) == zero)

let lib_ntt_lemma_opp1 #a [| ring a |] #n =
  Lib.Arithmetic.Group.Sequence.lemma_sym1_lseq #a #add_ag.g #n

val lib_ntt_lemma_opp2:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat{n%2=0}
  -> p:lib_poly a n
  -> Lemma (plus (opp p) p == zero)

let lib_ntt_lemma_opp2 #a [| ring a |] #n =
  Lib.Arithmetic.Group.Sequence.lemma_sym2_lseq #a #add_ag.g #n

instance lib_ntt_plus_group: (#a:Type0) -> (#[tcresolve ()] r:ring a) -> (#n:size_nat{n%2=0}) -> group (lib_poly a n) =
  fun #a #r #n ->
    {
      m = lib_ntt_plus_monoid;
      sym = lib_ntt_opp;
      lemma_sym1 = lib_ntt_lemma_opp1;
      lemma_sym2 = lib_ntt_lemma_opp2;
    }

val lib_ntt_lemma_plus_swap:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat{n%2=0}
  -> p1:lib_poly a n
  -> p2:lib_poly a n
  -> Lemma (plus p1 p2 == plus p2 p1)

let lib_ntt_lemma_plus_swap #a [| ring a |] #n =
  Lib.Arithmetic.Group.Sequence.lemma_swap_lseq #a #add_ag #n


instance lib_ntt_plus_abelian_group: (#a:Type0) -> (#[tcresolve ()] r:ring a) -> (#n:size_nat{n%2=0}) -> abelian_group (lib_poly a n) =
  fun #a #r #n ->
    {
      g = lib_ntt_plus_group;
      lemma_swap = lemma_plus_swap;
    }

val lib_ntt_mul:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat{n%2=0}
  -> i:size_nat{pow2 i = (n/2)}
  -> zeta:a
  -> p1:lib_poly a n
  -> p2:lib_poly a n
  -> p:lib_poly a n
  
let lib_ntt_mul #a [| ring a |] #n i zeta p1 p2 =
  let plus = plus #a in
  let mul = mul #a in
  let p1even,p1odd = split_seq p1 in
  let p2even,p2odd = split_seq p2 in
  let f (k:nat{k<n/2}) = plus (mul p1even.[k] p2even.[k]) (mul (mul p1odd.[k] p2odd.[k]) (exp zeta (2*(br i k)+1))) in
  let g (k:nat{k<n/2}) = plus (mul p1odd.[k] p2even.[k]) (mul p1even.[k] p2odd.[k]) in
  let l = createi (n/2) (fun x -> x) in
  join_seq (Seq.map f l) (Seq.map g l)

val lib_ntt_one:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat{n%2=0}
  -> p:lib_poly a n

let lib_ntt_one #a [| ring a |] #n =
  join_seq (create (n/2) one) (create (n/2) zero)

#reset-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val lib_ntt_lemma_mul_assoc:
  #a:Type0
  -> #[tcresolve ()] r: ring a
  -> #n:size_nat{n%2=0}
  -> i:size_nat{pow2 i = n/2}
  -> zeta:a{forall (x:a). mul x zeta == mul zeta x}
  -> p1:lib_poly a n
  -> p2:lib_poly a n
  -> p3:lib_poly a n
  -> Lemma (lib_ntt_mul i zeta (lib_ntt_mul i zeta p1 p2) p3 == lib_ntt_mul i zeta p1 (lib_ntt_mul i zeta p2 p3))

let lib_ntt_lemma_mul_assoc #a [| ring a |] #n i zeta p1 p2 p3 = 
  let rec commut_zeta (x:a) (j:nat) : Lemma (ensures mul #a x (exp zeta j) == mul #a (exp zeta j) x) (decreases j) =
    if (j=0) then
      (lemma_exp_zero #a zeta; lemma_one1 x; lemma_one2 x)
    else begin
      lemma_exp_succ1 #a zeta (j-1);
      lemma_mul_assoc x zeta (exp #a zeta (j-1));
      lemma_mul_assoc #a zeta x (exp #a zeta (j-1));
      commut_zeta x (j-1);
      lemma_mul_assoc zeta (exp #a zeta (j-1)) x end
  in
  let p12 = lib_ntt_mul i zeta p1 p2 in
  let p12_3 = lib_ntt_mul i zeta p12 p3 in
  let p23 = lib_ntt_mul i zeta p2 p3 in
  let p1_23 = lib_ntt_mul i zeta p1 p23 in
  let lemma_mul_assoc = lemma_mul_assoc #a in
  let lemma_plus_assoc = lemma_plus_assoc #a in
  let lemma_plus_swap = lemma_plus_swap #a in
  let lemma_distr_right = lemma_distr_right #a in
  let lemma_distr_left = lemma_distr_left #a in
  let customprop (k:nat{k<n}) : Type0 = (p12_3.[k] == p1_23.[k]) in
  let customlemma (k:nat{k<n}) : Lemma (customprop k) =
  euclidean_division_definition k 2; 
  if (k%2 = 0) then begin
    let k' = 2*(br i (k/2)) in
    assert(k == (k/2)*2);
    assert(p12_3.[k] == plus #a (mul p12.[k] p3.[k]) (mul (mul p12.[k+1] p3.[k+1]) (exp zeta (k'+1))));
    assert(p12_3.[k] == plus #a (mul (plus #a (mul p1.[k] p2.[k]) (mul (mul p1.[k+1] p2.[k+1]) (exp zeta (k'+1)))) p3.[k]) (mul (mul (plus #a (mul p1.[k+1] p2.[k]) (mul p1.[k] p2.[k+1])) p3.[k+1]) (exp zeta (k'+1))));
    lemma_distr_right p3.[k] (mul p1.[k] p2.[k]) (mul (mul p1.[k+1] p2.[k+1]) (exp zeta (k'+1)));
    lemma_distr_right p3.[k+1] (mul p1.[k+1] p2.[k]) (mul p1.[k] p2.[k+1]);
    lemma_distr_right (exp zeta (k'+1)) (mul (mul p1.[k+1] p2.[k]) p3.[k+1]) (mul (mul p1.[k] p2.[k+1]) p3.[k+1]);
    assert(p12_3.[k] == plus #a (plus #a (mul (mul p1.[k] p2.[k]) p3.[k]) (mul (mul (mul p1.[k+1] p2.[k+1]) (exp zeta (k'+1))) p3.[k])) (plus #a (mul (mul (mul p1.[k+1] p2.[k]) p3.[k+1]) (exp zeta (k'+1))) (mul (mul (mul p1.[k] p2.[k+1]) p3.[k+1]) (exp zeta (k'+1)))));
    
    lemma_mul_assoc p1.[k] p2.[k] p3.[k];
    
    lemma_mul_assoc (mul p1.[k+1] p2.[k+1]) (exp zeta (k'+1)) p3.[k];
    commut_zeta p3.[k] (k'+1);
    lemma_mul_assoc (mul p1.[k+1] p2.[k+1]) p3.[k] (exp zeta (k'+1));
    lemma_mul_assoc p1.[k+1] p2.[k+1] p3.[k];
    
    lemma_mul_assoc p1.[k+1] p2.[k] p3.[k+1];
    
    lemma_mul_assoc p1.[k] p2.[k+1] p3.[k+1];
    lemma_mul_assoc p1.[k] (mul p2.[k+1] p3.[k+1]) (exp zeta (k'+1));

    assert(p12_3.[k] == plus #a (plus #a (mul p1.[k] (mul p2.[k] p3.[k])) (mul (mul p1.[k+1] (mul p2.[k+1] p3.[k])) (exp zeta (k'+1)))) (plus #a (mul (mul p1.[k+1] (mul p2.[k] p3.[k+1])) (exp zeta (k'+1))) (mul p1.[k] (mul (mul p2.[k+1] p3.[k+1]) (exp zeta (k'+1))))));
    lemma_plus_swap (mul #a (mul p1.[k+1] (mul p2.[k] p3.[k+1])) (exp zeta (k'+1))) (mul #a p1.[k] (mul (mul p2.[k+1] p3.[k+1]) (exp zeta (k'+1))));
    lemma_plus_assoc (plus #a (mul p1.[k] (mul p2.[k] p3.[k])) (mul (mul p1.[k+1] (mul p2.[k+1] p3.[k])) (exp zeta (k'+1)))) (mul #a p1.[k] (mul (mul p2.[k+1] p3.[k+1]) (exp zeta (k'+1)))) (mul #a (mul p1.[k+1] (mul p2.[k] p3.[k+1])) (exp zeta (k'+1)));
    lemma_plus_assoc (mul #a p1.[k] (mul p2.[k] p3.[k])) (mul #a (mul p1.[k+1] (mul p2.[k+1] p3.[k])) (exp zeta (k'+1))) (mul #a p1.[k] (mul (mul p2.[k+1] p3.[k+1]) (exp zeta (k'+1))));
    lemma_plus_swap (mul #a (mul p1.[k+1] (mul p2.[k+1] p3.[k])) (exp zeta (k'+1))) (mul #a p1.[k] (mul (mul p2.[k+1] p3.[k+1]) (exp zeta (k'+1))));
    lemma_plus_assoc (mul #a p1.[k] (mul p2.[k] p3.[k])) (mul #a p1.[k] (mul (mul p2.[k+1] p3.[k+1]) (exp zeta (k'+1)))) (mul #a (mul p1.[k+1] (mul p2.[k+1] p3.[k])) (exp zeta (k'+1)));
    lemma_plus_assoc (plus (mul #a p1.[k] (mul p2.[k] p3.[k])) (mul #a p1.[k] (mul (mul p2.[k+1] p3.[k+1]) (exp zeta (k'+1))))) (mul #a (mul p1.[k+1] (mul p2.[k+1] p3.[k])) (exp zeta (k'+1))) (mul #a (mul p1.[k+1] (mul p2.[k] p3.[k+1])) (exp zeta (k'+1)));
    assert(p12_3.[k] == plus #a (plus #a (mul p1.[k] (mul p2.[k] p3.[k])) (mul p1.[k] (mul (mul p2.[k+1] p3.[k+1]) (exp zeta (k'+1))))) (plus #a (mul (mul p1.[k+1] (mul p2.[k+1] p3.[k])) (exp zeta (k'+1))) (mul (mul p1.[k+1] (mul p2.[k] p3.[k+1])) (exp zeta (k'+1)))));
    lemma_distr_left p1.[k] (mul p2.[k] p3.[k]) (mul (mul p2.[k+1] p3.[k+1]) (exp zeta (k'+1)));
    lemma_distr_right (exp zeta (k'+1)) (mul p1.[k+1] (mul p2.[k+1] p3.[k])) (mul p1.[k+1] (mul p2.[k] p3.[k+1]));
    lemma_distr_left p1.[k+1] (mul p2.[k+1] p3.[k]) (mul p2.[k] p3.[k+1])
    end
 else begin
   let k' = 2*(br i ((k-1)/2)) + 1 in
   assert(k=((k-1)/2)*2+1);
   assert(p12_3.[k] == plus #a (mul p12.[k] p3.[k-1]) (mul p12.[k-1] p3.[k]));
   assert(p12_3.[k] == plus #a (mul (plus #a (mul p1.[k] p2.[k-1]) (mul p1.[k-1] p2.[k])) p3.[k-1]) (mul (plus #a (mul p1.[k-1] p2.[k-1]) (mul (mul p1.[k] p2.[k]) (exp zeta k'))) p3.[k]));
   lemma_distr_right p3.[k-1] (mul p1.[k] p2.[k-1]) (mul p1.[k-1] p2.[k]);
   lemma_distr_right p3.[k] (mul p1.[k-1] p2.[k-1]) (mul (mul p1.[k] p2.[k]) (exp zeta k'));
   lemma_mul_assoc p1.[k] p2.[k-1] p3.[k-1];

   lemma_mul_assoc p1.[k-1] p2.[k] p3.[k-1];

   lemma_mul_assoc p1.[k-1] p2.[k-1] p3.[k];

   lemma_mul_assoc (mul p1.[k] p2.[k]) (exp zeta k') p3.[k];
   commut_zeta p3.[k] k';
   lemma_mul_assoc (mul p1.[k] p2.[k]) p3.[k] (exp zeta k');
   lemma_mul_assoc p1.[k] p2.[k] p3.[k];
   lemma_mul_assoc p1.[k] (mul p2.[k] p3.[k]) (exp zeta k');

   lemma_plus_swap (mul p1.[k-1] (mul p2.[k-1] p3.[k])) (mul p1.[k] (mul (mul p2.[k] p3.[k]) (exp zeta k')));
   lemma_plus_assoc (plus (mul p1.[k] (mul p2.[k-1] p3.[k-1])) (mul p1.[k-1] (mul p2.[k] p3.[k-1]))) (mul p1.[k] (mul (mul p2.[k] p3.[k]) (exp zeta k'))) (mul p1.[k-1] (mul p2.[k-1] p3.[k]));
   lemma_plus_assoc (mul p1.[k] (mul p2.[k-1] p3.[k-1])) (mul p1.[k-1] (mul p2.[k] p3.[k-1])) (mul p1.[k] (mul (mul p2.[k] p3.[k]) (exp zeta k')));
   lemma_plus_swap (mul p1.[k-1] (mul p2.[k] p3.[k-1])) (mul p1.[k] (mul (mul p2.[k] p3.[k]) (exp zeta k')));
   lemma_plus_assoc (mul p1.[k] (mul p2.[k-1] p3.[k-1])) (mul p1.[k] (mul (mul p2.[k] p3.[k]) (exp zeta k'))) (mul p1.[k-1] (mul p2.[k] p3.[k-1]));
   lemma_plus_assoc (plus (mul p1.[k] (mul p2.[k-1] p3.[k-1])) (mul p1.[k] (mul (mul p2.[k] p3.[k]) (exp zeta k')))) (mul p1.[k-1] (mul p2.[k] p3.[k-1])) (mul p1.[k-1] (mul p2.[k-1] p3.[k]));
   lemma_distr_left p1.[k] (mul p2.[k-1] p3.[k-1]) (mul (mul p2.[k] p3.[k]) (exp zeta k'));
   lemma_distr_left p1.[k-1] (mul p2.[k] p3.[k-1]) (mul p2.[k-1] p3.[k])
  end
  in FStar.Classical.forall_intro customlemma;
  eq_intro p12_3 p1_23;
  eq_elim p12_3 p1_23

#reset-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val lib_ntt_lemma_one1:
  #a:Type0
  -> #[tcresolve ()] r: ring a
  -> #n:size_nat{n%2=0}
  -> i:size_nat{pow2 i = n/2}
  -> zeta:a
  -> p:lib_poly a n
  -> Lemma (lib_ntt_mul i zeta lib_ntt_one p == p)


let lib_ntt_lemma_one1 #a [| ring a |] #n i zeta p =
  let p' = lib_ntt_mul i zeta lib_ntt_one p in
  let customprop (k:nat{k<n}) : Type0 = (p'.[k] == p.[k]) in
  let customlemma (k:nat{k<n}) : Lemma (customprop k) =
    if(k%2=0) then begin
      let k' = 2*(br i (k/2)) in
      lemma_one1 #a p.[k];
      lemma_zero_absorb1 #a p.[k+1];
      lemma_zero_absorb1 #a (exp zeta (k'+1));
      lemma_zero2 #a p.[k]
      end
    else begin
      lemma_zero_absorb1 #a p.[k-1];
      lemma_one1 #a p.[k];
      lemma_zero1 #a p.[k]
      end    
  in FStar.Classical.forall_intro customlemma;
  eq_intro p' p;
  eq_elim p' p

 
val lib_ntt_lemma_one2:
  #a:Type0
  -> #[tcresolve ()] r: ring a
  -> #n:size_nat{n%2=0}
  -> i:size_nat{pow2 i = n/2}
  -> zeta:a
  -> p:lib_poly a n
  -> Lemma (lib_ntt_mul i zeta p lib_ntt_one == p)


let lib_ntt_lemma_one2 #a [| ring a |] #n i zeta p =
  let p' = lib_ntt_mul i zeta p lib_ntt_one in
  let customprop (k:nat{k<n}) : Type0 = (p'.[k] == p.[k]) in
  let customlemma (k:nat{k<n}) : Lemma (customprop k) =
    if(k%2=0) then begin
      let k' = 2*(br i (k/2)) in
      lemma_one2 #a p.[k];
      lemma_zero_absorb2 #a p.[k+1];
      lemma_zero_absorb1 #a (exp zeta (k'+1));
      lemma_zero2 #a p.[k]
      end
    else begin
      lemma_zero_absorb2 #a p.[k-1];
      lemma_one2 #a p.[k];
      lemma_zero2 #a p.[k]
      end
  in FStar.Classical.forall_intro customlemma;
  eq_intro p' p;
  eq_elim p' p

instance lib_ntt_mul_monoid : (#a:Type0) -> (#[tcresolve ()] r:ring a) -> (#n:size_nat{n%2=0}) -> (i:size_nat{pow2 i = n/2}) -> zeta:a{forall (x:a). mul x zeta == mul zeta x} -> monoid (lib_poly a n) =
  fun #a #r #n i zeta ->
    {
      id = lib_ntt_one;
      op = lib_ntt_mul #a i zeta;
      lemma_assoc = lib_ntt_lemma_mul_assoc #a i zeta;
      lemma_id1 = lib_ntt_lemma_one1 #a i zeta;
      lemma_id2 = lib_ntt_lemma_one2 #a i zeta;
    }

#reset-options "--z3rlimit 1000 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val lib_ntt_lemma_distr_left:
  #a:Type0
  -> #[tcresolve ()] r: ring a
  -> #n:size_nat{n%2=0}
  -> i:size_nat{pow2 i = n/2}
  -> zeta:a
  -> p1:lib_poly a n
  -> p2:lib_poly a n
  -> p3:lib_poly a n
  -> Lemma (lib_ntt_mul i zeta p1 (lib_ntt_plus p2 p3) == lib_ntt_plus (lib_ntt_mul i zeta p1 p2) (lib_ntt_mul i zeta p1 p3))

let lib_ntt_lemma_distr_left #a [| ring a |] #n i zeta p1 p2 p3 =
  let p1_23 = lib_ntt_mul i zeta p1 (lib_ntt_plus p2 p3) in
  let p12_13 = lib_ntt_plus (lib_ntt_mul i zeta p1 p2) (lib_ntt_mul i zeta p1 p3) in
  let customprop (k:nat{k<n}) : Type0 = (p1_23.[k] == p12_13.[k]) in
  let customlemma (k:nat{k<n}) : Lemma (customprop k) =
   if(k%2=0) then begin
      let k' = 2*(br i (k/2)) in
      assert(p1_23.[k] == plus #a (mul p1.[k] (plus p2.[k] p3.[k])) (mul (mul p1.[k+1] (plus p2.[k+1] p3.[k+1])) (exp zeta (k'+1))));
      lemma_distr_left #a p1.[k] p2.[k] p3.[k];
      lemma_distr_left #a p1.[k+1] p2.[k+1] p3.[k+1];
      lemma_distr_right #a (exp zeta (k'+1)) (mul p1.[k+1] p2.[k+1]) (mul p1.[k+1] p3.[k+1]);
      assert(p1_23.[k] == plus #a (plus (mul p1.[k] p2.[k]) (mul p1.[k] p3.[k])) (plus (mul (mul p1.[k+1] p2.[k+1]) (exp zeta (k'+1))) (mul (mul p1.[k+1] p3.[k+1]) (exp zeta (k'+1)))));
      lemma_plus_assoc #a (plus (mul p1.[k] p2.[k]) (mul p1.[k] p3.[k])) (mul (mul p1.[k+1] p2.[k+1]) (exp zeta (k'+1))) (mul (mul p1.[k+1] p3.[k+1]) (exp zeta (k'+1)));
      assert(p1_23.[k] == plus #a (plus (plus (mul p1.[k] p2.[k]) (mul p1.[k] p3.[k])) (mul (mul p1.[k+1] p2.[k+1]) (exp zeta (k'+1)))) (mul (mul p1.[k+1] p3.[k+1]) (exp zeta (k'+1))));
      lemma_plus_assoc #a (mul p1.[k] p2.[k]) (mul p1.[k] p3.[k]) (mul (mul p1.[k+1] p2.[k+1]) (exp zeta (k'+1)));
      assert(p1_23.[k] == plus #a (plus (mul p1.[k] p2.[k]) (plus (mul p1.[k] p3.[k]) (mul (mul p1.[k+1] p2.[k+1]) (exp zeta (k'+1))))) (mul (mul p1.[k+1] p3.[k+1]) (exp zeta (k'+1))));
      lemma_plus_swap #a (mul p1.[k] p3.[k]) (mul (mul p1.[k+1] p2.[k+1]) (exp zeta (k'+1)));
      assert(p1_23.[k] == plus #a (plus (mul p1.[k] p2.[k]) (plus (mul (mul p1.[k+1] p2.[k+1]) (exp zeta (k'+1))) (mul p1.[k] p3.[k]))) (mul (mul p1.[k+1] p3.[k+1]) (exp zeta (k'+1))));
      lemma_plus_assoc #a (mul p1.[k] p2.[k]) (mul (mul p1.[k+1] p2.[k+1]) (exp zeta (k'+1))) (mul p1.[k] p3.[k]);
      lemma_plus_assoc #a (plus (mul p1.[k] p2.[k]) (mul (mul p1.[k+1] p2.[k+1]) (exp zeta (k'+1)))) (mul p1.[k] p3.[k]) (mul (mul p1.[k+1] p3.[k+1]) (exp zeta (k'+1)))
    end
    else begin
      lemma_distr_left #a p1.[k] p2.[k-1] p3.[k-1];
      lemma_distr_left #a p1.[k-1] p2.[k] p3.[k];
      lemma_plus_assoc #a (plus (mul p1.[k] p2.[k-1]) (mul p1.[k] p3.[k-1])) (mul p1.[k-1] p2.[k]) (mul p1.[k-1] p3.[k]);
      lemma_plus_assoc #a (mul p1.[k] p2.[k-1]) (mul p1.[k] p3.[k-1]) (mul p1.[k-1] p2.[k]);
      lemma_plus_swap #a (mul p1.[k] p3.[k-1]) (mul p1.[k-1] p2.[k]);
      lemma_plus_assoc #a (mul p1.[k] p2.[k-1]) (mul p1.[k-1] p2.[k]) (mul p1.[k] p3.[k-1]);
      lemma_plus_assoc #a (plus (mul p1.[k] p2.[k-1]) (mul p1.[k-1] p2.[k])) (mul p1.[k] p3.[k-1]) (mul p1.[k-1] p3.[k])
    end
  in FStar.Classical.forall_intro customlemma;
  eq_intro p1_23 p12_13;
  eq_elim p1_23 p12_13

#reset-options "--z3rlimit 1000 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val lib_ntt_lemma_distr_right:
  #a:Type0
  -> #[tcresolve ()] r: ring a
  -> #n:size_nat{n%2=0}
  -> i:size_nat{pow2 i = n/2}
  -> zeta:a
  -> p1:lib_poly a n
  -> p2:lib_poly a n
  -> p3:lib_poly a n
  -> Lemma (lib_ntt_mul i zeta (lib_ntt_plus p2 p3) p1 == lib_ntt_plus (lib_ntt_mul i zeta p2 p1) (lib_ntt_mul i zeta p3 p1))

let lib_ntt_lemma_distr_right #a [| ring a |] #n i zeta p1 p2 p3 =
  let p23_1 = lib_ntt_mul i zeta (lib_ntt_plus p2 p3) p1 in
  let p21_31 = lib_ntt_plus (lib_ntt_mul i zeta p2 p1) (lib_ntt_mul i zeta p3 p1) in
  let customprop (k:nat{k<n}) : Type0 = (p23_1.[k] == p21_31.[k]) in
  let customlemma (k:nat{k<n}) : Lemma (customprop k) =
    if(k%2=0) then begin
      let k' = 2*(br i (k/2)) in
      assert(p23_1.[k] == plus #a (mul (plus p2.[k] p3.[k]) p1.[k]) (mul (mul (plus p2.[k+1] p3.[k+1]) p1.[k+1]) (exp zeta (k'+1))));
      lemma_distr_right #a p1.[k] p2.[k] p3.[k];
      lemma_distr_right #a p1.[k+1] p2.[k+1] p3.[k+1];
      lemma_distr_right #a (exp zeta (k'+1)) (mul p2.[k+1] p1.[k+1]) (mul p3.[k+1] p1.[k+1]);
      assert(p23_1.[k] == plus #a (plus (mul p2.[k] p1.[k]) (mul p3.[k] p1.[k])) (plus (mul (mul p2.[k+1] p1.[k+1]) (exp zeta (k'+1))) (mul (mul p3.[k+1] p1.[k+1]) (exp zeta (k'+1)))));
      lemma_plus_assoc #a (plus (mul p2.[k] p1.[k]) (mul p3.[k] p1.[k])) (mul (mul p2.[k+1] p1.[k+1]) (exp zeta (k'+1))) (mul (mul p3.[k+1] p1.[k+1]) (exp zeta (k'+1)));
      assert(p23_1.[k] == plus #a (plus (plus (mul p2.[k] p1.[k]) (mul p3.[k] p1.[k])) (mul (mul p2.[k+1] p1.[k+1]) (exp zeta (k'+1)))) (mul (mul p3.[k+1] p1.[k+1]) (exp zeta (k'+1))));
      lemma_plus_assoc #a (mul p2.[k] p1.[k]) (mul p3.[k] p1.[k]) (mul (mul p2.[k+1] p1.[k+1]) (exp zeta (k'+1)));
      assert(p23_1.[k] == plus #a (plus (mul p2.[k] p1.[k]) (plus (mul p3.[k] p1.[k]) (mul (mul p2.[k+1] p1.[k+1]) (exp zeta (k'+1))))) (mul (mul p3.[k+1] p1.[k+1]) (exp zeta (k'+1))));
      lemma_plus_swap #a (mul p3.[k] p1.[k]) (mul (mul p2.[k+1] p1.[k+1]) (exp zeta (k'+1)));
      lemma_plus_assoc #a (mul p2.[k] p1.[k]) (mul (mul p2.[k+1] p1.[k+1]) (exp zeta (k'+1))) (mul p3.[k] p1.[k]);
      lemma_plus_assoc #a (plus (mul p2.[k] p1.[k]) (mul (mul p2.[k+1] p1.[k+1]) (exp zeta (k'+1)))) (mul p3.[k] p1.[k]) (mul (mul p3.[k+1] p1.[k+1]) (exp zeta (k'+1)))
    end
    else begin
      lemma_distr_right #a p1.[k-1] p2.[k] p3.[k];
      lemma_distr_right #a p1.[k] p2.[k-1] p3.[k-1];
      lemma_plus_assoc #a (plus (mul p2.[k] p1.[k-1]) (mul p3.[k] p1.[k-1])) (mul p2.[k-1] p1.[k]) (mul p3.[k-1] p1.[k]);
      lemma_plus_assoc #a (mul p2.[k] p1.[k-1]) (mul p3.[k] p1.[k-1]) (mul p2.[k-1] p1.[k]);
      lemma_plus_swap #a (mul p3.[k] p1.[k-1]) (mul p2.[k-1] p1.[k]);
      lemma_plus_assoc #a (mul p2.[k] p1.[k-1]) (mul p2.[k-1] p1.[k]) (mul p3.[k] p1.[k-1]);
      lemma_plus_assoc #a (plus (mul p2.[k] p1.[k-1]) (mul p2.[k-1] p1.[k])) (mul p3.[k] p1.[k-1]) (mul p3.[k-1] p1.[k])
    end
  in FStar.Classical.forall_intro customlemma;
  eq_intro p23_1 p21_31;
  eq_elim p23_1 p21_31

let lib_ntt_ring #a [| ring a |] #n i zeta = (*: (#a:Type0) -> (#[tcresolve ()] r:ring a) -> (#n:size_nat{n%2=0}) -> (zeta:a{forall (x:a). mul x zeta == mul zeta x}) -> ring (lib_poly a n) =
  fun #a #r #n zeta -> *)
    {
      add_ag = lib_ntt_plus_abelian_group;
      mul_m = lib_ntt_mul_monoid #a i zeta;
      lemma_distr_left = lib_ntt_lemma_distr_left #a i zeta;
      lemma_distr_right = lib_ntt_lemma_distr_right #a i zeta;
    }

val lib_nttinv_mul:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat{n%2=0}
  -> i:size_nat{pow2 i = n/2}
  -> halfninv:a
  -> zeta:a//{forall (x:a). mul x zeta == mul zeta x}
  -> zetainv:a
  -> p1:lib_poly a n
  -> p2:lib_poly a n
  -> p:lib_poly a n

let lib_nttinv_mul #a [| ring a |] #n i halfninv zeta zetainv p1 p2 =
  lib_nttinv i halfninv zetainv (lib_ntt_mul i zeta (lib_ntt i zeta p1) (lib_ntt i zeta p2))

(* *************************************************************************** *) 

(*#reset-options "--z3rlimit 200 --max_fuel 2 --max_ifuel 2 --using_facts_from '* -FStar.Seq'"

val lib_nttinv_mul_lemma_keven_j:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat{n%2=0}
  -> halfninv:a
  -> zeta:a//{forall (x:a). mul x zeta == mul zeta x}
  -> zetainv:a
  -> p1:lib_poly a n
  -> p2:lib_poly a n
  -> k:nat{k<(n/2)}
  -> j:nat{j<(n/2)}
  -> Lemma (let pntt = lib_ntt_mul zeta (lib_ntt zeta p1) (lib_ntt zeta p2) in
           let pntteven,pnttodd = split_seq pntt in
	   let f (j:nat{j<n}) (g:a) : a = mul #a g (exp #a (exp #a zetainv 2) (k*j)) in
	   let s = mapi f pntteven in
	   s.[j] == mul #a pntt.[2*j] (exp zetainv (2*k*j))) //not the final lemma

#reset-options "--z3rlimit 1000 --max_fuel 2 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"// --debug Lib.Poly.NTT2 --debug_level Low --ugly"

let lib_nttinv_mul_lemma_keven_j #a [| ring a |] #n halfninv zeta zetainv p1 p2 k j =
  let _l2_lemma #a [| monoid a |] (l:lseq a 2) : Lemma (sum_n l == op #a l.[0] l.[1]) =
    sum_n_zero_elements_is_id (sub (sub l 1 1) 1 0);
    sum_n_simple_lemma1 (sub l 1 1);
    lemma_id2 #a (sub l 1 1).[0];
    sum_n_simple_lemma1 l
  in
  let m = add_ag.g.m in
  let p1ntt = lib_ntt zeta p1 in
  let p2ntt = lib_ntt zeta p2 in
  let pntt = lib_ntt_mul zeta p1ntt p2ntt in
  let pntteven,pnttodd = split_seq pntt in
  let f (j:nat{j<n}) (g:a) : a = mul #a g (exp #a (exp #a zetainv 2) (k*j)) in
  let s = mapi f pntteven in
  assert (s.[j] == mul #a pntteven.[j] (exp (exp zetainv 2) (k*j)));
  lemma_exp_exp zetainv 2 (k*j);
  assert (s.[j] == mul #a pntt.[2*j] (exp zetainv (2*(k*j))));
  assert (s.[j] == mul #a (plus #a (mul p1ntt.[2*j] p2ntt.[2*j]) (mul (mul p1ntt.[2*j+1] p2ntt.[2*j+1]) (exp zeta (2*j+1)))) (exp zetainv (2*(k*j))));
  lemma_distr_right #a (exp zetainv (2*(k*j))) (mul #a p1ntt.[2*j] p2ntt.[2*j]) (mul (mul p1ntt.[2*j+1] p2ntt.[2*j+1]) (exp zeta (2*j+1))); 
  lemma_mul_assoc #a (mul p1ntt.[2*j+1] p2ntt.[2*j+1]) (exp zeta (2*j+1)) (exp zetainv (2*(k*j)));
  assert (s.[j] == plus #a (mul (mul p1ntt.[2*j] p2ntt.[2*j]) (exp zetainv (2*(k*j)))) (mul (mul p1ntt.[2*j+1] p2ntt.[2*j+1]) (mul (exp zeta (2*j+1)) (exp zetainv (2*(k*j)))))); 
  let l2 = Seq.upd (Seq.upd (create 2 (zero #a)) 0 (mul #a (mul #a p1ntt.[2*j] p2ntt.[2*j]) (exp #a zetainv (2*(k*j))))) 1 (mul #a (mul #a p1ntt.[2*j+1] p2ntt.[2*j+1]) (mul #a (exp #a zeta (2*j+1)) (exp #a zetainv (2*(k*j))))) in
  let b (x:nat{x<n/2}) : Type0 = (y:nat{y<2}) in
  let customprop2 (x:nat{x<n/2}) (y: b x) : Type0 = (2*x+y < n) in
  let customlemma2 (x:nat{x<n/2}) (y:b x) : Lemma (customprop2 x y) =
    if (x=0) then assert(n>=2) else begin
      lemma_mult_le_left 2 x ((n/2)-1);
      distributivity_sub_right 2 (n/2) 1;
      euclidean_division_definition n 2;
      assert (2*x+y <= n -2 + y)
      end in
  FStar.Classical.forall_intro_2 customlemma2;
  assert(forall(x:nat{x<(n/2)}). (forall (y:nat{y<2}). 2*x+y < n));
  let g1 (x:nat{x<(n/2)}) (y:nat{y<2}) : a = plus #a (repeat_plus #a one ((y+1)%2)) (mul #a (repeat_plus #a one y) (exp #a zeta (2*x+1))) in
  let g2 (x:nat{x<(n/2)}) (y:nat{y<2}) = mul #a (g1 x y) (exp #a zetainv (2*(k*x))) in
  let g (x:nat{x<(n/2)}) (y:nat{y<2}) = mul #a (mul #a p1ntt.[2*x+y] p2ntt.[2*x+y]) (g2 x y) in
  //let g (x:nat{x<(n/2)}) (y:nat{y<2}) = mul #a (mul #a p1ntt.[2*x+y] p2ntt.[2*x+y]) (mul #a (plus #a (repeat_plus #a one ((y+1)%2)) (mul #a (repeat_plus #a one y) (exp #a zeta (2*x+1)))) (exp #a zetainv (2*(k*x)))) in admit()
  lemma_repeat_op_zero #a #m (one #a);
  lemma_zero_absorb1 (exp zeta (2*j+1));
  lemma_repeat_op_succ1 #a one 0;
  lemma_zero2 #a one;
  lemma_one1 (exp zetainv (2*(k*j)));

  lemma_one1 (exp zeta (2*j+1));
  lemma_zero1 (exp zeta (2*j+1));
  assert (l2.[0] == g j 0);
  assert (l2.[1] == g j 1);
  assert (s.[j] == plus #a l2.[0] l2.[1]);
  _l2_lemma l2;
  assert(s.[j] == sum_n l2); admit()


val lib_nttinv_mul_lemma_keven:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat{n%2=0}
  -> halfninv:a
  -> zeta:a//{forall (x:a). mul x zeta == mul zeta x}
  -> zetainv:a
  -> p1:lib_poly a n
  -> p2:lib_poly a n
  -> k:nat{k<(n/2)}
  -> Lemma (True)

#reset-options "--z3rlimit 300 --max_fuel 0 --max_ifuel 2 --using_facts_from '* -FStar.Seq'"

let lib_nttinv_mul_lemma_keven #a [| ring a |] #n halfninv zeta zetainv p1 p2 k =
  let m = add_ag.g.m in
  let p1ntt = lib_ntt zeta p1 in
  let p2ntt = lib_ntt zeta p2 in
  let pntt = lib_ntt_mul zeta p1ntt p2ntt in
  let pntteven,pnttodd = split_seq pntt in
  let p = lib_nttinv halfninv zetainv pntt in
  let peven,podd = split_seq p in
  let s :lib_poly a (n/2) = (mapi (fun j g -> mul #a g (exp (exp zetainv 2) (k*j))) pntteven) in
  lemma_join_split (Lib.Poly.NTT.lib_nttinv halfninv (exp zetainv 2) zetainv pntteven) (Lib.Poly.NTT.lib_nttinv halfninv (exp zetainv 2) zetainv pnttodd);
  Lib.Poly.NTT.lib_nttinv_lemma_instantiate halfninv (exp zetainv 2) zetainv pntteven peven k;
  
  assert(p.[2*k] == mul #a halfninv (mul (exp zetainv k) (sum_n #a #add_ag.g.m s)));
  let customprop (j:nat{j<(n/2)}) : Type0 = (s.[j] == s.[j]) in
  let customlemma (j:nat{j<(n/2)}) : Lemma (customprop p) =
    lib_nttinv_mul_lemma_keven_j halfninv zeta zetainv p1 p2 k j
  in FStar.Classical.forall_intro customlemma

assume val lib_nttinv_mul_lemma_kodd:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat{n%2=0}
  -> halfninv:a
  -> zeta:a//{forall (x:a). mul x zeta == mul zeta x}
  -> zetainv:a
  -> p1:lib_poly a n
  -> p2:lib_poly a n
  -> k:nat{k<(n/2)}
  -> Lemma (True)

val lib_nttinv_mul_lemma:
  #a:Type0
  -> #[tcresolve ()] r:ring a
  -> #n:size_nat{n%2=0}
  -> halfninv:a
  -> zeta:a//{forall (x:a). mul x zeta == mul zeta x}
  -> zetainv:a
  -> p1:lib_poly a n
  -> p2:lib_poly a n
  -> Lemma (True)

let lib_nttinv_mul_lemma #a [| ring a |] #n halfninv zeta zetainv p1 p2 =
  let p1ntt = lib_ntt zeta p1 in
  let p2ntt = lib_ntt zeta p2 in
  let pntt = lib_ntt_mul zeta p1ntt p2ntt in
  let p = lib_nttinv halfninv zetainv pntt in
  let customprop (k:nat{k<n}) : Type0 = (True) in
  let customlemma (k:nat{k<n}) : Lemma (customprop k) =
  if(k%2=0) then
    lib_nttinv_mul_lemma_keven halfninv zeta zetainv p1 p2 (k/2)
  else 
    lib_nttinv_mul_lemma_kodd halfninv zeta zetainv p1 p2 (k/2)
  in
  FStar.Classical.forall_intro customlemma
