module Hacl.Spec.EC.Point

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Limb


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 5"

module U32 = FStar.UInt32

let spoint = seqelem * seqelem


let sgetx (p:spoint) = fst p
let sgety (p:spoint) = fst p
let sgetz (p:spoint) = snd p

val smake: seqelem -> seqelem -> Tot spoint
let smake a b = a, b

type s_513 = s:seqelem{Hacl.Spec.EC.AddAndDouble.red_513 s}


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 50"

val lemma_xor: #n:pos -> a:UInt.uint_t n -> b:UInt.uint_t n -> Lemma
  (UInt.logxor a (UInt.logxor a b) = b /\ UInt.logxor a (UInt.logxor b a) = b
    /\ UInt.logxor a (UInt.zero n) = a)
let lemma_xor #n a b =
  UInt.logxor_associative a a b;
  UInt.logxor_commutative a b;
  UInt.logxor_commutative (UInt.zero n) b;
  UInt.logxor_self a;
  UInt.logxor_lemma_1 a;
  UInt.logxor_lemma_1 b

val lemma_and: #n:pos -> a:UInt.uint_t n -> Lemma (UInt.logand (UInt.ones n) a = a /\ UInt.logand (UInt.zero n) a = UInt.zero n)
let lemma_and #n a =
  UInt.logand_lemma_1 #n a;
  UInt.logand_lemma_2 #n a;
  UInt.logand_commutative #n a (UInt.zero n); 
  UInt.logand_commutative #n a (UInt.ones n)


val swap_conditional_step_spec: x:s_513 -> y:s_513 -> l:limb{v l = pow2 64 - 1 \/ v l = 0} -> ctr:U32.t{U32.v ctr <= len /\ U32.v ctr > 0} -> Tot (t:(s_513 * s_513){
    let x' = fst t in let y' = snd t in
    (forall (i:nat). {:pattern (Seq.index x' i) \/ (Seq.index y' i)} (i < Seq.length x /\ i <> U32.v ctr - 1) ==>
      Seq.index x' i == Seq.index x i /\ Seq.index y' i == Seq.index y i)
    /\ (v l = pow2 64 - 1 ==> (Seq.index x' (U32.v ctr-1) == Seq.index y (U32.v ctr - 1)
                             /\ Seq.index y' (U32.v ctr - 1) == Seq.index x (U32.v ctr - 1)))
    /\ (v l = 0           ==> (Seq.index x' (U32.v ctr-1) == Seq.index x (U32.v ctr - 1)
                             /\ Seq.index y' (U32.v ctr - 1) == Seq.index y (U32.v ctr - 1)))
  })
let swap_conditional_step_spec a b swap ctr =
  let i = U32.(ctr -^ 1ul) in
  let i' = U32.v i in
  let ai = Seq.index a i' in
  let bi = Seq.index b i' in
  let x = swap &^ (ai ^^ bi) in
  lemma_and (v (ai ^^ bi));
  cut (v x = v (ai ^^ bi) \/ v x = 0);
  lemma_xor (v ai) (v bi);
  lemma_xor (v bi) (v ai);  
  let ai' = ai ^^ x in
  let bi' = bi ^^ x in
  cut (v ai' = v bi \/ v ai' = v ai);
  cut (v bi' = v ai \/ v bi' = v bi);
  let a' = Seq.upd a i' ai' in
  let b' = Seq.upd b i' bi' in
  a', b'


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val swap_conditional_spec_:
  x:s_513 -> y:s_513 -> l:limb{v l = pow2 64 - 1 \/ v l = 0} ->
  ctr:U32.t{U32.v ctr <= len} ->
  GTot (t:(s_513 * s_513){
    let x' = fst t in let y' = snd t in let ctr = U32.v ctr in
     (v l = pow2 64 - 1 ==> (forall (i:nat). (i < ctr) ==>
      (Seq.index x' i == Seq.index y i /\ Seq.index y' i == Seq.index x i)))
     /\ (v l = pow2 64 - 1 ==> (forall (i:nat). (i >= ctr /\ i < Seq.length x) ==>
      (Seq.index x' i == Seq.index x i /\ Seq.index y' i == Seq.index y i)))
    /\ (v l = 0 ==> (x' == x /\ y' == y))
  }) (decreases (U32.v ctr))
let rec swap_conditional_spec_ a b swap ctr =
  if U32.(ctr =^ 0ul) then (a,b)
  else (
    let a', b' = swap_conditional_step_spec a b swap ctr in
    if v swap = 0 then (Seq.lemma_eq_intro a a'; Seq.lemma_eq_intro b b');
    let i = U32.(ctr -^ 1ul) in
    let a'', b'' = swap_conditional_spec_ a' b' swap i in
    a'', b''
  )


type spoint_513 = p:spoint{Hacl.Spec.EC.AddAndDouble.red_513 (fst p)
  /\ Hacl.Spec.EC.AddAndDouble.red_513 (snd p)}

val swap_conditional_spec: a:spoint_513 -> b:spoint_513 -> bit:limb{v bit = 1 \/ v bit = 0} ->
  GTot (t:(spoint_513 * spoint_513){
    let a' = fst t in let b' = snd t in
    (v bit = 1 ==> a' == b /\ b' == a)
    /\ (v bit = 0 ==> a' == a /\ b' == b)
  })
let swap_conditional_spec a b mask =
  let mask = limb_zero -%^ mask in
  assert_norm((0 - 1) % pow2 64 = pow2 64 - 1);
  assert_norm((0 - 0) % pow2 64 = 0);
  let ax, bx = swap_conditional_spec_ (sgetx a) (sgetx b) mask clen in
  let az, bz = swap_conditional_spec_ (sgetz a) (sgetz b) mask clen in
  if v mask = 0 then (
    Seq.lemma_eq_intro (fst a) ax;
    Seq.lemma_eq_intro (snd a) az;
    Seq.lemma_eq_intro (fst b) bx;
    Seq.lemma_eq_intro (snd b) bz
  ) else (
    Seq.lemma_eq_intro (fst a) bx;
    Seq.lemma_eq_intro (snd a) bz;
    Seq.lemma_eq_intro (fst b) ax;
    Seq.lemma_eq_intro (snd b) az
  );
  ((ax, az), (bx, bz))
