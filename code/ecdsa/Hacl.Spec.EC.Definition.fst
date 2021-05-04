module Hacl.Spec.EC.Definition

open Lib.IntTypes
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.Sequence
open FStar.Mul

open Spec.ECC.Curves

#set-options " --z3rlimit 200"

noextract
let point_seq (c: curve) = lseq uint64 (uint_v (getCoordinateLenU64 c) * 3)

noextract
let felem_seq (c: curve) = lseq uint64 (uint_v (getCoordinateLenU64 c))


noextract 
val lseq_as_nat_: #l: size_nat -> #t:inttype{unsigned t} -> a: lseq (uint_t t SEC) l -> i: nat {i <= Lib.Sequence.length a} -> Tot nat

let rec lseq_as_nat_ #l #t a i = 
  if i = 0 then 0 else
  let a_i_1 = Lib.Sequence.index a (i - 1) in
  lseq_as_nat_ a (i - 1) + pow2 (bits t * (i - 1)) * v a_i_1

noextract 
val lseq_as_nat: #l: size_nat -> #t:inttype{unsigned t} -> a: lseq (uint_t t SEC) l -> Tot nat

let lseq_as_nat #l a = lseq_as_nat_ a l


val lseq_as_nat_last: #l: size_nat -> a: lseq uint64 l -> Lemma (lseq_as_nat_ #l a 0 == 0)

let lseq_as_nat_last #l a = ()

val lseq_as_nat_first: #l: size_nat -> a: lseq uint64 l {l > 0} -> Lemma (lseq_as_nat_ a 1 == v (Lib.Sequence.index a 0))

let lseq_as_nat_first a = ()




val lseq_as_nat_definiton: #len:size_nat -> a: lseq uint64 len -> i: nat {i > 0 /\ i <= len} ->
  Lemma (lseq_as_nat_ #len a i == lseq_as_nat_ a (i - 1) + pow2 (64 * (i - 1)) * v (Lib.Sequence.index a (i - 1)))

let lseq_as_nat_definiton #len b i = ()


val lemma_equal_lseq_equal_nat: #len: size_nat -> a: lseq uint64 len -> b: lseq uint64 len -> 
  Lemma (a == b ==> lseq_as_nat a == lseq_as_nat b)

let lemma_equal_lseq_equal_nat #len a b = ()


val lemma_create_: #l: size_nat -> i: nat {i > 0 /\ i <= l} -> Lemma (let a = Seq.create l (u64 0) in lseq_as_nat_ #l a i == 0)

let rec lemma_create_ #l i = 
  let a = Seq.create l (u64 0) in 
  match i with 
  |1 -> 
    lseq_as_nat_definiton #l a 1
  |_ -> 
    lemma_create_ #l (i - 1);
    lseq_as_nat_definiton #l a i


val lemma_create_zero_buffer: len: size_nat {len > 0} -> c: curve -> Lemma (lseq_as_nat #len (Seq.create len (u64 0)) == 0)

let lemma_create_zero_buffer len c = lemma_create_ #len len


val lemma_lseq_as_seq_as_forall: #l: size_nat -> a: lseq uint64 l -> b: lseq uint64 l -> i: nat {i >= 0 /\ i <= l} ->
  Lemma ((forall (k: nat). k <= (i - 1) ==> Lib.Sequence.index a k == Lib.Sequence.index b k) ==>
    (lseq_as_nat_ #l a i == lseq_as_nat_ #l b i))

let rec lemma_lseq_as_seq_as_forall #l a b i = 
  match i with 
  |0 -> lseq_as_nat_last a; lseq_as_nat_last b
  |_ -> 
    lemma_lseq_as_seq_as_forall a b (i - 1);
    lseq_as_nat_definiton a i;
    lseq_as_nat_definiton b i
    

val lemma_lseq_1: l: size_nat -> a: lseq uint64 l -> i: nat {i > 0 /\ i <= l} ->
  Lemma (lseq_as_nat_ a i % pow2 64 == v (Lib.Sequence.index a 0))

let rec lemma_lseq_1 l a i = 
  match i with 
  |1 -> ()
  |_ -> lemma_lseq_1 l a (i - 1);
    lseq_as_nat_definiton a i;
    FStar.Math.Lemmas.lemma_mod_add_distr (lseq_as_nat_ a (i - 1)) (pow2 (64 * (i - 1)) * v (Lib.Sequence.index a (i - 1))) (pow2 64);
    FStar.Math.Lemmas.pow2_multiplication_modulo_lemma_1 (v (Lib.Sequence.index a (i - 1))) 64 (64 * (i - 1))  


val lemma_lseq_as_seq_extension: 
  #l0: size_nat ->  #l1: size_nat -> 
  a0: lseq uint64 l0 -> a1: lseq uint64 l1 -> 
  i: nat {i <= l0 /\ i <= l1} ->
  Lemma 
    (requires (Lib.Sequence.sub a0 0 i == Lib.Sequence.sub a1 0 i))
    (ensures lseq_as_nat_ a0 i == lseq_as_nat_ a1 i)

let rec lemma_lseq_as_seq_extension #l0 #l1 a0 a1 i = 
  match i with 
  | 0 -> ()
  | _ -> 
    assert(forall (k: nat {k < i}). Lib.Sequence.index (Lib.Sequence.sub a1 0 i) k == Lib.Sequence.index a0 k);
    assert(forall (k: nat {k < i}). Lib.Sequence.index (Lib.Sequence.sub a0 0 i) k == Lib.Sequence.index a0 k);
    
    eq_intro (Lib.Sequence.sub a0 0 (i - 1)) (Lib.Sequence.sub a1 0 (i - 1));
    assert(Lib.Sequence.sub a0 0 (i - 1) == Lib.Sequence.sub a1 0 (i - 1));
    
    lemma_lseq_as_seq_extension a0 a1 (i - 1);

    lseq_as_nat_definiton a0 i;
    lseq_as_nat_definiton a1 i;

    assert(forall (k: nat {k < i}). Lib.Sequence.index a0 k == Lib.Sequence.index a1 k);
    assert (Lib.Sequence.index a0 (i - 1) == Lib.Sequence.index a1 (i - 1))


val lseq_upperbound_: #len:size_nat -> a: lseq uint64 len -> i: nat {i >= 0 /\ i <= len} -> Lemma (lseq_as_nat_ a i < pow2 (64 * i))

let rec lseq_upperbound_ #len a i = 
  match i with 
  |0 -> ()
  |_ -> lseq_upperbound_ a (i - 1); 
    lseq_as_nat_definiton a i;
    FStar.Math.Lemmas.pow2_plus 64 (64 * (i - 1))

val lseq_upperbound: #l: size_nat -> a: lseq uint64 l -> Lemma (lseq_as_nat a < pow2 (64 * l))

let lseq_upperbound #l a = lseq_upperbound_  a l


val lseq_upperbound2: #l: size_nat -> a: lseq uint64 l -> i: nat {i >= 0 /\ i <= l} -> 
  Lemma (lseq_as_nat_ a (l - i) <= lseq_as_nat a)

let rec lseq_upperbound2 #l a i = 
  match i with 
  |0 -> ()
  |_ -> lseq_upperbound2 #l a (i - 1); lseq_as_nat_definiton a (l - 1 + 1)


val lseq_upperbound1: #l: size_nat -> a: lseq uint64 l -> i: nat {i > 0 /\ i < l} -> k: nat{k >= 0 && k <= l - i} -> Lemma 
  (requires lseq_as_nat a < pow2 (64 * i))
  (ensures lseq_as_nat_ a i == lseq_as_nat_ a (i + k))

let rec lseq_upperbound1 #l a i k = 
  match k with 
  |0 -> ()
  |_ -> lseq_upperbound1 #l a i (k - 1);
    lseq_as_nat_definiton a (i + 1); 
    lseq_upperbound2 a (l - i - k);
    if (v (Lib.Sequence.index a (i + k - 1)) >= 1) then begin
      assert(pow2 (64 * (i + k - 1)) <= pow2 (64 * (i + k - 1)) * v (Lib.Sequence.index a (i + k - 1)));
      assert((64 * i) <= 64 * (i + k - 1));
      FStar.Math.Lemmas.pow2_le_compat (64 * (i + k - 1)) (64 * i);
      assert(False)
  end


val lemma_lseq_as_seq_as_forall_r_: #l: size_nat -> a: lseq uint64 l -> b: lseq uint64 l -> i: nat {i >= 1 /\ i <= l} -> 
  Lemma (requires lseq_as_nat_ a i == lseq_as_nat_ #l b i)
  (ensures lseq_as_nat_ a (i - 1) == lseq_as_nat_ #l b (i - 1))

let lemma_lseq_as_seq_as_forall_r_ #l a b i = 
  lseq_as_nat_definiton a i;
  lseq_as_nat_definiton b i;
  
  lseq_upperbound_ a (i - 1);
  lseq_upperbound_ b (i - 1);

  let ai = v (Lib.Sequence.index a (i - 1)) in 
  let bi = v (Lib.Sequence.index b (i - 1)) in 

  FStar.Math.Lemmas.lemma_mod_plus (lseq_as_nat_ a (i - 1)) ai (pow2 (64 * (i - 1)));
  FStar.Math.Lemmas.lemma_mod_plus (lseq_as_nat_ b (i - 1)) bi (pow2 (64 * (i - 1)));

  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 

  assert_by_tactic (ai * pow2 (64 * (i - 1)) == pow2 (64 * (i - 1)) * ai) canon;
  assert_by_tactic (bi * pow2 (64 * (i - 1)) == pow2 (64 * (i - 1)) * bi) canon;

  FStar.Math.Lemmas.small_mod (lseq_as_nat_ a (i - 1)) (pow2 (64 * (i - 1)));
  FStar.Math.Lemmas.small_mod (lseq_as_nat_ b (i - 1)) (pow2 (64 * (i - 1)))


val lemma_lseq_as_seq_as_forall_r: #l: size_nat -> a: lseq uint64 l -> b: lseq uint64 l -> i: nat {i >= 0 /\ i <= l} ->
  Lemma ((lseq_as_nat_ #l a i == lseq_as_nat_ #l b i) ==> (forall (k: nat). k <= (i - 1) ==> Lib.Sequence.index a k == Lib.Sequence.index b k))

let rec lemma_lseq_as_seq_as_forall_r #l a b i = 
  match i with 
  |0 -> ()
  |_ -> lemma_lseq_as_seq_as_forall_r #l a b (i - 1);
    let i_1 = i - 1 in 
    lseq_as_nat_definiton a i;
    lseq_as_nat_definiton b i;
    if lseq_as_nat_ a i = lseq_as_nat_ b i then
      lemma_lseq_as_seq_as_forall_r_ a b i


val lemma_lseq_as_seq_as_forall_lr: #l: size_nat -> a: lseq uint64 l -> b: lseq uint64 l -> i: nat {i >= 0 /\ i <= l} -> 
  Lemma ((lseq_as_nat_ #l a i == lseq_as_nat_ #l b i) <==> (forall (k: nat). k <= (i - 1) ==> Lib.Sequence.index a k == Lib.Sequence.index b k))

let lemma_lseq_as_seq_as_forall_lr #l a b i = 
  lemma_lseq_as_seq_as_forall #l a b i;
  lemma_lseq_as_seq_as_forall_r #l a b i


val lseq_as_nat_zero_l: #l: size_nat -> a: lseq uint64 l -> i: nat {i >= 0 /\ i <= l} -> Lemma 
  (lseq_as_nat_ a i == 0 ==> (forall (j: nat {j < i}). v (Lib.Sequence.index a j) == 0))

let rec lseq_as_nat_zero_l #l a i = 
  match i with 
  |0 -> ()
  |_ -> lseq_as_nat_zero_l #l a (i - 1); lseq_as_nat_definiton a i


val lseq_as_nat_zero_r: #l: size_nat -> a: lseq uint64 l -> i: nat {i >= 0 /\ i <= l} -> Lemma 
  ((forall (j: nat {j < i}). v (Lib.Sequence.index a j) == 0) ==> lseq_as_nat_ a i == 0)

let rec lseq_as_nat_zero_r #l a i = 
  match i with 
  |0 -> ()
  |_ -> lseq_as_nat_zero_r #l a (i - 1); lseq_as_nat_definiton a i


val lseq_as_nat_zero: #l: size_nat -> a: lseq uint64 l -> Lemma 
  (lseq_as_nat_ a l == 0 <==> (forall (j: nat {j < l}). v (Lib.Sequence.index a j) == 0))

let lseq_as_nat_zero #l a = 
  lseq_as_nat_zero_l #l a l;
  lseq_as_nat_zero_r #l a l


val lemma_test: #l: size_nat -> a: lseq uint64 l -> i: nat {i <= l} 
  -> Lemma (ensures (
    let a0 = sub a 0 i in 
    let a1 = sub a i (l - i) in 
    lseq_as_nat a = lseq_as_nat a0 + pow2 (64 * i) * lseq_as_nat a1))
    (decreases (l - i))

let rec lemma_test #l a i = 
  if i = 0 then begin 
    let a0 = sub a 0 0 in 
    let a1 = sub a 0 l in 
    lseq_as_nat_last a0
    end
  else begin if i = l then lseq_as_nat_last (sub a l 0) else
    begin 
      let a0 = sub a 0 i in 
      let a1 = sub a i (l - i) in 

      calc (==) 
      {
  lseq_as_nat a1;
  (==) {lemma_test #(l - i) a1 1}
  lseq_as_nat (sub a1 0 1) + pow2 64 * lseq_as_nat (sub a1 1 (l - i - 1));
  (==) {lseq_as_nat_first (sub a1 0 1)}
  v (index a1 0) + pow2 64 * lseq_as_nat (sub a1 1 (l - i - 1));
  (==) {Seq.lemma_index_slice a 0 (i + 1) i}
  v (index a i) + pow2 64 * lseq_as_nat (sub a (i + 1) (l - (i + 1)));
      };
    
    assert(lseq_as_nat a1 - v (index a i) =  pow2 64 * lseq_as_nat (sub a (i + 1) (l - (i + 1))));

    lemma_lseq_as_seq_extension (sub a 0 (i + 1)) (sub a 0 i) i;

    let open FStar.Tactics in 
    let open FStar.Tactics.Canon in 

    
    calc (==) {
      lseq_as_nat a;
      (==) {lemma_test a (i + 1)}
      lseq_as_nat (sub a 0 (i + 1)) + pow2 (64 * (i + 1)) * lseq_as_nat (sub a (i + 1) (l - (i + 1)));
      (==) {FStar.Math.Lemmas.pow2_plus (64 * i) 64}
      lseq_as_nat (sub a 0 (i + 1)) + pow2 (64 * i) * pow2 64 * lseq_as_nat (sub a (i + 1) (l - (i + 1)));
      (==) {assert_by_tactic (pow2 (64 * i) * pow2 64 * lseq_as_nat (sub a  (i + 1) (l - (i + 1))) == 
  pow2 (64 * i) * (pow2 64 * lseq_as_nat (sub a (i + 1) (l - (i + 1))))) canon}
      lseq_as_nat (sub a 0 (i + 1)) + pow2 (64 * i) * (pow2 64 * lseq_as_nat (sub a (i + 1) (l - (i + 1))));
      (==) {assert(lseq_as_nat a1 - v (index a i) =  pow2 64 * lseq_as_nat (sub a (i + 1) (l - (i + 1))))}
      lseq_as_nat (sub a 0 (i + 1)) - pow2 (64 * i) * v (index a i) + pow2 (64 * i) * lseq_as_nat a1; 
      (==) {assert (lseq_as_nat (sub a 0 (i + 1)) == lseq_as_nat (sub a 0 i) + pow2 (64 * i) * v (index a i))}
      lseq_as_nat (sub a 0 i) + pow2 (64 * i) * lseq_as_nat a1;}
    end end


val lemma_lseq_as_bn_v_: #l: size_nat -> a: Lib.Sequence.lseq uint64 l -> i: nat{i <= l} ->
  Lemma (lseq_as_nat_ #l a i == Hacl.Spec.Bignum.Definitions.eval_ l a i) 

let rec lemma_lseq_as_bn_v_ #l a i = 
  match i with 
  |0 -> ()
  |_ -> lemma_lseq_as_bn_v_ #l a (i - 1)


val lemma_lseq_as_bn_v: #l: size_nat -> a: Lib.Sequence.lseq uint64 l -> 
  Lemma (lseq_as_nat #l a == Hacl.Spec.Bignum.Definitions.bn_v #l a) 
  [SMTPat (Hacl.Spec.Bignum.Definitions.bn_v #l a)]

let lemma_lseq_as_bn_v #l a =  
  lemma_lseq_as_bn_v_ #l a l



open Lib.Buffer

inline_for_extraction
let felem (c: curve) = lbuffer uint64 (getCoordinateLenU64 c)

inline_for_extraction 
let widefelem (c: curve) = lbuffer uint64 (getCoordinateLenU64 c *! 2ul)

noextract
let felem_seq_as_nat (c: curve) (a: felem_seq c) : Tot nat = lseq_as_nat a


noextract
let as_nat (c: curve) (h:mem) (e:felem c) : GTot nat = lseq_as_nat (as_seq h e)

noextract
let as_nat_il (c: curve) (h:mem) (e:glbuffer uint64 (getCoordinateLenU64 c)) : GTot nat =
  lseq_as_nat (as_seq h e)


noextract
let wide_as_nat (c: curve) (h:mem) (e: widefelem c) : GTot nat = lseq_as_nat (as_seq h e)


inline_for_extraction
type point (c: curve) = lbuffer uint64 (getCoordinateLenU64 c *! 3ul)

inline_for_extraction
type pointAffine (c: curve) = lbuffer uint64 (getCoordinateLenU64 c *! 2ul)


inline_for_extraction
type coordinateAffine8 (c: curve) = lbuffer uint8 (getCoordinateLenU c)

inline_for_extraction
type pointAffine8 (c: curve) = lbuffer uint8 (2ul *! getCoordinateLenU c)


type scalar_t (#t: buftype) (#c: curve)  = lbuffer_t t uint8 (getScalarLenBytes c)


let felem_eval (c: curve) (h: mem) (f: felem c) = as_nat c h f < getPrime c


val getX: #c: curve -> p: point c -> GTot (felem c)

let getX #c p = gsub p (size 0) (getCoordinateLenU64 c)

val getY: #c: curve -> p: point c -> GTot (felem c)

let getY #c p = gsub p (getCoordinateLenU64 c) (getCoordinateLenU64 c)

val getZ: #c: curve -> p: point c -> GTot (felem c)

let getZ #c p = gsub p (size 2 *! getCoordinateLenU64 c) (getCoordinateLenU64 c)


val getXAff: #c: curve -> p: pointAffine c -> GTot (felem c)

let getXAff #c p = gsub p (size 0) (getCoordinateLenU64 c)

val getYAff: #c: curve -> p: pointAffine c  -> GTot (felem c)

let getYAff #c p = gsub p (getCoordinateLenU64 c) (getCoordinateLenU64 c)


val getXAff8: #c: curve -> p: pointAffine8 c -> GTot (coordinateAffine8 c)

let getXAff8 #c p = gsub p (size 0) (getCoordinateLenU c)

val getYAff8: #c: curve -> p: pointAffine8 c -> GTot (coordinateAffine8 c)

let getYAff8 #c p = gsub p (getCoordinateLenU c) (getCoordinateLenU c)



let point_eval (c: curve) (h:mem) (p:point c) = 
  let x, y, z = getX p, getY p, getZ p in 
  felem_eval c h x /\ felem_eval c h y /\ felem_eval c h z 
  

noextract 
let point_x_as_nat (c: curve) (h: mem) (e: point c {point_eval c h e}) : GTot (a: nat {a < getPrime c}) = 
  as_nat c h (getX e)

noextract 
let point_y_as_nat (c: curve) (h: mem) (e: point c {point_eval c h e}) : GTot (a: nat {a < getPrime c}) = 
  as_nat c h (getY e)

noextract 
let point_z_as_nat (c: curve) (h: mem) (e: point c {point_eval c h e}) : GTot (a: nat {a < getPrime c}) = 
  as_nat c h (getZ e)


noextract
let point_as_nat (c: curve) (h: mem) (e: point c {point_eval c h e}) : GTot (point_nat_prime #c) = 
  point_x_as_nat c h e, point_y_as_nat c h e, point_z_as_nat c h e

let point_prime_to_coordinates (c: curve) (p:point_seq c) : GTot point_nat =
  let len = uint_v (getCoordinateLenU64 c) in 
  lseq_as_nat (Lib.Sequence.sub p 0 len),
  lseq_as_nat (Lib.Sequence.sub p len len),
  lseq_as_nat (Lib.Sequence.sub p (len * 2) len)
  
