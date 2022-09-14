module Hacl.Impl.EC.ScalarMultiplication.WNAF.Lemmas

open FStar.HyperStack.All
open FStar.HyperStack

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Spec.ECC.Curves
open Spec.ECC
open Spec.ECC.WNAF

open Hacl.Impl.EC.LowLevel
open Hacl.Spec.EC.Definition

open Hacl.Spec.MontgomeryMultiplication

open FStar.Mul

open FStar.Math.Lemmas


#set-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
let radix: (r: uint64 {v r == w}) = u64 5

inline_for_extraction noextract
let radix_shiftval: (r: shiftval U64 {v r == w /\ v r == v radix}) = size 5

inline_for_extraction noextract
let radix_u32: (r: size_t {v r == w /\ v r == v radix}) = size 5

inline_for_extraction noextract
let dradix : (r: uint64 {v r == m}) = assert_norm(pow2 5 == 32); u64 32

inline_for_extraction noextract
let dradix_wnaf : (r: uint64 {v r == 2 * m}) = 
  FStar.Math.Lemmas.pow2_double_sum 5; 
  assert_norm (pow2 6 == 64);
  u64 64


val getLenWnaf: #c: curve -> Tot (r: size_t {v r == v (getScalarLen c) / w})

let getLenWnaf #c = 
  match c with
  |P256 -> 
    assert (v (getScalarLen P256) / 5 == 51);
    size 51
  |P384 ->
    assert (v (getScalarLen P384) / 5 == 76);
    size 76


val rnaf_to_step__: #c: curve 
  -> rnaf: Lib.Sequence.lseq uint64 (2 * (v (getScalarLen c) / w + 1)) 
  -> r: Lib.Sequence.seq int {Lib.Sequence.length r == v (getLenWnaf #c) + 1} 
  -> i: nat {i < Seq.length r /\ (
   forall (j: nat {j < i}). 
      let ri = Lib.Sequence.index rnaf (2 * j) in 
      let sign = Lib.Sequence.index rnaf (2 * j + 1) in 
      if v sign = 0 then 
	Seq.index r j == v ri
      else 
	Seq.index r j == - (v ri))} -> 
  Tot (r: Seq.seq int {Lib.Sequence.length r == v (getLenWnaf #c) + 1 /\ (
    forall (j: nat {j <= i}). 
      let ri = Lib.Sequence.index rnaf (2 * j) in 
      let sign = Lib.Sequence.index rnaf (2 * j + 1) in 
      if v sign = 0 then 
	Seq.index r j == v ri
      else 
	Seq.index  r j == - (v ri))})

let rnaf_to_step__ #c rnaf r i = 
  let ri = Seq.index rnaf (2 * i) in 
  let sign = Seq.index rnaf (2 * i + 1) in 

  if v sign = 0 then 
    Seq.upd r i (v ri)
  else 
    Seq.upd r i (- (v ri))


val rnaf_to_step_: #c: curve 
  -> rnaf: Lib.Sequence.lseq uint64 (2 * (v (getScalarLen c) / w + 1)) 
  -> r: Lib.Sequence.seq int {Lib.Sequence.length r == v (getLenWnaf #c) + 1} 
  -> i: nat {i <= Seq.length r /\ (
    if i < Seq.length r then 
     begin
       forall (j: nat {j < i}). 
	 let ri = Lib.Sequence.index rnaf (2 * j) in 
	 let sign = Lib.Sequence.index rnaf (2 * j + 1) in 
	 if v sign = 0 then 
	   Lib.Sequence.index #_ #(v (getLenWnaf #c) + 1) r j == v ri
	 else 
	   Lib.Sequence.index #_ #(v (getLenWnaf #c) + 1) r j == - (v ri) end
     else
       begin
	 forall (j: nat {j < i}). 
	   let ri = Lib.Sequence.index rnaf (2 * j) in 
	   let sign = Lib.Sequence.index rnaf (2 * j + 1) in 
	   if v sign = 0 then 
	     Lib.Sequence.index #_ #(v (getLenWnaf #c) + 1) r j == v ri
	   else 
	     Lib.Sequence.index #_ #(v (getLenWnaf #c) + 1) r j == - (v ri) end)} ->
  Tot (r: Lib.Sequence.seq int {Lib.Sequence.length r == v (getLenWnaf #c) + 1 /\ (
    forall (j: nat {j < Seq.length r}). 
    let ri = Lib.Sequence.index rnaf (2 * j) in 
    let sign = Lib.Sequence.index rnaf (2 * j + 1) in 
    if v sign = 0 then 
      Lib.Sequence.index #_ #(v (getLenWnaf #c) + 1) r j == v ri
    else 
      Lib.Sequence.index #_ #(v (getLenWnaf #c) + 1) r j == - (v ri))})
  (decreases Seq.length r - i)
  
let rec rnaf_to_step_ #c rnaf r i = 
  if i = Seq.length r then 
    r
  else
    let r = rnaf_to_step__ #c rnaf r i in 
    rnaf_to_step_ #c rnaf r (i + 1)


let rnaf_to_spec (#c: curve) (rnaf: Lib.Sequence.lseq uint64  (2 * (v (getScalarLen c) / w + 1))) : (
  r: Lib.Sequence.seq int {
    Lib.Sequence.length r == v (getLenWnaf #c) + 1 /\ (
    forall (i: nat {i < Seq.length r}). 
      let ri = Lib.Sequence.index rnaf (2 * i) in 
      let sign = Lib.Sequence.index rnaf (2 * i + 1) in 
      if v sign = 0 then 
	Lib.Sequence.index #_ #(v (getLenWnaf #c) + 1) r i == v ri
      else 
	Lib.Sequence.index #_ #(v (getLenWnaf #c) + 1) r i == - (v ri) )}) = 
  let s = Seq.Base.create (v (getLenWnaf #c) + 1) 0 in
  rnaf_to_step_ #c rnaf s 0


val scalar_compute_window_lemma_lemma_powers: unit -> Lemma (
  pow2 2 * 2 == pow2 3 /\
  pow2 3 * 2 == pow2 4 /\
  pow2 4 * 2 == pow2 5 /\
  pow2 5 * 2 == pow2 6)

let scalar_compute_window_lemma_lemma_powers () = 
  pow2_double_sum 2;
  pow2_double_sum 3;
  pow2_double_sum 4;
  pow2_double_sum 5


val scalar_compute_window_lemma_less: 
  sh0: nat {sh0 <= 1} -> sh1: nat {sh1 <= 1} -> sh2: nat {sh2 <= 1} -> sh3: nat {sh3 <= 1} -> sh4: nat {sh4 <= 1} -> 
  Lemma (sh0 * pow2 1 + 
    sh1 * pow2 2 +
    sh2 * pow2 3 +
    sh3 * pow2 4 +
    sh4 * pow2 5 < pow2 6)

let scalar_compute_window_lemma_less sh0 sh1 sh2 sh3 sh4 = 
  assert_norm (pow2 1 + pow2 2 + pow2 3 + pow2 4 + pow2 5 < pow2 6)


#set-options "--z3rlimit 300"

val scalar_as_nat_is_same_as_scalar_to_odd: #c: curve 
  -> scalar: scalar_bytes #c {scalar_as_nat scalar < pow2 (getPower c)} -> t: pos ->
  Lemma (scalar_as_nat scalar / pow2 t == scalarToOdd (getPower c) (scalar_as_nat scalar) / pow2 t)

let scalar_as_nat_is_same_as_scalar_to_odd #c scalar t = 
  if scalar_as_nat scalar % 2 = 1 then ()
  else
    begin
      division_multiplication_lemma (scalarToOdd (getPower c) (scalar_as_nat scalar)) 2 (pow2 (t - 1));
      division_multiplication_lemma (scalar_as_nat scalar) 2 (pow2 (t - 1));
      pow2_double_mult (t - 1)
    end

val scalar_compute_window_lemma: #c: curve 
  -> scalar: scalar_bytes #c {scalar_as_nat scalar < pow2 (getPower c)}
  -> i: size_t {v i < getPower c / Spec.ECC.WNAF.w - 1} ->
  Lemma (
    let t = (v i + 1) * w  in 
    let sh0 = v (ith_bit scalar (t + 1)) in 
    let sh1 = v (ith_bit scalar (t + 2)) in 
    let sh2 = v (ith_bit scalar (t + 3)) in 
    let sh3 = v (ith_bit scalar (t + 4)) in 
    let sh4 = v (ith_bit scalar (t + 5)) in 

    let i = sh0 * pow2 1 + 
      sh1 * pow2 2 +
      sh2 * pow2 3 +
      sh3 * pow2 4 +
      sh4 * pow2 5 in 
  scalarToOdd (getPower c) (scalar_as_nat scalar) / pow2 (t + 1) % m * 2 == i)

let scalar_compute_window_lemma #c scalar k = 
  let t = (v k + 1) * w  in 
  let sh0 = v (ith_bit scalar (t + 1)) in 
  let sh1 = v (ith_bit scalar (t + 2)) in 
  let sh2 = v (ith_bit scalar (t + 3)) in 
  let sh3 = v (ith_bit scalar (t + 4)) in 
  let sh4 = v (ith_bit scalar (t + 5)) in 

  let i = sh0 * pow2 1 + 
    sh1 * pow2 2 +
    sh2 * pow2 3 +
    sh3 * pow2 4 +
    sh4 * pow2 5 in 
    
  scalar_as_nat_def #c scalar (getPower c - (t + 1));
  scalar_as_nat_def #c scalar (getPower c - (t + 2));
  scalar_as_nat_def #c scalar (getPower c - (t + 3));
  scalar_as_nat_def #c scalar (getPower c - (t + 4));
  scalar_as_nat_def #c scalar (getPower c - (t + 5));

  scalar_compute_window_lemma_lemma_powers ();

  let d = scalar_as_nat scalar in 
  let len = v (getScalarLen c) in 
  
  assert (2 * scalar_as_nat_ scalar (len - (t + 1)) == pow2 6 * scalar_as_nat_ scalar (len - (t + 6)) + i);
  assert (2 * scalar_as_nat_ scalar (len - (t + 1)) % pow2 6 == (pow2 6 * scalar_as_nat_ scalar (len - (t + 6)) + i) % pow2 6); 

  pow2_multiplication_modulo_lemma_2 (scalar_as_nat_ scalar (len - (t + 1))) 6 1;
  assert(scalar_as_nat_ scalar (len - (t + 1)) * 2 % pow2 6 == (pow2 6 * scalar_as_nat_ scalar (len - (t + 6)) + i) % pow2 6);

  lemma_mod_plus i (scalar_as_nat_ scalar (len - (t + 6))) (pow2 6);
  assert(scalar_as_nat_ scalar (len - (t + 1)) % pow2 5 * 2 ==  i % pow2 6);

  scalar_compute_window_lemma_less sh0 sh1 sh2 sh3 sh4;
  small_mod i (pow2 6);

  Hacl.Impl.EC.Masking.ScalarAccess.Lemmas.test #c scalar (len - (t + 1));
  assert(scalar_as_nat_ scalar (len - (t + 1)) % pow2 5 * 2 == i);

  assert(scalar_as_nat_ scalar (len - (t + 1)) == d / pow2 (t + 1));
  assert(d / pow2 (t + 1) % m * 2 == i);
  scalar_as_nat_is_same_as_scalar_to_odd scalar (t + 1)


val scalar_rwnaf_lemma0_lemma_byte: #c: curve -> scalar: scalar_bytes #c ->
  Lemma (
    let i0 = ith_bit scalar 0 in 
    let i1 = ith_bit scalar 1 in 
    let i2 = ith_bit scalar 2 in 
    let i3 = ith_bit scalar 3 in 
    let i4 = ith_bit scalar 4 in  
    let i5 = ith_bit scalar 5 in 
    let i6 = ith_bit scalar 6 in  
    let i7 = ith_bit scalar 7 in  
    v i0 + v i1 * pow2 1 + v i2 * pow2 2 + v i3 * pow2 3 + v i4 * pow2 4 + v i5 * pow2 5 + v i6 * pow2 6 + v i7  * pow2 7 
    == v (Lib.Sequence.index scalar (v (getScalarLenBytes c) - 1)))

let scalar_rwnaf_lemma0_lemma_byte #c scalar = 
  Hacl.Impl.EC.Masking.ScalarAccess.Lemmas.lemma_index_as_ith #c scalar (v (getScalarLenBytes c) - 1);

  assert_norm(pow2 0 == 1);

  assert(
    let l = v (getScalarLen c) in
    let i = (v (getScalarLenBytes c) - 1) in 
    let s = scalar in 
    v (Lib.Sequence.index scalar (v (getScalarLenBytes c) - 1)) == 
      v (ith_bit s 0) + 
      pow2 1 * v (ith_bit s 1) + 
      pow2 2 * v (ith_bit s 2) + 
      pow2 3 * v (ith_bit s 3) + 
      pow2 4 * v (ith_bit s 4) +
      pow2 5 * v (ith_bit s 5) + 
      pow2 6 * v (ith_bit s 6) + 
      pow2 7 * v (ith_bit s 7))


val scalar_rwnaf_lemma0: #c: curve -> scalar: scalar_bytes #c -> 
  Lemma (scalar_as_nat scalar % pow2 8 = v (Lib.Sequence.index scalar (v (getScalarLenBytes c) - 1)))

let scalar_rwnaf_lemma0 #c scalar = 
  let len = v (getScalarLen c) in 

  let i0 = ith_bit scalar 0 in 
  let i1 = ith_bit scalar 1 in 
  let i2 = ith_bit scalar 2 in 
  let i3 = ith_bit scalar 3 in 
  let i4 = ith_bit scalar 4 in  
  let i5 = ith_bit scalar 5 in 
  let i6 = ith_bit scalar 6 in  
  let i7 = ith_bit scalar 7 in  

  let q = v (getScalarLenBytes c) - 1 in


  shift_right_lemma (Lib.Sequence.index scalar (v (getScalarLenBytes c) - 1)) (size 0);
  logand_mask (Lib.Sequence.index scalar  (v (getScalarLenBytes c) - 1)) (u8 1) 1; 

  assert(v i0 == v (Lib.Sequence.index scalar q) % 2);
  scalar_rwnaf_lemma0_lemma_byte #c scalar;

    assert_norm (pow2 2 = 4);
    assert_norm (pow2 3 = 8);
    assert_norm (pow2 4 = 16);
    assert_norm (pow2 5 = 32);
    assert_norm (pow2 6 = 64);
    assert_norm (pow2 7 = 128);
    assert_norm (pow2 8 = 256);

  scalar_as_nat_def #c scalar len;
  scalar_as_nat_def #c scalar (len - 1);
  scalar_as_nat_def #c scalar (len - 2);
  scalar_as_nat_def #c scalar (len - 3);
  scalar_as_nat_def #c scalar (len - 4);
  scalar_as_nat_def #c scalar (len - 5);
  scalar_as_nat_def #c scalar (len - 6);
  scalar_as_nat_def #c scalar (len - 7);

  lemma_mod_plus (v (Lib.Sequence.index scalar q)) (scalar_as_nat_ scalar (len - 8)) (pow2 8);
    assert ( v (Lib.Sequence.index scalar q) < pow2 8);
  small_mod (v (Lib.Sequence.index scalar q)) (pow2 8);
    assert(scalar_as_nat scalar % pow2 8 = v (Lib.Sequence.index scalar q))


val logor_definition_i: i: pos -> a: UInt.uint_t i -> b : UInt.uint_t i -> Lemma (
  forall (j: nat {j < i}). UInt.nth #i (UInt.logor a b) j = (UInt.nth a j) || (UInt.nth b j))

let logor_definition_i i a b = 
  let t: Type0 = j: nat {j < i} in 
  let p: (t -> GTot Type) = (fun (j: t) -> UInt.nth #i (UInt.logor a b) j = (UInt.nth a j) || (UInt.nth b j)) in 
  let r: (x : t -> Lemma (p x)) = UInt.logor_definition #i a b in 

  Classical.forall_intro #t #p r


#push-options "--max_ifuel 1 --max_fuel 1"

val logor_mask: a: uint64 -> Lemma (v (logor (u64 1) a) == v a / 2 * 2 + 1)

let logor_mask a = 
  if v a % 2 = 0 then 
    begin
      logor_disjoint (u64 1) a 1
    end
  else
    begin
      logor_spec (u64 1) a;
      UInt.one_nth_lemma #64 1; 
      UInt.logor_definition #64 1 (v a) 63;
      logor_definition_i 64 (v a) 1;
      UInt.nth_lemma #64 (v a) (v (logor (u64 1) a))
    end

#pop-options


val scalar_rwnaf_lemma_tail: #c: curve -> s: nat {s < pow2 (v (getScalarLen c))} -> 
  Lemma (
    let len = v (getScalarLen c) in 
    ((s / pow2 ((len / w - 1) * w + 1) % pow2 w * 2 + 1) / pow2 (w + 1) * pow2 (w + 1) + m) % pow2 64 / m == 
    ((s / pow2 ((len / w - 1) * w + 1) % pow2 w * 2 + 1) / pow2 (w + 1) * pow2 (w + 1) + m) / m)

let scalar_rwnaf_lemma_tail #c s = 
  let len = v (getScalarLen c) in 
  lemma_div_lt_nat s len ((len / w - 1) * w + 1);
  multiply_fractions (s / pow2 ((len / w - 1) * w + 1) % pow2 w * 2 + 1) (pow2 (w + 1));
  assert_norm(pow2 w * 2 + 1 + m < pow2 64);
  small_mod ((s / pow2 ((len / w - 1) * w + 1) % pow2 w * 2 + 1) / pow2 (w + 1) * pow2 (w + 1) + m) (pow2 64)


val scalar_rwnaf_lemma0_tail: #c: curve -> s: nat {s < pow2 (v (getScalarLen c))} -> 
  Lemma (
    let len = v (getScalarLen c) in 
    ((s / pow2 ((len / w - 1) * w + 1) % pow2 w * 2 + 1) / pow2 (w + 1) * pow2 (w + 1) + m) / m == 1)

let scalar_rwnaf_lemma0_tail #c s = 
  let len = v (getScalarLen c) in 

  pow2_plus w 1;

  assert(((s / pow2 ((len / w - 1) * w + 1) % pow2 w * 2 + 1) / pow2 (w + 1) * pow2 (w + 1) + m) / m == (s / pow2 ((len / w - 1) * w + 1) % pow2 w * 2 + 1) / pow2 (w + 1) * 2 + 1);

  assert(s / pow2 ((len / w - 1) * w + 1) % pow2 w < pow2 w);
  assert(s / pow2 ((len / w - 1) * w + 1) % pow2 w  <= pow2 w - 1);
  assert(s / pow2 ((len / w - 1) * w + 1) % pow2 w * 2 <= (pow2 w - 1) * 2);
  assert(s / pow2 ((len / w - 1) * w + 1) % pow2 w * 2 <= pow2 w * 2 - 2);
  assert(s / pow2 ((len / w - 1) * w + 1) % pow2 w * 2 + 1 <= pow2 w * 2 - 1);
  assert(s / pow2 ((len / w - 1) * w + 1) % pow2 w * 2 + 1 < pow2 w * 2);
  assert((s / pow2 ((len / w - 1) * w + 1) % pow2 w * 2 + 1 < pow2 (w + 1)));
  
  assert(1 == (s / pow2 ((len / w - 1) * w + 1) % pow2 w * 2 + 1) / pow2 (w + 1) * 2 + 1)


val rwnaf_lemma0_: d0: nat -> j: nat -> Lemma (
  (2 * (d0 / pow2 (j * w + 1)) + 1) % (2 * m) - m == (d0 / pow2 (j * w + 1) % pow2 w * 2 + 1) % (2 * m) - m)

let rwnaf_lemma0_ d0 j = 
  calc (==) {
  (2 * (d0 / pow2 (j * w + 1)) + 1) % (2 * m);
    (==) {lemma_mod_add_distr 1 (2 * (d0 / pow2 (j * w + 1))) (2 * m)}
  (2 * (d0 / pow2 (j * w + 1)) % (2 * pow2 w) + 1) % (2 * m);
    (==) {pow2_double_mult w}
  (2 * (d0 / pow2 (j * w + 1)) % (pow2 (w + 1)) + 1) % (2 * m);
  (==) {pow2_multiplication_modulo_lemma_2 ((d0 / pow2 (j * w + 1))) (w + 1) 1}
  (2 * (d0 / pow2 (j * w + 1) % pow2 w) + 1) % (2 * m); }

val rwnaf_lemma0: d0: nat -> Lemma
  (forall (j: nat). (2 * (d0 / pow2 (j * w + 1)) + 1) % (2 * m) - m == (d0 / pow2 (j * w + 1) % pow2 w * 2 + 1) % (2 * m) - m)

let rwnaf_lemma0 d0 = 
  Classical.forall_intro (rwnaf_lemma0_ d0)


val scalar_rwnaf_lemma_to_spec: n: pos {2 * (n / w + 1) < pow2 32}
  -> d: nat {d < pow2 n} 
  -> out: lbuffer uint64 (size (2 * (n / w + 1))) -> h: mem 
  -> Lemma (requires (
    let wnaf_repr = to_wnaf n (scalarToOdd n d) in (
    forall (j: nat {j < n / w }). 
      let sign = Lib.Sequence.index (as_seq h out) (2 * j + 1) in 
      let abs =  Lib.Sequence.index (as_seq h out) (2 * j) in 
      let wf = Lib.Sequence.index #_ #(n / w + 1) wnaf_repr j in 
      (if wf >= 0 then v sign = 0 else v sign = maxint U64) /\ (
      if v sign = 0 then wf == v abs else - wf == v abs)) /\ (
    let lastIndex = n / w in 
    let absLast = Lib.Sequence.index (as_seq h out) (2 * lastIndex) in 
    let signLast = Lib.Sequence.index (as_seq h out) (2 * lastIndex + 1) in 
    v signLast == 0 /\
    v absLast = Lib.Sequence.index #_ #(n / w + 1) wnaf_repr (n / w)))) 
  (ensures (
    let wnaf_repr = to_wnaf n (scalarToOdd n d) in 
    forall (j: nat {j <= n / w }). 
      let sign = Lib.Sequence.index (as_seq h out) (2 * j + 1) in 
      let abs =  Lib.Sequence.index (as_seq h out) (2 * j) in 
      let wf = Lib.Sequence.index #_ #(n / w + 1) wnaf_repr j in 
      (if wf >= 0 then v sign = 0 else v sign = maxint U64) /\ (
      if v sign = 0 then wf == v abs else - wf == v abs)))

let scalar_rwnaf_lemma_to_spec n d out h = ()


(* for all the points on the curve (except a point at infinity, we do not talk about it now) there is an inverse point *)
assume val lemma_inverse_existence: #c: curve 
  -> p0: Spec.ECC.point #c {~ (isPointAtInfinity #Jacobian p0)} 
  -> p:  Spec.ECC.point #c {~ (isPointAtInfinity #Jacobian p)}
  -> Lemma (
  exists (b: pos {b < getOrder #c}). 
    let bP = Spec.ECC.point_mult #c b p0 in
    isPointAtInfinity (pointAdd #c bP p))

(* this inverse point is unique *)
val lemma_inverse_uniqueness: #c: curve
  -> p:  Spec.ECC.point #c {~ (isPointAtInfinity #Jacobian p)}
  -> q:  Spec.ECC.point #c {~ (isPointAtInfinity #Jacobian q) /\ isPointAtInfinity (pointAdd p q)}
  -> q1: Spec.ECC.point #c {~ (isPointAtInfinity #Jacobian q1) /\ isPointAtInfinity (pointAdd p q1)}
  -> Lemma (pointEqual q q1)

let lemma_inverse_uniqueness #c p q q1 = 
  curve_compatibility_with_translation_lemma #c q q1 p;
  curve_commutativity_lemma p q;
  curve_commutativity_lemma p q1


val getDLP: #c: curve 
  -> p: Spec.ECC.point #c {~ (isPointAtInfinity #Jacobian p)} 
  -> Tot (b: pos {b < getOrder #c /\ 
    pointEqual p (Spec.ECC.point_mult #c b (basePoint #c))})

let getDLP #c p = admit()


val getDLP_point_mult: #c: curve 
  -> b0: pos {b0 < getOrder #c} 
  -> p: Spec.ECC.point #c {~ (isPointAtInfinity #Jacobian p) /\ 
    pointEqual p (point_mult #c b0 (basePoint #c))}
  -> Lemma (getDLP #c p == b0)

let getDLP_point_mult #c b0 p = 
  if b0 <> getDLP #c p then
    begin
      assert(pointEqual p (point_mult #c b0 (basePoint #c)));
      Hacl.Impl.EC.ScalarMult.Radix.lemma_two_points_different_coeff_not_equal (basePoint #c) b0 p (getDLP #c p) (point_mult #c (getDLP #c p) (basePoint #c));
      assert(False)
    end


val point_neg_lemma_infinity_indexes: #c: curve -> p: Spec.ECC.point #c {~ (isPointAtInfinity #Jacobian p)} ->
  Lemma(
    let b = getDLP #c p in 
    isPointAtInfinity (pointAdd #c p (point_mult #c (-b) (basePoint #c))))

let point_neg_lemma_infinity_indexes #c p = 
  let b = getDLP #c p in 
  let q = point_mult #c (-b) (basePoint #c) in
  lemmaApplPointAdd (basePoint #c) b p (-b) q;
    assert(pointEqual (pointAdd p q) (point_mult #c 0 (basePoint #c)));
  point_mult_0 #c (basePoint #c) 0


val point_addition_y_is_0: #c: curve 
  -> p: Spec.ECC.point #c #Jacobian {~ (isPointAtInfinity #Jacobian p) /\ (let x, y, z = p in y == 0)} ->
  Lemma (isPointAtInfinity (pointAdd p p))

let point_addition_y_is_0 #c p = 
  let x, y, z = p in 

  small_mod 0 (getPrime c);

    let prime = getPrime c in 
    let x, y, z = toJacobianCoordinates #Jacobian p in
    let delta = z * z in 
    let alpha = 3 * (x - delta) * (x + delta) in 
    let x3 = (alpha * alpha) % prime in 
    let y3 = (alpha * ( - x3)) % prime in 
    let z3 = ((z) * (z) - z * z - 0) % prime in 
  assert(pointAdd p p = (x3, y3, 0));

  assert(isPointAtInfinity (x3, y3, 0))


val lemma_point_negative_and_point_y_are_not_equal: #c: curve 
  -> p: Spec.ECC.point #c #Jacobian {~ (isPointAtInfinity #Jacobian p) /\ (let x, y, z = p in z <> 0) } -> 
  Lemma (let x, y, z = p in 
    y > 0 ==>
      (modp_inv2 #c (z * z * z) * y) % getPrime c <> (modp_inv2 #c (z * z * z) * ((0 - y) % getPrime c) % getPrime c))

let lemma_point_negative_and_point_y_are_not_equal #c p = 
  let x, y, z = p in 
  let zMod = modp_inv2 #c (z * z * z) in 
  let p = getPrime c in 
  let a = (zMod * y) % getPrime c in 
  let b = (zMod * ((0 - y) % getPrime c)) % getPrime c in 

  if a = b then begin
    small_mod z p;
    Hacl.Impl.EC.Math.lemma_a_not_zero_b_not_zero_mod_not_zero p z z;
    Hacl.Impl.EC.Math.lemma_a_not_zero_b_not_zero_mod_not_zero p (z * z) z;
    Hacl.Impl.EC.Math.lemma_exp_not_zero p (z * z * z) (p - 2);
    FStar.Math.Fermat.mod_mult_congr (getPrime c) y ((0 - y) % getPrime c) zMod;
    
    small_modulo_lemma_1 y p; 
    lemma_mod_twice (0 - y) p;

    if y > 0 then begin
      lemma_mod_sub_1 y p;

      assert(y % 2 == (p - y) % 2);

      lemma_mod_add_distr (- y) p 2;
      assert(~ (FStar.Math.Euclid.divides p 2));
      if (p % 2 = 0) then 
	begin
	  FStar.Math.Euclid.mod_divides p 2;
	  assert(False)
	end;
      
      assert (p % 2 == 1);

      assert(y % 2 == (1 - y) % 2);
      assert(False)
    end
  end



val point_neg_infinity_when_y_minus: #c: curve -> x: nat {x < getPrime c} -> y: nat {y < getPrime c} 
  -> z: nat {z <> 0 /\ z < getPrime c} ->
  Lemma (
    let p: Spec.ECC.point #c = (x, y, z) in 
    let q: Spec.ECC.point #c = (x, (0 - y) % getPrime c, z) in 
    isPointAtInfinity (pointAdd #c p q))

let point_neg_infinity_when_y_minus #c x y z = 
  let p: Spec.ECC.point #c = x, y, z in 
  let q: Spec.ECC.point #c = (x, (0 - y) % getPrime c, z) in 

  let pAffineX, pAffineY, pAffineZ = _norm p in 
  let qAffineX, qAffineY, qAffineZ = _norm q in 

  _norm_modification_of_y p;
  _norm_modification_of_y q;

  if y > 0 then
    lemma_point_negative_and_point_y_are_not_equal p
  else
    point_addition_y_is_0 p
    
  
val lemma_mod_sub_0: #c: curve -> a: nat {a < getPrime c} -> Lemma ((0 - a) % getPrime c == 0 <==> a == 0)

let lemma_mod_sub_0 #c a = 
  if a <> 0 then
    lemma_mod_sub_1 a (getPrime c)


val lemma_fromDomain0: #c: curve -> Lemma (fromDomain #c 0 == 0)

let lemma_fromDomain0 #c =   
  lemmaFromDomain #c #DH 0;
  assert(fromDomain #c 0 == 0 * modp_inv2_prime (pow2 (getPower c)) (getModePrime DH c) % getModePrime DH c);
  assert(0 * modp_inv2_prime (pow2 (getPower c)) (getModePrime DH c) == 0);
  small_modulo_lemma_1 0 (getModePrime DH c);
  assert (0 * modp_inv2_prime (pow2 (getPower c)) (getModePrime DH c) % getModePrime DH c == 0)


val pow2_not_reducible_mod_prime: a: nat -> p: nat {p > 2 /\ Math.Euclid.is_prime p} -> Lemma (pow2 a % p <> 0)

let rec pow2_not_reducible_mod_prime a p = 
  match a with 
  |0 -> assert(pow2 0 == 1); assert_norm (1 % p <> 0)
  |_ -> 
    pow2_not_reducible_mod_prime (a - 1) p;
    assert(pow2 (a - 1) % p <> 0);

    FStar.Math.Lemmas.pow2_double_mult (a - 1);
    assert(pow2 a % p = pow2 (a - 1) * 2 % p);

    if (pow2 (a - 1) * 2 % p = 0) then 
      begin
	FStar.Math.Euclid.euclid_prime p (pow2 (a - 1)) 2;
	assert_norm(2 % p <> 0);
	assert(False)
      end


val mult_two_not_0_is_not_0: a: nat -> b: pos -> Lemma (pow2 a * b <> 0)

let mult_two_not_0_is_not_0 a b = ()


val scalar_mult_cmb_composite_not_infinity: #c: curve 
  -> a: nat 
  -> b: pos {b < getOrder #c} ->
  Lemma (
    ~ (isPointAtInfinity (point_mult #c (pow2 a * b) (basePoint #c))) /\
    (pow2 a * b) % getOrder #c <> 0)

let scalar_mult_cmb_composite_not_infinity #c a b = 
  curve_order_is_the_smallest #c (basePoint #c);
  lemma_scalar_reduce #c (basePoint #c) (pow2 a * b);
  
  let order = getOrder #c in 

  pow2_not_reducible_mod_prime a order;
  small_mod b order; 

  mult_two_not_0_is_not_0 a b;
  Hacl.Impl.EC.Math.lemma_a_not_zero_b_not_zero_mod_not_zero order (pow2 a) b


val dlp_mod_order: #c: curve -> p: Spec.ECC.point #c {~ (isPointAtInfinity #Jacobian p)} 
  -> i: nat {i % getOrder #c <> 0} ->  Lemma (
  pointEqual p (point_mult #c i (basePoint #c)) ==> 
  getDLP #c p == i % getOrder #c)

let dlp_mod_order #c p i = 
  if pointEqual p (point_mult #c i (basePoint #c)) then begin
     lemma_scalar_reduce #c (basePoint #c) i;
     getDLP_point_mult (i % getOrder #c) p
  end
  

val lemma_all_elements_rwnaf_odd: n: pos {n < pow2 32} 
  -> d: nat {d < pow2 n} 
  -> i: nat {i < Lib.Sequence.length (to_wnaf n (scalarToOdd n d))} ->
  Lemma (Seq.index (to_wnaf n (scalarToOdd n d)) i % 2 == 1 /\ (Seq.index (to_wnaf n (scalarToOdd n d)) i - 1) % 2 == 0)
 
let lemma_all_elements_rwnaf_odd n d j = 
  let r = to_wnaf n (scalarToOdd n d) in 
  if j < n / w then begin
    lemma_mod_sub_distr ((2 * (d / pow2 (w * j + 1)) + 1) % (2 * m)) m 2;
    pow2_double_mult (w - 1);
    pow2_double_mult w;
    pow2_modulo_modulo_lemma_1 (2 * (d / pow2 (w * j + 1)) + 1) 1 (w + 1)
    end


val lemmaApplPointAddReverse: #c: curve -> p: Spec.ECC.point #c -> k: int 
  -> Lemma (pointEqual (point_mult k p) (pointAdd p (point_mult (k - 1) p)))

let lemmaApplPointAddReverse #c p k = 
  point_mult_1 p;
  lemmaApplPointAdd p 1 p (k - 1) (point_mult (k - 1) p)


val lemma_scalar_reduce_neg: #c: curve -> p0: Spec.ECC.point #c {~ (isPointAtInfinity #Jacobian p0)} -> a: int -> b: int -> 
 Lemma (point_mult #c (- (a * (- b) % getOrder #c)) p0 == point_mult #c ((a * b) % getOrder #c) p0)

let lemma_scalar_reduce_neg #c p0 a b = 
  let k = point_mult #c (- (a * (- b) % getOrder #c)) p0 in 
  lemma_scalar_reduce #c p0 (- (a * (- b) % getOrder #c));
    assert(k == point_mult #c ((0 - (a * (- b) % getOrder #c)) % getOrder #c) p0);
  lemma_mod_sub_distr 0 ((a * (- b))) (getOrder #c);
    assert(k == point_mult #c ((a * b) % getOrder #c) p0)


val lemma_mod_negative_number: #c: curve -> a: nat -> bits: int -> 
  Lemma ((- ( pow2 a * (- bits) % getOrder #c)) % getOrder #c == pow2 a * bits % getOrder #c)

let lemma_mod_negative_number #c a bits = 
  let o = getOrder #c in 
  lemma_mod_sub_distr 0 (pow2 a * (- bits)) o


val lemma_scalar_step1: #c: curve
  -> s: scalar_bytes 
  -> rnaf: Lib.Sequence.lseq uint64 (2 * (v (getScalarLen c) / w + 1))
  -> k: nat {k < (v (getLenWnaf #c) + 1)}
  -> z: Spec.ECC.point #c ->
  Lemma 
  (requires (
    let d = scalar_as_nat #c s in
    let n = v (getScalarLen c) in d < pow2 n /\ (
    let d_as_wnaf = to_wnaf n (scalarToOdd n d) in rnaf_to_spec #c rnaf ==  d_as_wnaf /\ (
    let bits = Lib.Sequence.index #_ #(v (getLenWnaf #c) + 1) d_as_wnaf k in 
    let b = pow2 (k * w) * bits % getOrder #c in ~ (pointEqual #c z (point_mult #c b (basePoint #c)))))))
  (ensures (
    let d0 = v (Lib.Sequence.index rnaf (2 * k)) in 
    let d1 = v (Lib.Sequence.index rnaf (2 * k + 1)) in 
    let b = pow2 (k * w) * ((d0 - 1) / 2 * 2 + 1) % getOrder #c in
    if d1 = 0 then 
      ~ (pointEqual #c z (point_mult #c (pow2 (k * w) * ((d0 - 1) / 2 * 2 + 1) % getOrder #c) (basePoint #c))) 
    else
      ~ (pointEqual #c z (point_mult #c (- (pow2 (k * w) * ((d0 - 1) / 2 * 2 + 1) % getOrder #c)) (basePoint #c)))))

let lemma_scalar_step1 #c s rnaf k z = 
  let d = scalar_as_nat #c s in
  let n = v (getScalarLen c) in 
  let d_as_wnaf = to_wnaf n (scalarToOdd n d) in 
  let bits = Seq.index d_as_wnaf k in 
  let b = pow2 (k * w) * bits % getOrder #c in
    assert(~ (pointEqual #c z (point_mult #c b (basePoint #c))));

  let d0 = v (Lib.Sequence.index rnaf (2 * k)) in 
  let d1 = v (Lib.Sequence.index rnaf (2 * k + 1)) in 

    assert (if d1 = 0 then d0 = bits else d0 = - bits);
  
  lemma_all_elements_rwnaf_odd (v (getScalarLen c)) (scalar_as_nat s) k;
    assert (bits % 2 == 1);
    assert(bits = (bits - 1) / 2 * 2 + 1);

  lemma_mod_negative_number #c (k * w) bits;

    assert(if d1 = 0 then 
      ~ (pointEqual #c z (point_mult #c (pow2 (k * w) * ((d0 - 1) / 2 * 2 + 1) % getOrder #c) (basePoint #c))) else
      ~ (pointEqual #c z (point_mult #c (- (pow2 (k * w) * ((d0 - 1) / 2 * 2 + 1) % getOrder #c)) (basePoint #c))))


val lemma_wnaf_step2: #c: curve 
  -> rnaf: Lib.Sequence.lseq uint64 (2 * (v (getScalarLen c) / w + 1)) 
  -> k: nat {k < Seq.length (rnaf_to_spec #c rnaf)}
  -> p: Spec.ECC.point #c #Jacobian ->
  Lemma (
    let s = rnaf_to_spec #c rnaf in
    let i = v (getLenWnaf #c) - k in 
    let p0 = basePoint #c in 
    pointEqual (wnaf_step2 #c p0 s k p) (pointAdd p (point_mult #c (pow2 (w * i) * Seq.index s i) p0)))

let lemma_wnaf_step2 #c  rnaf k p = 
  let s = rnaf_to_spec #c rnaf in 
  let i = v (getLenWnaf #c) - k in 
  let p0 = basePoint #c in 
  assert(pointEqual (wnaf_step2 #c p0 s k p) (pointAdd p (point_mult  #c (Seq.index s i * pow2 (w * i)) p0)))


val lemma_application_wnaf_step_on_equal_points: #c: curve 
  -> p0: Spec.ECC.point #c {~ (isPointAtInfinity #Jacobian p0)}
  -> s: Lib.Sequence.seq int 
  -> r0: Spec.ECC.point #c 
  -> r1: Spec.ECC.point #c 
  -> j: nat {j < Seq.length s /\ Seq.length s < pow2 32 - 1} -> 
  Lemma (let f = wnaf_step2 #c p0 s in pointEqual r0 r1 ==> pointEqual #c (f j r0) (f j r1))

let lemma_application_wnaf_step_on_equal_points #c p0 s r0 r1 j = 
  let f = wnaf_step2 #c p0 s in 
  let l = Seq.length s in 

  if pointEqual r0 r1 then begin

    assert (f j r0 == wnaf_step2 #c p0 s j r0);
    
    let i = l - (j + 1) in 
    let bits = Seq.index s i * pow2 (w * i) in 

    assert(wnaf_step2 #c p0 s j r0 == pointAdd r0 (getPrecomputed p0 bits));
    assert(wnaf_step2 #c p0 s j r1 == pointAdd r1 (getPrecomputed p0 bits));

    curve_compatibility_with_translation_lemma r0 r1 (getPrecomputed p0 bits) 
  end


val lemma_equclidian_sum0: #c: curve -> d: nat -> i: nat -> 
  Lemma ((d / pow2 (w * i + 1) * 2 + 1) % (2 * m) == (d / pow2 (i * w + 1)) % pow2 w * 2 + 1)

let lemma_equclidian_sum0 #c d i = 
  small_mod ((d / pow2 (i * w + 1)) % pow2 w * 2 + 1) (2 * pow2 w);
  FStar.Math.Lemmas.lemma_mod_add_distr 1 (d / pow2 (w * i + 1) * 2) (2 * m);
  modulo_scale_lemma (d / pow2 (w * i + 1)) 2 m


val lemma_equclidian_sum1: #c: curve -> d: nat -> i: nat -> 
  Lemma (d / pow2 (i * w + w + 1) * 2 * m == (d / pow2 (i * w + 1) / pow2 w * pow2 w) * 2)

let lemma_equclidian_sum1 #c d i = 
  pow2_plus (i * w + 1) w;
  division_multiplication_lemma d (pow2 (i * w + 1)) (pow2 w)


val lemma_equclidian_sum: #c: curve -> d: nat -> i: nat ->
  Lemma ((d / pow2 (w * i + 1) * 2 + 1) % (2 * m) + d / pow2 (i * w + w + 1) * 2 * m == d / pow2 (i * w + 1) * 2 + 1)

let lemma_equclidian_sum #c d i = 
  lemma_equclidian_sum0 #c d i;
  lemma_equclidian_sum1 #c d i


val lemma_from_domain__:  #c: curve -> d: nat {d < pow2 (v (getScalarLen c))} 
  -> i: nat {
    let n = v (getScalarLen c) in 
    let s = to_wnaf n (scalarToOdd n d) in i < Seq.length s} -> 
  Lemma (ensures (
    let n = v (getScalarLen c) in 
    let d = scalarToOdd n d in 
    let s = to_wnaf n d in  
    let i' = Seq.length s - i - 1 in 
    from_wnaf_ s i' == d / pow2 (i' * w + 1) * 2 + 1))
  (decreases i)

let rec lemma_from_domain__ #c d i = 
  let n = v (getScalarLen c) in 
  let d = scalarToOdd n d in
  let s = to_wnaf n d in 
  match i with 
  |0 -> lemma_from_wnaf_last s
  |_ -> begin
    let i' = Seq.length s - i - 1 in 
    lemma_from_domain__ #c d (i - 1);
    lemma_from_wnaf_next s i';
    lemma_equclidian_sum #c d i'
  end


val lemma_each_element_rwnaf_:  #c: curve -> d: nat {d < pow2 (v (getScalarLen c))} 
  -> i: nat {
    let n = v (getScalarLen c) in 
    let s = to_wnaf n (scalarToOdd n d) in i < Seq.length s} -> 
  Lemma (
    let n = v (getScalarLen c) in
    let d = scalarToOdd n d in  
    let s = to_wnaf n d in  
    from_wnaf_ s i == d / pow2 (i * w + 1) * 2 + 1)

let lemma_each_element_rwnaf_ #c d i = 
  let n = v (getScalarLen c) in 
  let d = scalarToOdd n d in  
  let s = to_wnaf n d in  
  lemma_from_domain__ #c d (Seq.length s - i - 1)


val lemma_from_domain_is_not_equal_11: #c: curve -> Lemma (let n = getPower c in getOrder #c > pow2 (n - w) + 1)

let lemma_from_domain_is_not_equal_11 #c = 
  match c with 
  |P256 -> assert_norm (0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551 > pow2 (256 - w) + 1)
  |P384 -> assert_norm (0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973 > pow2 (384 - w) + 1)


val lemma_1st_element_rwnaf_less_order: #c: curve -> d: nat {d < pow2 (v (getScalarLen c))} -> 
  Lemma (
    let n = v (getScalarLen c) in 
    let d = scalarToOdd n d in  
    let s = to_wnaf n d in  
    from_wnaf_ s 1 < getOrder #c)

let lemma_1st_element_rwnaf_less_order #c d = 
  let n = v (getScalarLen c) in 
  let d = scalarToOdd n d in  
  let s = to_wnaf n d in 
  
  lemma_each_element_rwnaf_ #c d 1;
    assert(from_wnaf_ s 1 == (d / pow2 (w + 1) * 2 + 1) );

  lemma_div_lt d n (w + 1);
  pow2_double_mult (n - (w + 1));

  lemma_from_domain_is_not_equal_11 #c;
    assert(pow2 (n - w) + 1 < getOrder #c);
    
    assert(d / pow2 (w + 1) * 2 + 1 < pow2 (n - w) + 1);
    assert(pow2 (n - w) + 1 < getOrder #c);
    assert(d / pow2 (w + 1) * 2 + 1 < getOrder #c);
    
  small_mod (d / pow2 (w + 1) * 2 + 1) (getOrder #c);
    assert((d / pow2 (w + 1) * 2 + 1) % getOrder #c == (d / pow2 (w + 1) * 2 + 1))


val lemma_each_element_rwnaf: #c: curve -> d: nat {d < pow2 (v (getScalarLen c))} ->
  Lemma (
    let n = v (getScalarLen c) in 
    let d = scalarToOdd n d in  
    let s = to_wnaf n d in 
    forall (i: nat {i < Seq.length s}). from_wnaf_ s i == d / pow2 (i * w + 1) * 2 + 1)

let lemma_each_element_rwnaf #c d = Classical.forall_intro (fun i -> lemma_each_element_rwnaf_ #c d i)


open FStar.Tactics.Canon
open FStar.Tactics 

val lemma_from_domain_in_not_equal0: #c: curve
  -> s: scalar_bytes #c {scalar_as_nat s < getOrder #c}
  -> i: nat {
    let d = scalar_as_nat #c s in 
    let n = getPower c in 
    let s = to_wnaf n (scalarToOdd n d) in 
    let len = Seq.length s in 
    let o = getOrder #c in i < len - 1 /\ i > 0 /\ (
    let si = Seq.index s (len - (i + 1)) in si < 0)} -> 
  Lemma (
    let d = scalar_as_nat #c s in 
    let n = getPower c in 
    let d = scalarToOdd n d in  
    let scalar_as_wnaf = to_wnaf (getPower c) d in 
    let len = Seq.length scalar_as_wnaf in  
    let o = getOrder #c in 
    let si = Seq.index scalar_as_wnaf (len - (i + 1)) in 
    si % o > o - m - 1)

let lemma_from_domain_in_not_equal0 #c s i = 
  let d = scalar_as_nat #c s in 
  let n = getPower c in 
  let scalar_as_wnaf = to_wnaf n (scalarToOdd n d) in 

  let len = Seq.length scalar_as_wnaf in 
  let i' = len - (i + 1) in 
  let o = getOrder #c in 
  let si = Seq.index scalar_as_wnaf i' in 

  assert_norm (m < o);
  lemma_mod_sub_1 (- si) o; 
  small_mod (- si) o


val lemma_from_domain_is_not_equal_10: #c: curve -> Lemma (let n = getPower c in getOrder #c > pow2 (n - w + 1))

let lemma_from_domain_is_not_equal_10 #c = 
  match c with 
  |P256 -> assert_norm (0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551 > pow2 (256 - w + 1))
  |P384 -> assert_norm (0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973 > pow2 (384 - w + 1))


#push-options "--z3rlimit 300" 

val lemma_from_domain_is_not_equal_2: #c: curve
  -> s: scalar_bytes #c {scalar_as_nat s < getOrder #c}
  -> i: nat {
    let d = scalar_as_nat #c s in 
    let n = getPower c in 
    let scalar_as_wnaf = to_wnaf n (scalarToOdd n d) in 
    let len = Seq.length scalar_as_wnaf in 
    i < len - 1 /\ i > 0} -> 
  Lemma (
    let d = scalar_as_nat #c s in 
    let n = getPower c in 
    let s = to_wnaf n (scalarToOdd n d) in 
    let len = Seq.length s in 
    let o = getOrder #c in 
    from_wnaf_ s (len - i) * pow2 w >= pow2 w)

let lemma_from_domain_is_not_equal_2 #c s i = 
  let d = scalar_as_nat #c s in 
  let n = getPower c in
  let d = scalarToOdd n d in 
  let s = to_wnaf n d in 
  
  lemma_each_element_rwnaf #c d;
  lemma_mult_le_right (pow2 w) 1 (from_wnaf_ s (Seq.length s - i))


val lemma_from_domain_is_not_equal_3: #c: curve -> 
  Lemma (
    let n = getPower c in 
    let o = getOrder #c in 
    o - m - 1 > pow2 (n - w + 1))

let lemma_from_domain_is_not_equal_3 #c = 
  let n = getPower c in 
  let o = getOrder #c in
  match c with 
  |P256 -> assert_norm(o - m - 1 > pow2 (256 - w + 1))
  |P384 -> assert_norm(o - m - 1 > pow2 (384 - w + 1))


val lemma_from_domain_is_not_equal_1: #c: curve
  -> s: scalar_bytes #c {scalar_as_nat s < getOrder #c}
  -> i: nat {
    let d = scalar_as_nat #c s in 
    let n = getPower c in
    let scalar_as_wnaf = to_wnaf n (scalarToOdd n d) in 
    let len = Seq.length scalar_as_wnaf in 
    i < len - 1 /\ i > 0} -> 
  Lemma (
    let d = scalar_as_nat #c s in 
    let n = getPower c in
    let s = to_wnaf n (scalarToOdd n d) in 
    let len = Seq.length s in 
    let o = getOrder #c in 
    from_wnaf_ s (len - i) * pow2 w % o == from_wnaf_ s (len - i) * pow2 w /\ 
    from_wnaf_ s (len - i) * pow2 w < pow2 (n - w + 1))

let lemma_from_domain_is_not_equal_1 #c s i = 
  let d = scalar_as_nat #c s in 
  let n = getPower c in
  let d = scalarToOdd n d in 
  let s = to_wnaf n d in 
  
  let len = Seq.length s in 
  let o = getOrder #c in 

  lemma_each_element_rwnaf #c d;

  assert(from_wnaf_ s (len - i) == d / pow2 ((len - i) * w + 1) * 2 + 1);

  lemma_div_lt_nat d n ((len - i) * w + 1);
  pow2_double_mult (n - ((n / w + 1 - i) * w + 1));

    assert(d / pow2 ((len - i) * w + 1) * 2 + 1 <= pow2 (n - ((n / w + 1 - i) * w + 1) + 1));
  pow2_plus (n - ((n / w + 1 - i) * w + 1) + 1) w;
    assert((d / pow2 ((len - i) * w + 1) * 2 + 1) * pow2 w <= pow2 (n - n / w * w + i * w));


    assert(i < len - 1);
    assert(i <= len - 2);
    assert(n - n / w * w + i * w < n - w + 1);

  pow2_lt_compat (n - w + 1) (n - n / w * w + i * w);
    assert(pow2 (n - n / w * w + i * w) < pow2 (n - w + 1));

  lemma_from_domain_is_not_equal_10 #c;
    assert (getOrder #c > pow2 (n - w + 1));

    assert((d / pow2 ((len - i) * w + 1) * 2 + 1) * pow2 w < pow2 (n - w + 1));
  small_mod (from_wnaf_ s (len - i) * pow2 w) o;
    assert((d / pow2 ((len - i) * w + 1) * 2 + 1) * pow2 w < pow2 (n - w + 1));
    assert(from_wnaf_ s (len - i) * pow2 w < pow2 (n - w + 1));
    assert((from_wnaf_ s (len - i) * pow2 w) % o == (from_wnaf_ s (len - i) * pow2 w))


val lemma_from_domain_is_not_equal_index: #c: curve
  -> s: scalar_bytes #c {scalar_as_nat s < getOrder #c}
  -> i: nat {
    let d = scalar_as_nat #c s in 
    let n = getPower c in
    let scalar_as_wnaf = to_wnaf n (scalarToOdd n d) in 
    let len = Seq.length scalar_as_wnaf in 
    i < len - 1 /\ i > 0} -> 
  Lemma (
    let d = scalar_as_nat #c s in 
    let n = getPower c in
    let scalar_as_wnaf = to_wnaf n (scalarToOdd n d) in 
    let len = Seq.length scalar_as_wnaf in 
    let i' = len - (i + 1) in
    let o = getOrder #c in 
    from_wnaf_ scalar_as_wnaf (len - i) * pow2 (w * (len - i)) % o <> Seq.index scalar_as_wnaf i' * pow2 (w * i') % o)


let lemma_from_domain_is_not_equal_index #c s i = 
  let d = scalar_as_nat #c s in 
  let n = getPower c in
  let d = scalarToOdd n d in
  let scalar_as_wnaf = to_wnaf n d in 
  let len = Seq.length scalar_as_wnaf in 
  let i' = len - (i + 1) in 

  let o = getOrder #c in 

  FStar.Math.Lemmas.pow2_plus (w * (len - 1 - i)) w;

  lemma_each_element_rwnaf #c d;
  let si = Seq.index scalar_as_wnaf i' in 


  if from_wnaf_ scalar_as_wnaf (len - i) * pow2 (w * (len - i)) % o = si * pow2 (w * i') % o then 
    begin
      assert_by_tactic (from_wnaf_ scalar_as_wnaf (len - i) * (pow2 (w * (len - 1 - i)) * pow2 w) == (from_wnaf_ scalar_as_wnaf (len - i) * pow2 w) * pow2 (w * (len - 1 - i))) canon;
      pow2_not_reducible_mod_prime (w * i') o; 
      FStar.Math.Fermat.mod_mult_congr o (from_wnaf_ scalar_as_wnaf (len - i) * pow2 w) si (pow2 (w * i'));
      
      assert_norm (m < o);

      if si >= 0 then 
	begin
	  small_mod si o;
	  lemma_from_domain_is_not_equal_1 s i;
	  lemma_from_domain_is_not_equal_2 s i;
	  assert((from_wnaf_ scalar_as_wnaf (len - i) * pow2 w) = (2 * (d / pow2 (w * i' + 1)) + 1) % (2 * m) - m);
	  assert(False)
	end
      else
	begin
	  lemma_from_domain_is_not_equal_1 #c s i;
	  lemma_from_domain_in_not_equal0 #c s i;

	  assert(from_wnaf_ scalar_as_wnaf (len - i) * pow2 w = si % o);
	  assert(from_wnaf_ scalar_as_wnaf (len - i) * pow2 w < pow2 (n - w + 1));

	  lemma_from_domain_is_not_equal_3 #c;
	  assert (si % o > pow2 (n - w + 1));
	  assert(False)
	end
    end


val lemma_from_domain_is_not_equal_index_main0: #c: curve 
  -> s: scalar_bytes #c {scalar_as_nat s < getOrder #c} ->
  Lemma (
    let n = getPower c in 
    let d = scalar_as_nat #c s in 
    let scalar_as_wnaf = to_wnaf n (scalarToOdd n d) in 
    ~ (isPointAtInfinity (point_mult #c (pow2 (n / w * w) * (Seq.index scalar_as_wnaf (n / w)) % getOrder #c) (basePoint #c))))

let lemma_from_domain_is_not_equal_index_main0 #c s = 
  let n = getPower c in 
  let d = scalar_as_nat #c s in 
  let d = (scalarToOdd n d) in 
  let scalar_as_wnaf = to_wnaf n d in 

  lemma_each_element_rwnaf_ #c d (n / w);
  assert(Seq.index scalar_as_wnaf (n / w) == (d / pow2 ((n / w) * w + 1)) * 2 + 1);

  assert (d / pow2 ((n / w) * w + 1) * 2 + 1 >  0);

  assert(d < pow2 n);
  lemma_div_lt_nat d n ((n / w * w + 1)); 
  pow2_double_mult (n % w - 1);
  assert(d / pow2 ((n / w) * w + 1) * 2 + 1 < pow2 (n % w) + 1);
  assert_norm (pow2 (n % w) + 1 < getOrder #c);

  scalar_mult_cmb_composite_not_infinity #c ((n / w) * w) (Seq.index scalar_as_wnaf (n / w));
  assert(~ (isPointAtInfinity (point_mult #c (pow2 (n / w * w) * (Seq.index scalar_as_wnaf (n / w))) (basePoint #c))));

  lemma_scalar_reduce #c (basePoint #c) (pow2 (n / w * w) * (Seq.index scalar_as_wnaf (n / w)))

  
val lemma_from_domain_is_not_equal_index_main: #c: curve
  -> s: scalar_bytes #c {scalar_as_nat s < getOrder #c}
  -> i: nat {i >= 0 /\ i <= v (getLenWnaf #c) - 1}
  -> result: Spec.ECC.point #c {
    let d = scalar_as_nat #c s in 
    let n = getPower c in
    let scalar_as_wnaf = to_wnaf n (scalarToOdd n d) in 
    let len = Seq.length scalar_as_wnaf in
    pointEqual result (point_mult #c (from_wnaf_ scalar_as_wnaf (len - i) * pow2 (w * (len - i))) (basePoint #c))} -> 
  Lemma (
    let d = scalar_as_nat #c s in 
    let n = getPower c in
    let scalar_as_wnaf = to_wnaf n (scalarToOdd n d) in 
    let j = v (getLenWnaf #c) - i in 
    ~ (pointEqual #c result (point_mult #c (pow2 (j * w) * (Seq.index scalar_as_wnaf j) % getOrder #c) (basePoint #c))))

let lemma_from_domain_is_not_equal_index_main #c s i result = 
  if i = 0 then 
    begin
    	let d = scalar_as_nat #c s in 
	let n = getPower c in
	let scalar_as_wnaf = to_wnaf n (scalarToOdd n d) in 
	let len = Seq.length scalar_as_wnaf in
	from_wnaf_lemma_0 scalar_as_wnaf;
	assert(pointEqual result (point_mult #c 0 (basePoint #c)));
	  
	point_mult_0 #c (basePoint #c) 0;
	lemma_from_domain_is_not_equal_index_main0 s
    end
  else
    begin
      lemma_from_domain_is_not_equal_index s i;
      
      let d = scalar_as_nat #c s in 
      let n = getPower c in
      let d = scalarToOdd n d in 
      let scalar_as_wnaf = to_wnaf n d in 
      
      let len = Seq.length scalar_as_wnaf in 
      let o = getOrder #c in    
      let i' = len - (i + 1) in 

      let b = from_wnaf_ scalar_as_wnaf (len - i) * pow2 (w * (len - i)) in 
      let d = Seq.index scalar_as_wnaf i' * pow2 (w * i') % o in 
      let p0 = basePoint #c in 

      Hacl.Impl.EC.ScalarMult.Radix.lemma_two_points_different_coeff_not_equal #c p0 (b % o) (point_mult #c (b % o) p0) d (point_mult #c d p0);
      lemma_scalar_reduce #c p0 b;
      assert_by_tactic (Seq.index scalar_as_wnaf i' * pow2 (w * i') == pow2 (w * i') * Seq.index scalar_as_wnaf i') canon
    end


val lemma_pointAtInfInDomain: #c: curve -> p: Spec.ECC.point #c ->
  Lemma (isPointAtInfinity #Jacobian p == isPointAtInfinity #Jacobian (fromDomainPoint #c #DH p))

let lemma_pointAtInfInDomain #c p = 
  let x, y, z = p in 
  Hacl.Spec.MontgomeryMultiplication.lemma_pointAtInfInDomain #c x y z


val lemma_the_last_before_one_point_add_is_not_infinity: #c: curve 
  -> scalar: scalar_bytes #c {scalar_as_nat scalar < getOrder #c}
  -> result: Spec.ECC.point #c -> 
  Lemma
  (requires (
    let d = scalar_as_nat #c scalar in 
    let n = getPower c in
    let d = scalarToOdd n d in 
    let scalar_as_wnaf = to_wnaf n d in 
    let b = from_wnaf_ scalar_as_wnaf 1 * pow2 w in 
    pointEqual #c (fromDomainPoint #c #DH result) (point_mult #c b (basePoint #c))))
  (ensures  ~ (isPointAtInfinity #Jacobian result))


let lemma_the_last_before_one_point_add_is_not_infinity #c scalar result = 
  let d = scalar_as_nat #c scalar in 
  let n = getPower c in
  let d = scalarToOdd n d in 
  let s = to_wnaf n d in 
    
  lemma_each_element_rwnaf_ #c d 1;
  lemma_1st_element_rwnaf_less_order #c d;

  scalar_mult_cmb_composite_not_infinity #c w (from_wnaf_ s 1);

  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 

  assert_by_tactic (pow2 w * from_wnaf_ s 1 == from_wnaf_ s 1 * pow2 w) canon;
  lemma_pointAtInfInDomain #c result


val lemma_three_equal_points: #c: curve 
  -> p0: Spec.ECC.point #c #Jacobian
  -> p1: Spec.ECC.point #c #Jacobian {pointEqual p0 p1}
  -> p2: Spec.ECC.point #c #Jacobian {pointEqual p0 p2} -> 
  Lemma (pointEqual p1 p2)

let lemma_three_equal_points #c p0 p1 p2 =  assert(pointEqual p1 p2)


val lemma_point_equal_coeff_equal: #c: curve 
  -> pk: nat
  -> p1: Spec.ECC.point #c #Jacobian {pointEqual p1 (point_mult pk (basePoint #c))}
  -> qk: nat {qk < getOrder #c}
  -> p2: Spec.ECC.point #c #Jacobian {pointEqual p2 (point_mult qk (basePoint #c)) /\ pointEqual p1 p2}
  -> Lemma (pk % getOrder #c == qk % getOrder #c)

let lemma_point_equal_coeff_equal #c pk p qk q = 
  let o = getOrder #c in 
  
  if pk  % o <> qk % o then 
    begin
      lemma_scalar_reduce #c (basePoint #c) pk;
      lemma_scalar_reduce #c (basePoint #c) qk;
      Hacl.Impl.EC.ScalarMult.Radix.lemma_two_points_different_coeff_not_equal #c (basePoint #c) (pk % o)  p (qk % o) q;
      assert(False)
    end


val lemma_last_bit: #c: curve 
  -> scalar: scalar_bytes #c {scalar_as_nat scalar < getOrder #c}
  -> result: Spec.ECC.point #c 
  -> Lemma
  (requires (
    let d = scalar_as_nat #c scalar in 
    let n = getPower c in
    let d = scalarToOdd n d in 
    let s = to_wnaf n d in 
    scalar_as_nat #c scalar % 2 == 0 /\
    pointEqual #c result (Lib.LoopCombinators.repeati (n / w + 1) (wnaf_step2 #c (basePoint #c) s) (0, 0, 0))))
  (ensures (~ (pointEqual #c result (Spec.ECC.point_mult #c (- 1) (basePoint #c)))))

let lemma_last_bit #c scalar result = 
  let d = scalar_as_nat #c scalar in 
  let n = getPower c in
  let d = scalarToOdd n d in 
  let s = to_wnaf n d in 

  let p0 = basePoint #c in 
  let r0 = Lib.LoopCombinators.repeati (getPower c / w + 1) (wnaf_step2 #c p0 s) (0, 0, 0) in 

  assert(pointEqual #c result r0);

  assert(pointEqual (wnaf_spec #c scalar p0) (pointAdd r0 (point_mult (-1) p0)));
  assert(pointEqual (wnaf_spec #c scalar p0) (point_mult #c (scalar_as_nat #c scalar) p0));

  lemma_three_equal_points (wnaf_spec #c scalar p0) (pointAdd r0 (point_mult (-1) p0)) (point_mult #c (scalar_as_nat #c scalar) p0);
  assert (pointEqual (point_mult #c (scalar_as_nat #c scalar) p0) (pointAdd r0 (point_mult (-1) p0)));

  curve_compatibility_with_translation_lemma #c r0 result (point_mult (-1) p0);

  if pointEqual #c result (Spec.ECC.point_mult #c (- 1) (basePoint #c)) then 
    begin
      assert (pointEqual (point_mult #c (scalar_as_nat #c scalar) p0) (pointAdd result (point_mult (-1) p0)));
      lemmaApplPointAdd (basePoint #c) (-1) result (-1) result; 
      lemma_scalar_reduce #c p0 (-1 -1); 
      let o = getOrder #c in 
      assert(pointEqual (pointAdd result (point_mult (-1) p0)) (point_mult ((-1 - 1) % getOrder #c) p0));
      lemma_mod_sub_1 2 o;
      small_mod 2 o;
      assert(pointEqual (pointAdd result (point_mult (-1) p0)) (point_mult (o - 2) p0));
      lemma_mod_sub_1 2 o;

      assert (pointEqual (point_mult #c (scalar_as_nat #c scalar) p0) (point_mult (getOrder #c -1 - 1) p0));
      lemma_point_equal_coeff_equal (scalar_as_nat #c scalar) (point_mult #c (scalar_as_nat #c scalar) p0) (getOrder #c -1 - 1) 
(point_mult (getOrder #c -1 - 1) p0);
      small_modulo_lemma_1 (scalar_as_nat #c scalar) o;
      small_modulo_lemma_1 ((getOrder #c -1 - 1)) o;

      assert (scalar_as_nat #c scalar == (getOrder #c -1 - 1));

      assert (scalar_as_nat #c scalar % 2 == 0);
      
      assert(~ (FStar.Math.Euclid.divides o 2));
	if (o % 2 = 0) then 
	begin
	  FStar.Math.Euclid.mod_divides o 2;
	  assert(False)
	end;

      assert (getOrder #c -1 - 1 % 2 == 1);

      assert(False)
    end



val scalar_rwnaf_to_invariant_lemma0_j: #c: curve 
  -> d: pos {d < pow2 (getPower c)}
  -> j: nat {j < v (getScalarLen c) / w} ->
  Lemma (
    let wf = (2 * (d / pow2 (w * j + 1)) + 1) % (2 * m) - m in 
    if wf >= 0 then wf >= 1 /\ wf < pow2 w else - wf >= 1 /\ -wf < pow2 w)

let scalar_rwnaf_to_invariant_lemma0_j #c d j = 
  let wf = (2 * (d / pow2 (w * j + 1)) + 1) % (2 * m) - m in 
  if ((2 * (d / pow2 (w * j + 1)) + 1) % (2 * m) = m) then 
    begin
      pow2_double_mult (w - 1);
      pow2_modulo_modulo_lemma_1 ((2 * (d / pow2 (w * j + 1)) + 1)) 1 (w + 1);
      assert(((2 * (d / pow2 (w * j + 1)) + 1) % 2 = 0)); 
      assert (False)
    end;

  if wf < 0 then 
    begin
      pow2_double_mult w;
      assert((2 * (d / pow2 (w * j + 1)) + 1) % (2 * m) - m >= - m);

      if ((2 * (d / pow2 (w * j + 1)) + 1) % (2 * m) = 0)  then 
      begin
        pow2_modulo_modulo_lemma_1 ((2 * (d / pow2 (w * j + 1)) + 1)) 1 (w + 1);
	assert(((2 * (d / pow2 (w * j + 1)) + 1) % 2 = 0));
	assert(False)
      end;
      
      assert ((2 * (d / pow2 (w * j + 1)) + 1) % (2 * m) - m > - pow2 w)
    end

val scalar_rwnaf_to_invariant_lemma0: #c: curve 
  -> d: pos {d < pow2 (getPower c)} -> 
  Lemma (
    forall (j: nat {j < v (getScalarLen c) / w}).
    let wf = (2 * (d / pow2 (w * j + 1)) + 1) % (2 * m) - m in 
    if wf >= 0 then wf >= 1 /\ wf < pow2 w else - wf >= 1 /\ -wf < pow2 w)

let scalar_rwnaf_to_invariant_lemma0 #c d = 
  Classical.forall_intro (scalar_rwnaf_to_invariant_lemma0_j #c d)


val scalar_rwnaf_to_invariant_lemma1: #c: curve 
  -> d: pos {d < pow2 (getPower c)} -> 
  Lemma (d / pow2 (getPower c / w * w + 1) * 2 + 1 < pow2 w /\ d / pow2 (getPower c / w * w + 1) * 2 + 1 >= 1)

let scalar_rwnaf_to_invariant_lemma1 #c d = 
  let n = getPower c in 

  lemma_div_lt_nat d n (n / w * w + 1);
  pow2_double_mult (n % w - 1);
  assert_norm (pow2 (n % w) + 1 < pow2 w)


val point_add_complete_last_step_lemma1: #c: curve -> d: uint64 {v d < pow2 (w - 1)} 
  -> p: Spec.ECC.point #c {~ (isPointAtInfinity #Jacobian p)} -> r: Spec.ECC.point #c -> Lemma 
  (requires (pointEqual p (point_mult #c (2 * v d + 1) (basePoint #c)))) 
  (ensures (
    let b = getDLP #c p in 
    pointEqual r (Spec.ECC.point_mult #c (- b) (basePoint #c)) ==> pointEqual r (point_mult (- (2 * v d + 1)) (basePoint #c))))

let point_add_complete_last_step_lemma1 #c d p r = 
  let b = getDLP #c p in 
    assert_norm (2 * v d + 1 < getOrder #c);
    FStar.Math.Lemmas.small_mod (2 * v d + 1) (getOrder #c); 
  dlp_mod_order p (2 * v d + 1);
  if pointEqual r (Spec.ECC.point_mult #c (- b) (basePoint #c)) then 
    assert (pointEqual r (point_mult (- (2 * v d + 1)) (basePoint #c)))


val point_add_complete_last_step_main_lemma0: #c: curve 
  -> rnaf: Lib.Sequence.lseq uint64  (2 * (v (getScalarLen c) / w + 1)) 
  -> s: Lib.Sequence.seq int ->
  Lemma 
  (requires (rnaf_to_spec #c rnaf  == s))
  (ensures (
    let ri = Lib.Sequence.index rnaf 0 in 
    let sign = Lib.Sequence.index rnaf 1 in
    if v sign = 0 then 
      Seq.index s 0 == v ri
    else 
      Seq.index  s 0 == - (v ri)))

let point_add_complete_last_step_main_lemma0 #c rnaf s = 
  assert(rnaf_to_spec #c rnaf == s);

  assert(forall (i: nat). i < Seq.length s ==> (
      let ri = Lib.Sequence.index rnaf (2 * i) in 
      let sign = Lib.Sequence.index rnaf (2 * i + 1) in 
      if v sign = 0 then 
  Lib.Sequence.index #_ #(v (getLenWnaf #c) + 1) s i == v ri
      else 
  Lib.Sequence.index #_ #(v (getLenWnaf #c) + 1) s i == - (v ri)));

  assert(
    let ri = Lib.Sequence.index rnaf 0 in 
    let sign = Lib.Sequence.index rnaf 1 in 
    if v sign = 0 then 
      Seq.index s 0 == v ri
    else 
      Seq.index  s 0 == - (v ri))
  

val point_add_complete_last_step_main_lemma1: #c: curve -> s: scalar_bytes #c 
  -> rnaf: Lib.Sequence.lseq uint64 (2 * (v (getScalarLen c) / w + 1)) -> Lemma
  (requires (
    let d = scalar_as_nat s in
    let n = v (getScalarLen c) in 
    d < pow2 n /\ rnaf_to_spec #c rnaf == to_wnaf n (scalarToOdd n d)))
  (ensures (
    let d = scalar_as_nat s in
    let n = v (getScalarLen c) in 
    let s = to_wnaf n (scalarToOdd n d) in 
    let d = Seq.index s 0 in 
    - d - 1 = (- d - 1) / 2 * 2 /\ (d - 1) = (d - 1) / 2 * 2))
    
let point_add_complete_last_step_main_lemma1 #c s rnaf = 
  let d = scalar_as_nat s in
  let n = v (getScalarLen c) in 
  let s = to_wnaf n (scalarToOdd n d) in 
  let d0 = Seq.index s 0 in 
  let open FStar.Math.Lemmas in 

  lemma_all_elements_rwnaf_odd n (scalarToOdd n d) 0;
  euclidean_division_definition (- d0 - 1) 2;
  euclidean_division_definition (d0 - 1) 2


val lemma_3: #c: curve 
  -> rnaf: Lib.Sequence.lseq uint64 (2 * (v (getScalarLen c) / w + 1)) 
  -> s: scalar_bytes #c  -> j: nat {j < getPower c / w + 1} -> r: Spec.ECC.point #c -> k: Spec.ECC.point #c ->
  Lemma 
  (requires (
    let d = scalar_as_nat #c s in
    let n = v (getScalarLen c) in 
    d < pow2 n /\ rnaf_to_spec #c rnaf == to_wnaf n (scalarToOdd n d) /\ (
    let rnaf_2j = v (Lib.Sequence.index rnaf (2 * j)) in 
    let is_neg_rnaf_2j = v (Lib.Sequence.index rnaf (2 * j + 1)) in 
    let b = 
      if is_neg_rnaf_2j = 0 then 
	(pow2 (j * w) * ((rnaf_2j - 1) / 2 * 2 + 1) % getOrder #c) 
      else 
        - (pow2 (j * w) * ((rnaf_2j - 1) / 2 * 2 + 1) % getOrder #c) in
    pointEqual r (pointAdd #c k (point_mult #c b (basePoint #c))))))
  (ensures (
    let n = getPower c in 
    let d = scalar_as_nat s in
    let s = to_wnaf n (scalarToOdd n d) in 
    pointEqual r (pointAdd #c k (point_mult #c (pow2 (j * w) * Seq.index s j) (basePoint #c)))))

let lemma_3 #c rnaf s j r k = 
  let d = scalar_as_nat #c s in
  let n = v (getScalarLen c) in 
  let rnaf_2j = v (Lib.Sequence.index rnaf (2 * j)) in 
  let is_neg_rnaf_2j = v (Lib.Sequence.index rnaf (2 * j + 1)) in 
  let b = 
      if is_neg_rnaf_2j = 0 then 
	(pow2 (j * w) * ((rnaf_2j - 1) / 2 * 2 + 1) % getOrder #c) 
      else 
        - (pow2 (j * w) * ((rnaf_2j - 1) / 2 * 2 + 1) % getOrder #c) in

  lemma_all_elements_rwnaf_odd n d j;
  let s = to_wnaf n (scalarToOdd n d) in 
  if is_neg_rnaf_2j = 0 then 
    begin
      assert(b == (pow2 (j * w) * (Seq.index s j) % getOrder #c))
    end
  else
    begin
      lemma_scalar_reduce_neg #c (basePoint #c) (pow2 (j * w)) (Seq.index s j); 
      assert(point_mult #c b (basePoint #c) == 
	point_mult ((pow2 (j * w) * (Seq.index s j) % getOrder #c)) (basePoint #c))
    end;
  lemma_scalar_reduce #c (basePoint #c) (pow2 (j * w) * (Seq.index s j))


val scalar_multiplication_cmb_last_bit_lemma0: #c: curve -> scalar: scalar_bytes #c ->  Lemma
  (scalar_as_nat #c scalar % 2 == v (Lib.Sequence.index scalar (v (getScalarLenBytes c) - 1)) % 2)

let scalar_multiplication_cmb_last_bit_lemma0 #c scalar = 
  Hacl.Impl.EC.Masking.ScalarAccess.Lemmas.lemma_index_scalar_as_nat scalar (v (getScalarLenBytes c) - 1);
  pow2_modulo_modulo_lemma_1 (scalar_as_nat #c scalar) 1 8;
  assert(v (Lib.Sequence.index scalar (v (getScalarLenBytes c) - 1)) % 2 == scalar_as_nat #c scalar % 2)
