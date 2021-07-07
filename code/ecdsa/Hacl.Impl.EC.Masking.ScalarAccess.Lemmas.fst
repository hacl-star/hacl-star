module Hacl.Impl.EC.Masking.ScalarAccess.Lemmas

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Spec.ECC
open Spec.ECC.Curves

open FStar.Mul
module BV = FStar.BitVector
open FStar.Math.Lemmas


#set-options "--fuel 0 --ifuel 0 --z3rlimit 200"

inline_for_extraction noextract
val get_high_part: a:uint64 -> r:uint32{uint_v r == uint_v a / pow2 32}
let get_high_part a = to_u32 (shift_right a (size 32))

inline_for_extraction noextract
val get_high_part_28: a:uint32 -> r:uint32{uint_v r == uint_v a / pow2 4}
let get_high_part_28 a = to_u32 (shift_right a (size 4))


inline_for_extraction noextract
val get_low_part: a:uint64 -> r:uint32{uint_v r == uint_v a % pow2 32}
let get_low_part a = to_u32 a


inline_for_extraction noextract
val get_low_part_4: a:uint32 -> r:uint8{uint_v r == uint_v a % pow2 4}
let get_low_part_4 a = logand_mask a (u32 0xf) 4; to_u8 (logand a (u32 0xf))


val append_uint: #n1:nat -> #n2:nat
  -> num1:UInt.uint_t n1 -> num2:UInt.uint_t n2 -> UInt.uint_t (n1 + n2)

val shift_bound: #n:nat -> num:UInt.uint_t n -> n':nat ->
  Lemma (num * pow2 n' <= pow2 (n' + n) - pow2 n')

let shift_bound #n num n' =
  Math.Lemmas.lemma_mult_le_right (pow2 n') num (pow2 n - 1);
  Math.Lemmas.distributivity_sub_left (pow2 n) 1 (pow2 n');
  Math.Lemmas.pow2_plus n' n


let append_uint #n1 #n2 num1 num2 =
  shift_bound num2 n1;
  num1 + num2 * pow2 n1

val to_vec_append : #n1:pos-> #n2:pos -> num1:UInt.uint_t n1 -> num2:UInt.uint_t n2 ->
  Lemma (UInt.to_vec (append_uint num1 num2) ==
         Seq.append (UInt.to_vec num2) (UInt.to_vec num1))

let to_vec_append #n1 #n2 num1 num2 =
  UInt.append_lemma (UInt.to_vec num2) (UInt.to_vec num1)

val to_vec_low_high: a:UInt.uint_t 64 -> Lemma
  (UInt.to_vec a ==
   Seq.append (UInt.to_vec #32 (a / pow2 32)) (UInt.to_vec #32 (a % pow2 32)))

let to_vec_low_high a =
  assert (a == append_uint #32 #32 (a % pow2 32) (a / pow2 32));
  to_vec_append #32 #32 (a % pow2 32) (a / pow2 32)


val to_vec_low_high_4: a:UInt.uint_t 32 -> Lemma ( 
  FStar.Math.Lemmas.pow2_minus 32 4; 
  UInt.to_vec a == Seq.append (UInt.to_vec #28 (a / pow2 4)) (UInt.to_vec #4 (a % pow2 4)))

let to_vec_low_high_4 a =
  FStar.Math.Lemmas.pow2_minus 32 4; 
  assert (a == append_uint #4 #28 (a % pow2 4) (a / pow2 4));
  to_vec_append #4 #28 (a % pow2 4) (a / pow2 4)


val logand_vec_append (#n1 #n2: pos) (a1 b1: BV.bv_t n1) (a2 b2: BV.bv_t n2) :
  Lemma (Seq.append (BV.logand_vec a1 b1) (BV.logand_vec a2 b2) ==
         BV.logand_vec #(n1 + n2) (FStar.Seq.append a1 a2) (FStar.Seq.append b1 b2))

let logand_vec_append #n1 #n2 a1 b1 a2 b2 =
  Seq.lemma_eq_intro (Seq.append (BV.logand_vec a1 b1) (BV.logand_vec a2 b2))
                     (BV.logand_vec #(n1 + n2) (Seq.append a1 a2) (Seq.append b1 b2))


val lemma_and_both_parts: a: uint64 -> b: uint64 -> Lemma (
  let a0, a1 = get_low_part a, get_high_part a in 
  let b0, b1 = get_low_part b, get_high_part b in 
  v (logand a1 b1) * pow2 32 + v (logand a0 b0) == v (logand a b))

let lemma_and_both_parts a b = 
  to_vec_low_high (v a);
  to_vec_low_high (v b);
    let a0, a1 = get_low_part a, get_high_part a in 
    let b0, b1 = get_low_part b, get_high_part b in 


  let a0_ = UInt.to_vec #32 (v a0) in
  let a1_ = UInt.to_vec #32 (v a1) in


  let b0_ = UInt.to_vec #32 (v b0) in
  let b1_ = UInt.to_vec #32 (v b1) in
  
  assert(UInt.to_vec #64 (v a) == Seq.append a1_ a0_);
  assert(UInt.to_vec #64 (v b) == Seq.append b1_ b0_);
  

  logand_vec_append a1_ b1_ a0_ b0_;

  assert(Seq.append (BV.logand_vec a1_ b1_) (BV.logand_vec a0_ b0_) ==
         BV.logand_vec #64  (FStar.Seq.append a1_ a0_) (FStar.Seq.append b1_ b0_));

  UInt.append_lemma a1_ a0_;
  UInt.append_lemma b1_ b0_;
  assert( (Seq.append a1_ a0_) == UInt.to_vec #64 (v a));
  assert(UInt.from_vec #64 (Seq.append b1_ b0_) == v b);


  assert( (Seq.append (BV.logand_vec a1_ b1_) (BV.logand_vec a0_ b0_)) ==
          (BV.logand_vec #64 (UInt.to_vec #64 (v a)) (UInt.to_vec #64 (v b))));


  logand_spec a b;
  assert(UInt.from_vec (BV.logand_vec #64 (UInt.to_vec #64 (v a)) (UInt.to_vec #64 (v b))) == v (logand a b));
  
  logand_spec a1 b1;
  assert(UInt.from_vec (BV.logand_vec #32 (UInt.to_vec #32 (v a1)) (UInt.to_vec #32 (v b1))) == v (logand a1 b1));
  logand_spec a0 b0;
  assert(UInt.from_vec (BV.logand_vec #32 (UInt.to_vec #32 (v a0)) (UInt.to_vec #32 (v b0))) == v (logand a0 b0));
  

  UInt.append_lemma (BV.logand_vec a1_ b1_) (BV.logand_vec a0_ b0_);
  assert(v (logand a1 b1) * pow2 32 + v (logand a0 b0) == v (logand a b))


let zero_extend_vec (#n:pos) (#n2: nat) (a:BitVector.bv_t n): Tot (BitVector.bv_t (n + n2)) = Seq.append (Seq.create n2 false) a

let zero_extend (#n:pos) (#n2: nat) (a:UInt.uint_t n): Tot (UInt.uint_t (n+n2)) = UInt.from_vec (zero_extend_vec (UInt.to_vec #n a))


val lemma_zero_extend: #n:pos -> #n2: pos -> a:UInt.uint_t n ->
  Lemma (zero_extend #n #n2 a = a)

let rec lemma_zero_extend #n #n2 a = 
  match n2 with 
  |1 -> UInt.lemma_zero_extend a
  |_ -> 
    let a_vec = UInt.to_vec #n a in 
    
    lemma_zero_extend #n #(n2 - 1) a;
    
    let f: BV.bv_t (n + n2 - 1) = Seq.append (Seq.create (n2 - 1) false) (UInt.to_vec #n a) in 
    let f1: BV.bv_t (n + n2) = Seq.append (Seq.create 1 false) f in 
    UInt.inverse_vec_lemma f;

    let k = zero_extend_vec #n #(n2 - 1) (UInt.to_vec #n a) in 
    assert(k == Seq.append (Seq.create (n2 - 1) false) (UInt.to_vec #n a));


    UInt.append_lemma #n2 #n (Seq.create n2 false) a_vec;
    UInt.append_lemma #(n2 - 1) #n (Seq.create (n2 - 1) false) a_vec;
    
    UInt.zero_from_vec_lemma #n2;
    UInt.zero_from_vec_lemma #(n2 - 1)


#push-options "--fuel 1"

val lemma_logand_zero: n: pos -> Lemma (let zero = UInt.to_vec #n 0 in BV.logand_vec zero zero = Seq.create n false)

let rec lemma_logand_zero n = 
  match n with 
  |1 -> ()
  |_ -> lemma_logand_zero (n - 1);
    let zero_1 = UInt.to_vec #(n - 1) 0 in 
    let zero = UInt.to_vec #n 0 in

    assert (Seq.equal (Seq.create n false) (Seq.append (Seq.create 1 false) (Seq.create (n - 1) false)));
    assert (BV.logand_vec zero_1 zero_1 = Seq.create (n - 1) false);


    let r0 = Seq.append (Seq.create 1 false) (BV.logand_vec zero_1 zero_1) in 
    let r1 = BV.logand_vec zero zero in 
     
    BV.logand_vec_definition zero zero 0;
    UInt.zero_nth_lemma #n 0;

    Seq.lemma_split r0 1;
    assert (Seq.equal r0 r1)


#pop-options

 
val lemma_and_both_parts_32: a: uint32 -> b: uint32 -> Lemma (
  let a0, a1 = get_low_part_4 a, get_high_part_28 a in 
  let b0, b1 = get_low_part_4 b, get_high_part_28 b in 
  v (logand a1 b1) * pow2 4 + v (logand a0 b0) == v (logand a b) /\ 
  UInt.logand #32 (v a1) (v b1) * pow2 4 + UInt.logand #4 (v a0) (v b0) == v (logand a b))

let lemma_and_both_parts_32 a b = 
  to_vec_low_high_4 (v a);
  to_vec_low_high_4 (v b);

  FStar.Math.Lemmas.pow2_minus 32 4; 
  
  let a0, a1 = get_low_part_4 a, get_high_part_28 a in 
  let b0, b1 = get_low_part_4 b, get_high_part_28 b in 

  let a0_ = UInt.to_vec #4 (v a0) in
  let a1_ = UInt.to_vec #28 (v a1) in

  let b0_ = UInt.to_vec #4 (v b0) in
  let b1_ = UInt.to_vec #28 (v b1) in

  logand_vec_append a1_ b1_ a0_ b0_;


  UInt.append_lemma a1_ a0_;
  UInt.append_lemma b1_ b0_;

  assert( (Seq.append (BV.logand_vec a1_ b1_) (BV.logand_vec a0_ b0_)) ==
          (BV.logand_vec #32 (UInt.to_vec #32 (v a)) (UInt.to_vec #32 (v b))));

  logand_spec a b;
  logand_spec a0 b0;
  logand_spec a1 b1;

  let zero = UInt.to_vec #4 0 in 

  to_vec_append #28 #4 (v a1) 0;
  to_vec_append #28 #4 (v b1) 0;


  logand_vec_append zero zero  (UInt.to_vec #28 (v a1)) (UInt.to_vec #28 (v b1));

  calc (==) {
    UInt.from_vec (BV.logand_vec #32 (Seq.append zero (UInt.to_vec #28 (v a1))) (Seq.append zero (UInt.to_vec #28 (v b1))));
      (==) {}
    UInt.from_vec (Seq.append (BV.logand_vec zero zero) (BV.logand_vec (UInt.to_vec #28 (v a1)) (UInt.to_vec #28 (v b1))));
      (==) {lemma_logand_zero 4}
    UInt.from_vec (zero_extend_vec #28 #4 (BV.logand_vec (UInt.to_vec #28 (v a1)) (UInt.to_vec #28 (v b1))));
      (==) {lemma_zero_extend #28 #4 (UInt.from_vec (BV.logand_vec (UInt.to_vec #28 (v a1)) (UInt.to_vec #28 (v b1))))}
    UInt.from_vec #28 (BV.logand_vec (UInt.to_vec #28 (v a1)) (UInt.to_vec #28 (v b1)));  
  };


  let zero = UInt.to_vec #4 0 in 

  to_vec_append #4 #4 (v a0) 0;
  to_vec_append #4 #4 (v b0) 0;
  
  logand_vec_append zero zero  (UInt.to_vec #4 (v a0)) (UInt.to_vec #4 (v b0));

  calc (==) {
    UInt.from_vec (BV.logand_vec #8 (Seq.append zero (UInt.to_vec #4 (v a0))) (Seq.append zero (UInt.to_vec #4 (v b0))));
      (==) {}
    UInt.from_vec (Seq.append (BV.logand_vec zero zero) (BV.logand_vec (UInt.to_vec #4 (v a0)) (UInt.to_vec #4 (v b0))));
      (==) {lemma_logand_zero 4}
    UInt.from_vec (zero_extend_vec #4 #4 (BV.logand_vec (UInt.to_vec #4 (v a0)) (UInt.to_vec #4 (v b0))));
      (==) {lemma_zero_extend #4 #4 (UInt.from_vec (BV.logand_vec (UInt.to_vec #4 (v a0)) (UInt.to_vec #4 (v b0))))}
    UInt.from_vec #4 (BV.logand_vec (UInt.to_vec #4 (v a0)) (UInt.to_vec #4 (v b0)));
  };


  UInt.append_lemma (BV.logand_vec a1_ b1_) (BV.logand_vec a0_ b0_)


assume val lemma_xor_of_4: bit0: uint64 {v bit0 <= 1} -> bit1: uint64 {v bit1 <= 1} 
  -> bit2: uint64 {v bit2 <= 1} -> bit3: uint64 {v bit3 <= 1} -> 
  Lemma (logxor_v (logxor_v (v bit0 * 8) (v bit1 * 4)) (logxor_v #U64 (v bit2 * 2) (v bit3)) == v bit0 * 8 + v bit1 * 4 + v bit2 * 2 + v bit3)


val scalar_as_nat_upperbound: #c: curve -> s: scalar_bytes #c -> i: nat {i <= v (getScalarLen c)} -> Lemma
  (scalar_as_nat_ s i < pow2 i)

let rec scalar_as_nat_upperbound #c s i = 
  match i with 
  |0 -> scalar_as_nat_zero s
  |_ -> 
    scalar_as_nat_upperbound #c s (i - 1);
    scalar_as_nat_def s i;
    pow2_double_sum (i - 1)


val test__:  #c: curve -> s: scalar_bytes #c -> i: nat {i > 0 /\ i < v (getScalarLen c)} -> Lemma (
  let len = v (getScalarLen c) in 
  scalar_as_nat_ s (len - i + 1) / 2 == scalar_as_nat_ s len / pow2 i)

let rec test__ #c s i = 
  match i with 
  |1 -> ()
  |_ -> 
    let len = v (getScalarLen c) in 
    test__ #c s (i - 1); 
    scalar_as_nat_def s (len - i + 1 + 1);
    pow2_modulo_division_lemma_1 (2 * scalar_as_nat_ s (len - i + 1)) 1 2;
    modulo_scale_lemma (scalar_as_nat_ s (len - i + 1)) 2 2;

    division_multiplication_lemma (scalar_as_nat_ s len) (pow2 (i - 1)) 2;
    pow2_double_mult (i - 1)

val test_:  #c: curve -> s: scalar_bytes #c -> i: nat {i < v (getScalarLen c)} -> Lemma (
  v (ith_bit s i) == scalar_as_nat s / pow2 i % 2)

let rec test_ #c s i = 
  match i with 
  |0 -> 
    scalar_as_nat_def s (v (getScalarLen c))
  |_ -> 
    let len = v (getScalarLen c) in 
    scalar_as_nat_def s (len - (i - 1));
    scalar_as_nat_def s (len - i);

    test_ s (i - 1);
    test__ s i

val test:  #c: curve -> s: scalar_bytes #c -> i: nat {i <= v (getScalarLen c)} -> Lemma (
  scalar_as_nat s / pow2 (v (getScalarLen c) - i) == scalar_as_nat_ #c s i)

let rec test #c s i = 
  match i with 
  |0 -> 
    scalar_as_nat_upperbound s (v (getScalarLen c));
    scalar_as_nat_zero s
  |_ -> 
    test s (i - 1);
    scalar_as_nat_def s i;
      assert(scalar_as_nat_ s i == 2 * scalar_as_nat_ s (i - 1) + v (ith_bit s (v (getScalarLen c) - i)));
    euclidean_division_definition (scalar_as_nat s / pow2 (v (getScalarLen c) - i)) 2;
      assert(scalar_as_nat s / pow2 (v (getScalarLen c) - i) == scalar_as_nat s / pow2 (v (getScalarLen c) - i) / 2 * 2 + scalar_as_nat s / pow2 (v (getScalarLen c) - i) % 2);
    division_multiplication_lemma (scalar_as_nat s) (pow2 (v (getScalarLen c) - i)) 2; 
      assert(scalar_as_nat s / pow2 (v (getScalarLen c) - i) == scalar_as_nat s / (pow2 (v (getScalarLen c) - i) * 2) * 2 + scalar_as_nat s / pow2 (v (getScalarLen c) - i) % 2);
    pow2_double_mult (v (getScalarLen c) - i); 
      assert(scalar_as_nat s / pow2 (v (getScalarLen c) - i) == scalar_as_nat s / pow2 (v (getScalarLen c) - i + 1) * 2 + scalar_as_nat s / pow2 (v (getScalarLen c) - i) % 2);

      assert(scalar_as_nat s / pow2 (v (getScalarLen c) - i) == scalar_as_nat_ s i 
	- v (ith_bit s (v (getScalarLen c) - i)) + scalar_as_nat s / pow2 (v (getScalarLen c) - i) % 2);

    test_ #c s (v (getScalarLen c) - i)


val scalar_as_sub_radix4: #c: curve -> s: scalar_bytes #c -> i: nat {4 * i + 4 <= v (getScalarLen c)} -> 
  Lemma (let l = v (getScalarLen c) in 
  (scalar_as_nat s / pow2 (l - (i + 1) * 4)) % pow2 4 == scalar_as_nat_ #c s (4 * i + 4) - 16 * scalar_as_nat_ #c s (4 * i))

let rec scalar_as_sub_radix4 #c s i =
  let l = v (getScalarLen c) in 
  match i with 
  |0 ->
    scalar_as_nat_zero #c s;  
    scalar_as_nat_def #c s 4;
    scalar_as_nat_def #c s l;
    test s 4;
    scalar_as_nat_upperbound s 4;
    small_mod (scalar_as_nat_ #c s 4) (pow2 4)
  |_ -> admit()



assume val lemma_index_scalar_as_nat: #c: curve -> s: scalar_bytes #c -> i: size_nat {i < v (getScalarLenBytes c)} ->
  Lemma (v (Lib.Sequence.index s i) == scalar_as_nat #c s / pow2 (v (getScalarLen c) - (i + 1) * 8) % pow2 8)
