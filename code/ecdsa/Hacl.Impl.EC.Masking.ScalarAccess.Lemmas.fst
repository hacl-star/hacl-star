module Hacl.Impl.EC.Masking.ScalarAccess.Lemmas

open Lib.IntTypes

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
    UInt.from_vec #4 (BV.logand_vec (UInt.to_vec #4 (v a0)) (UInt.to_vec #4 (v b0)));};
  UInt.append_lemma (BV.logand_vec a1_ b1_) (BV.logand_vec a0_ b0_)


val lemma_xor_of_4: bit0: uint64 {v bit0 <= 1} -> bit1: uint64 {v bit1 <= 1} -> bit2: uint64 {v bit2 <= 1} -> bit3: uint64 {v bit3 <= 1} -> 
  Lemma (logxor_v (logxor_v (v bit0 * 8) (v bit1 * 4)) (logxor_v #U64 (v bit2 * 2) (v bit3)) == v bit0 * 8 + v bit1 * 4 + v bit2 * 2 + v bit3)



val get_high_part_n: #n: pos {n < 64} -> a:uint64 -> r:uint64 {uint_v r == uint_v a / pow2 n}

let get_high_part_n #n a = shift_right a (size n)


val get_low_part_n: #n: pos {n < 64} -> a:uint64 -> r:uint64 {uint_v r == uint_v a % pow2 n}

let get_low_part_n #n a =
  pow2_lt_compat 64 n;
  let mask = u64 (pow2 n - 1) in 
  logand_mask a mask n;
  to_u64 (logand a mask)


val to_vec_low_high_n: #n: pos {n < 64} -> a:UInt.uint_t 64 -> Lemma ( 
  lemma_div_lt_nat a 64 n;
  UInt.to_vec a == Seq.append (UInt.to_vec #(64 - n) (a / pow2 n)) (UInt.to_vec #n (a % pow2 n)))

let to_vec_low_high_n #n a =
  lemma_div_lt_nat a 64 n;
  assert (a == append_uint #n #(64 - n) (a % pow2 n) (a / pow2 n));
  to_vec_append #n #(64 - n) (a % pow2 n) (a / pow2 n)


val logxor_vec_append (#n1 #n2: pos) (a1 b1: BV.bv_t n1) (a2 b2: BV.bv_t n2) :
  Lemma (Seq.append (BV.logxor_vec a1 b1) (BV.logxor_vec a2 b2) ==
         BV.logxor_vec #(n1 + n2) (FStar.Seq.append a1 a2) (FStar.Seq.append b1 b2))

let logxor_vec_append #n1 #n2 a1 b1 a2 b2 =
  Seq.lemma_eq_intro (Seq.append (BV.logxor_vec a1 b1) (BV.logxor_vec a2 b2))
                     (BV.logxor_vec #(n1 + n2) (Seq.append a1 a2) (Seq.append b1 b2))

val lemma_xor_zero:
  #n: pos {n < 64}
  -> low: uint64{v (get_high_part_n #n low) == 0}
  -> high: uint64{v (get_low_part_n #n high) == 0}
  -> Lemma (v (logxor low high) = v high + v low)


let lemma_xor_zero #n a b = 
  to_vec_low_high_n #n (v a);
  to_vec_low_high_n #n (v b);

  let l1: pos = 64 - n in 
  
  FStar.Math.Lemmas.pow2_minus 64 n; 

  let a0, a1 = get_low_part_n #n a, get_high_part_n #n a in 
  let b0, b1 = get_low_part_n #n b, get_high_part_n #n b in 

  lemma_div_lt_nat (v b) 64 n;

  let a0_, a1_ = UInt.to_vec #n (v a0), UInt.to_vec #l1 (v a1) in
  let b0_, b1_ = UInt.to_vec #n (v b0), UInt.to_vec #l1 (v b1) in


  logxor_vec_append #l1 #n a1_ b1_ a0_ b0_;
  
  assert(Seq.append (BV.logxor_vec #l1 a1_ b1_) (BV.logxor_vec #n a0_ b0_) == BV.logxor_vec #64 (Seq.append a1_ a0_) (Seq.append b1_ b0_));

  assert(UInt.from_vec #64 (Seq.append a1_ a0_) == v a1 * pow2 n + v a0);
  assert(UInt.from_vec #64 (Seq.append b1_ b0_) == v b1 * pow2 n + v b0);

  assert(UInt.from_vec #64 (Seq.append a1_ a0_) == v a0);
  assert(UInt.from_vec #64 (Seq.append b1_ b0_) == v b1 * pow2 n);   

  assert(Seq.append a1_ a0_ == UInt.to_vec #64 (v a0));
  assert(Seq.append b1_ b0_ == UInt.to_vec #64 (v b1 * pow2 n)); 

  logxor_spec a b;

  assert(UInt.from_vec #64 (Seq.append (BV.logxor_vec #l1 a1_ b1_) (BV.logxor_vec #n a0_ b0_)) == v (logxor a b));

  UInt.append_lemma (BV.logxor_vec #l1 a1_ b1_) (BV.logxor_vec #n a0_ b0_);

  assert(UInt.from_vec #64 (Seq.append (BV.logxor_vec #l1 a1_ b1_) (BV.logxor_vec #n a0_ b0_)) ==
    UInt.from_vec (BV.logxor_vec #l1 (UInt.to_vec #l1 (v a1)) (UInt.to_vec #l1 (v b1))) * pow2 n + 
    UInt.from_vec (BV.logxor_vec #n a0_ b0_));

  assert(UInt.from_vec #64 (Seq.append (BV.logxor_vec #l1 a1_ b1_) (BV.logxor_vec #n a0_ b0_)) ==
    UInt.logxor #l1 0 (v b1) * pow2 n + UInt.logxor #n (v a0) 0);

  UInt.logxor_lemma_1 #l1 (v b1);
  UInt.logxor_commutative #l1 (v b1) 0;

  UInt.logxor_lemma_1 #n (v a0);
  UInt.logxor_commutative #n (v a0) 0;

  assert(UInt.from_vec #64 (Seq.append (BV.logxor_vec #l1 a1_ b1_) (BV.logxor_vec #n a0_ b0_)) == v b + v a)



val lemma_xor_n: 
  #n: pos {n < 32} ->
  high: uint64 {v (get_low_part_n #n high) == 0} -> 
  low:  uint64 {v (get_high_part_n #n low) == 0} -> 
  Lemma (FStar.UInt.logxor #64 (v high) (v low) = v high + v low /\ FStar.UInt.logxor #64 (v low) (v high) = v high + v low)

let lemma_xor_n #n a b = 
  lemma_xor_zero #n b a; 
  logxor_spec b a;
  FStar.UInt.logxor_commutative #64 (v b) (v a)


let lemma_xor_of_4 bit0 bit1 bit2 bit3 = 
  let open FStar.UInt in 
  let open FStar.BitVector in 
    FStar.UInt.logxor_lemma_1 #64 0;
    FStar.UInt.logxor_lemma_1 #64 1;
    FStar.UInt.logxor_lemma_1 #64 2;
    FStar.UInt.logxor_lemma_1 #64 3;
    FStar.UInt.logxor_lemma_1 #64 4;
    FStar.UInt.logxor_lemma_1 #64 8;
    FStar.UInt.logxor_lemma_1 #64 12;

    FStar.UInt.logxor_commutative #64 0 1; 
    FStar.UInt.logxor_commutative #64 0 2; 
    FStar.UInt.logxor_commutative #64 0 3; 
    FStar.UInt.logxor_commutative #64 0 4; 

  lemma_xor_n #1 (u64 2) (u64 1);
    assert_norm(1 / pow2 62 == 0);
    assert_norm(2 / pow2 62 == 0);
    assert_norm(3 / pow2 62 == 0);
  lemma_xor_n #2 (u64 4) (u64 1);
  lemma_xor_n #2 (u64 4) (u64 2);
  lemma_xor_n #2 (u64 4) (u64 3);

  assert_norm(1 / pow2 61 == 0);
  assert_norm(2 / pow2 61 == 0);
  assert_norm(3 / pow2 61 == 0);
  assert_norm(4 / pow2 61 == 0);
    
  lemma_xor_n #3 (u64 8) (u64 1);
  lemma_xor_n #3 (u64 8) (u64 2);
  lemma_xor_n #3 (u64 8) (u64 3);
  lemma_xor_n #3 (u64 8) (u64 4);


  assert_norm(1 / pow2 60 == 0);
  assert_norm(2 / pow2 60 == 0);
  assert_norm(3 / pow2 60 == 0);
  
  lemma_xor_n #2 (u64 12) (u64 1);
  lemma_xor_n #2 (u64 12) (u64 2);
  lemma_xor_n #2 (u64 12) (u64 3)
    


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



val lemma_index_as_ith_: a: nat {a < pow2 8} 
  -> a7: nat {a7 = a / pow2 7 % 2} 
  -> a6: nat {a6 = a / pow2 6 % 2} 
  -> a5: nat {a5 = a / pow2 5 % 2} 
  -> a4: nat {a4 = a / pow2 4 % 2} 
  -> a3: nat {a3 = a / pow2 3 % 2} 
  -> a2: nat {a2 = a / pow2 2 % 2} 
  -> a1: nat {a1 = a / pow2 1 % 2} 
  -> a0: nat {a0 = a / pow2 0 % 2} 
  -> Lemma (a = a7 * pow2 7 + a6 * pow2 6 + a5 * pow2 5 + a4 * pow2 4 + a3 * pow2 3 + a2 * pow2 2 + a1 * pow2 1 + a0 * pow2 0)


let lemma_index_as_ith_ a a7 a6 a5 a4 a3 a2 a1 a0 = 
  euclidean_division_definition a (pow2 7);
  lemma_div_lt_nat a 8 7;
  small_mod (a / pow2 7) 2;

  euclidean_division_definition (a % pow2 7) (pow2 6);
  pow2_modulo_division_lemma_1 a 6 7;
  pow2_modulo_modulo_lemma_1 a 6 7;

  euclidean_division_definition (a % pow2 6) (pow2 5);
  pow2_modulo_division_lemma_1 a 5 6;
  pow2_modulo_modulo_lemma_1 a 5 6;

  euclidean_division_definition (a % pow2 5) (pow2 4);
  pow2_modulo_division_lemma_1 a 4 5;
  pow2_modulo_modulo_lemma_1 a 4 5;

  euclidean_division_definition (a % pow2 4) (pow2 3);
  pow2_modulo_division_lemma_1 a 3 4;
  pow2_modulo_modulo_lemma_1 a 3 4;

  euclidean_division_definition (a % pow2 3) (pow2 2);
  pow2_modulo_division_lemma_1 a 2 3;
  pow2_modulo_modulo_lemma_1 a 2 3;

  euclidean_division_definition (a % pow2 2) (pow2 1);
  pow2_modulo_division_lemma_1 a 1 2;
  pow2_modulo_modulo_lemma_1 a 1 2;

  euclidean_division_definition (a % pow2 1) (pow2 0);
  pow2_modulo_division_lemma_1 a 0 1;
  pow2_modulo_modulo_lemma_1 a 0 1


val lemma_index_as_ith: #c: curve -> s: scalar_bytes #c -> i: size_nat {i < v (getScalarLenBytes c)} -> 
  Lemma (
    let l = v (getScalarLen c) in 
    v (Lib.Sequence.index s i) == 
    pow2 0 * v (ith_bit s (l - 8 * i - 8)) + 
    pow2 1 * v (ith_bit s (l - 8 * i - 7)) + 
    pow2 2 * v (ith_bit s (l - 8 * i - 6)) + 
    pow2 3 * v (ith_bit s (l - 8 * i - 5)) + 
    pow2 4 * v (ith_bit s (l - 8 * i - 4)) +
    pow2 5 * v (ith_bit s (l - 8 * i - 3)) + 
    pow2 6 * v (ith_bit s (l - 8 * i - 2)) + 
    pow2 7 * v (ith_bit s (l - 8 * i - 1)))


let lemma_index_as_ith #c s i = 
  let l = v (getScalarLen c) in 

  
  logand_mask (Lib.Sequence.index s i >>. size 7) (u8 1) 1;
  logand_mask (Lib.Sequence.index s i >>. size 6) (u8 1) 1;
  logand_mask (Lib.Sequence.index s i >>. size 5) (u8 1) 1;
  logand_mask (Lib.Sequence.index s i >>. size 4) (u8 1) 1;
  logand_mask (Lib.Sequence.index s i >>. size 3) (u8 1) 1;
  logand_mask (Lib.Sequence.index s i >>. size 2) (u8 1) 1;
  logand_mask (Lib.Sequence.index s i >>. size 1) (u8 1) 1;
  logand_mask (Lib.Sequence.index s i >>. size 0) (u8 1) 1;

  let a7 = v (ith_bit s (l - 8 * i - 1)) in 
  let a6 = v (ith_bit s (l - 8 * i - 2)) in 
  let a5 = v (ith_bit s (l - 8 * i - 3)) in 
  let a4 = v (ith_bit s (l - 8 * i - 4)) in 
  let a3 = v (ith_bit s (l - 8 * i - 5)) in 
  let a2 = v (ith_bit s (l - 8 * i - 6)) in 
  let a1 = v (ith_bit s (l - 8 * i - 7)) in 
  let a0 = v (ith_bit s (l - 8 * i - 8)) in 

  assert(a7 ==  v (Lib.Sequence.index s i) / pow2 7 % 2);
  assert(a6 ==  v (Lib.Sequence.index s i) / pow2 6 % 2); 
  assert(a5 ==  v (Lib.Sequence.index s i) / pow2 5 % 2);
  assert(a4 ==  v (Lib.Sequence.index s i) / pow2 4 % 2);
  assert(a3 ==  v (Lib.Sequence.index s i) / pow2 3 % 2);
  assert(a2 ==  v (Lib.Sequence.index s i) / pow2 2 % 2);
  assert(a1 ==  v (Lib.Sequence.index s i) / pow2 1 % 2);
  assert(a0 ==  v (Lib.Sequence.index s i) / pow2 0 % 2); 

  assert (v (Lib.Sequence.index s i) < pow2 8);
  
  lemma_index_as_ith_ (v (Lib.Sequence.index s i)) a7 a6 a5 a4 a3 a2 a1 a0

val lemma_index_scalar_as_nat__: a: nat ->
  a7: nat -> a6: nat -> a5: nat -> a4: nat -> a3: nat -> a2: nat -> a1: nat -> a0: nat ->
  Lemma (pow2 4 * (pow2 4 * a + pow2 3 * a7 + pow2 2 * a6 + pow2 1 * a5 + a4) + pow2 3 * a3 + pow2 2 * a2 + pow2 1 * a1 + a0 == pow2 8 * a + pow2 7 * a7 + pow2 6 * a6 + pow2 5 * a5 + pow2 4 * a4  + pow2 3 * a3 + pow2 2 * a2 + pow2 1 * a1 + a0)

let lemma_index_scalar_as_nat__ a a7 a6 a5 a4 a3 a2 a1 a0 = 
  pow2_plus 4 4;
  pow2_plus 4 3;
  pow2_plus 4 2;
  pow2_plus 4 1


#push-options "--z3rlimit 1000"

val lemma_index_scalar_as_nat_: #c: curve -> s: scalar_bytes #c -> i: size_nat {i < v (getScalarLenBytes c)} -> Lemma (  
  let l = v (getScalarLen c) in 
  let a7 = v (ith_bit s (l - 8 * i - 1)) in 
  let a6 = v (ith_bit s (l - 8 * i - 2)) in 
  let a5 = v (ith_bit s (l - 8 * i - 3)) in 
  let a4 = v (ith_bit s (l - 8 * i - 4)) in 
  let a3 = v (ith_bit s (l - 8 * i - 5)) in 
  let a2 = v (ith_bit s (l - 8 * i - 6)) in 
  let a1 = v (ith_bit s (l - 8 * i - 7)) in 
  let a0 = v (ith_bit s (l - 8 * i - 8)) in 
  scalar_as_nat_ s (8 * i + 8) == pow2 8 * scalar_as_nat_ s (8 * i) + a0 + 2 * a1 + pow2 2 * a2 + pow2 3 * a3 + pow2 4 * a4 + pow2 5 * a5 + pow2 6 * a6 + pow2 7 * a7)

let lemma_index_scalar_as_nat_ #c s i = 
  let l = v (getScalarLen c) in 
  
  let a7 = v (ith_bit s (l - 8 * i - 1)) in 
  let a6 = v (ith_bit s (l - 8 * i - 2)) in 
  let a5 = v (ith_bit s (l - 8 * i - 3)) in 
  let a4 = v (ith_bit s (l - 8 * i - 4)) in 
  let a3 = v (ith_bit s (l - 8 * i - 5)) in 
  let a2 = v (ith_bit s (l - 8 * i - 6)) in 
  let a1 = v (ith_bit s (l - 8 * i - 7)) in 
  let a0 = v (ith_bit s (l - 8 * i - 8)) in

  calc (==) {
    scalar_as_nat_ s (8 * i + 4);
  (==) {scalar_as_nat_def s (8 * i + 4)}
    2 * scalar_as_nat_ s (8 * i + 3) + a4; 
  (==) {scalar_as_nat_def s (8 * i + 3); pow2_double_mult 1}
    pow2 2 * scalar_as_nat_ s (8 * i + 2) + pow2 1 * a5 + a4; 
  (==) {scalar_as_nat_def s (8 * i + 2); pow2_double_mult 2}
    pow2 3 * scalar_as_nat_ s (8 * i + 1) + pow2 2 * a6 + pow2 1 * a5 + a4; 
  (==) {scalar_as_nat_def s (8 * i + 1); pow2_double_mult 3}
    pow2 4 * scalar_as_nat_ s (8 * i) + pow2 3 * a7 + pow2 2 * a6 + pow2 1 * a5 + a4;
  };

  calc (==) {
    scalar_as_nat_ s (8 * i + 8); 
  (==) {scalar_as_nat_def s (8 * i + 8)}
    2 * scalar_as_nat_ s (8 * i + 7) + a0;
  (==) {scalar_as_nat_def s (8 * i + 7); pow2_double_mult 1}
    pow2 2 * scalar_as_nat_ s (8 * i + 6) + pow2 1 * a1 + a0;
  (==) {scalar_as_nat_def s (8 * i + 6); pow2_double_mult 2}
    pow2 3 * scalar_as_nat_ s (8 * i + 5) + pow2 2 * a2 + pow2 1 * a1 + a0;
  (==) {scalar_as_nat_def s (8 * i + 5); pow2_double_mult 3}
    pow2 4 * scalar_as_nat_ s (8 * i + 4) + pow2 3 * a3 + pow2 2 * a2 + pow2 1 * a1 + a0;
  (==) {}
    pow2 4 * (pow2 4 * scalar_as_nat_ s (8 * i) + pow2 3 * a7 + pow2 2 * a6 + pow2 1 * a5 + a4) + pow2 3 * a3 + pow2 2 * a2 + pow2 1 * a1 + a0;
  (==) {lemma_index_scalar_as_nat__ (scalar_as_nat_ s (8 * i)) a7 a6 a5 a4 a3 a2 a1 a0}
    pow2 8 * scalar_as_nat_ s (8 * i) + pow2 7 * a7 + pow2 6 * a6 + pow2 5 * a5 + pow2 4 * a4 + pow2 3 * a3 + pow2 2 * a2 + pow2 1 * a1 + a0;}


val lemma_index_scalar_as_nat: #c: curve -> s: scalar_bytes #c -> i: size_nat {i < v (getScalarLenBytes c)} ->
  Lemma (v (Lib.Sequence.index s i) == scalar_as_nat #c s / pow2 (v (getScalarLen c) - 8 * (i + 1)) % pow2 8)

let lemma_index_scalar_as_nat #c s i = 
  let l = v (getScalarLen c) in 
  lemma_index_as_ith #c s i;

  let a7 = v (ith_bit s (l - 8 * i - 1)) in 
  let a6 = v (ith_bit s (l - 8 * i - 2)) in 
  let a5 = v (ith_bit s (l - 8 * i - 3)) in 
  let a4 = v (ith_bit s (l - 8 * i - 4)) in 
  let a3 = v (ith_bit s (l - 8 * i - 5)) in 
  let a2 = v (ith_bit s (l - 8 * i - 6)) in 
  let a1 = v (ith_bit s (l - 8 * i - 7)) in 
  let a0 = v (ith_bit s (l - 8 * i - 8)) in 

  lemma_index_scalar_as_nat_ s i;
  lemma_mod_sub (scalar_as_nat_ s (8 * i + 8)) (pow2 8) (scalar_as_nat_ s (8 * i));
  test #c s (8 * i + 8);
  small_mod (v (Lib.Sequence.index s i)) (pow2 8)

#pop-options


val scalar_as_sub_radix4: #c: curve -> s: scalar_bytes #c -> i: nat {(i + 1) * 4 <= v (getScalarLen c)} -> 
  Lemma ((let l = v (getScalarLen c) in 
  (scalar_as_nat s / pow2 (l - (i + 1) * 4)) % pow2 4 == scalar_as_nat_ #c s (4 * i + 4) - 16 * scalar_as_nat_ #c s (4 * i))) 

let scalar_as_sub_radix4 #c s i =
  let l = v (getScalarLen c) in 
  test s ((i + 1) * 4);
 
  scalar_as_nat_def s (4 * i + 4); 
  scalar_as_nat_def s (4 * i + 3); 
  scalar_as_nat_def s (4 * i + 2); 
  scalar_as_nat_def s (4 * i + 1); 
  
  modulo_addition_lemma (8 * v (ith_bit s (l - (4 * i + 1))) + 
    4 * v (ith_bit s (l - (4 * i + 2))) + 
    2 * v (ith_bit s (l - (4 * i + 3))) + 
    v (ith_bit s (l - (4 * i + 4)))) (pow2 4) (scalar_as_nat_ s (4 * i));

  small_mod (
    8 * v (ith_bit s (l - (4 * i + 1))) + 
    4 * v (ith_bit s (l - (4 * i + 2))) + 
    2 * v (ith_bit s (l - (4 * i + 3))) + 
    v (ith_bit s (l - (4 * i + 4)))) (pow2 4)
