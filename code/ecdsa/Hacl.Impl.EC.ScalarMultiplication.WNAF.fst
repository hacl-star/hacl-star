module Hacl.Impl.EC.ScalarMultiplication.WNAF

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

open Hacl.Impl.EC.Masking
open Hacl.Impl.EC.Masking.ScalarAccess
open Lib.IntTypes.Intrinsics

open FStar.Math.Lemmas


#set-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0" 


inline_for_extraction noextract
let radix: (r: uint64 {v r == w}) = (u64 5)

inline_for_extraction noextract
let radix_shiftval: (r: shiftval U64 {v r == w /\ v r == v radix}) = (size 5)

inline_for_extraction noextract
let radix_u32: (r: size_t {v r == w /\ v r == v radix}) = (size 5)

inline_for_extraction noextract
let dradix : (r: uint64 {v r == m}) = assert_norm(pow2 5 == 32); (u64 32)

inline_for_extraction noextract
let dradix_wnaf : (r: uint64 {v r == 2 * m}) = 
  FStar.Math.Lemmas.pow2_double_sum 5; 
  assert_norm (pow2 6 == 64);
  (u64 64)


val scalar_rwnaf_step_compute_di: #c: curve -> w0: uint64 
  -> out: lbuffer uint64 (size ((getPower c / Spec.ECC.WNAF.w + 1) * 2))
  -> mask: uint64 {v mask = pow2 (v radix + 1) - 1} 
  -> r: lbuffer uint64 (size 1) -> i: size_t {v i < getPower c / Spec.ECC.WNAF.w} -> 
  Stack unit
  (requires fun h -> live h out /\ live h r /\ disjoint r out /\ (
    let lastIndex = v (getScalarLen c) / w in 
    let signLast = Lib.Sequence.index (as_seq h out) (2 * lastIndex + 1) in 
    v signLast == 0))
  (ensures fun h0 _ h1 -> modifies (loc out |+| loc r) h0 h1 /\ (
    let sign = Lib.Sequence.index (as_seq h1 out) (2 * v i + 1) in 
    let abs =  Lib.Sequence.index (as_seq h1 out) (2 * v i) in 
    (if v sign = 0 then v w0 - v dradix == v abs else - (v w0 - v dradix) == v abs) /\ 
    (if (v w0 - v dradix) >= 0 then v sign == 0 else v sign = pow2 64 - 1)) /\ (
    forall (j: nat {j < 2 * v i}).
      Lib.Sequence.index (as_seq h0 out) j == Lib.Sequence.index (as_seq h1 out) j) /\ (
    let lastIndex = v (getScalarLen c) / w in 
    let signLast = Lib.Sequence.index (as_seq h1 out) (2 * lastIndex + 1) in 
    v signLast == 0))

let scalar_rwnaf_step_compute_di w out mask r i =
  let h0 = ST.get() in 
  let c = Lib.IntTypes.Intrinsics.sub_borrow_u64 (u64 0) w dradix r in 
  let r0 = index r (size 0) in 
    let h1 = ST.get() in 

  let r2 = u64 0 -. r0 in 
    
  let cAsFlag = eq1_u64 c in 
  let r3 = cmovznz2 r2 r0 cAsFlag in 

  upd out (size 2 *! i) r3;
  upd out (size 2 *! i +! size 1) cAsFlag


val scalar_compute_window_lemma: #c: curve ->  scalar: scalar_bytes #c
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
  scalar_as_nat_ scalar (v (getScalarLen c) - (t + 1)) % m * 2 == i /\
  scalar_as_nat scalar / pow2 (t + 1) % m * 2 == i)


#push-options "--z3rlimit 300"

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
  sh0: nat {sh0 <= 1} -> sh1: nat {sh1 <= 1} -> sh2: nat {sh2 <= 1} -> sh3: nat {sh3 <= 1} ->  sh4: nat {sh4 <= 1} -> 
  Lemma (sh0 * pow2 1 + 
    sh1 * pow2 2 +
    sh2 * pow2 3 +
    sh3 * pow2 4 +
    sh4 * pow2 5 < pow2 6)

let scalar_compute_window_lemma_less sh0 sh1 sh2 sh3 sh4 = 
  assert_norm (pow2 1 + pow2 2 + pow2 3 + pow2 4 + pow2 5 < pow2 6)


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
    
  scalar_as_nat_def #c  scalar (v (getScalarLen c) - (t + 1));
  scalar_as_nat_def #c  scalar (v (getScalarLen c) - (t + 2));
  scalar_as_nat_def #c  scalar (v (getScalarLen c) - (t + 3));
  scalar_as_nat_def #c  scalar (v (getScalarLen c) - (t + 4));
  scalar_as_nat_def #c  scalar (v (getScalarLen c) - (t + 5));

  scalar_compute_window_lemma_lemma_powers ();
  
  assert(2 * scalar_as_nat_ scalar (v (getScalarLen c) - (t + 1)) == 
    pow2 6 * scalar_as_nat_ scalar (v (getScalarLen c) - (t + 6)) + i);

  assert(2 * scalar_as_nat_ scalar (v (getScalarLen c) - (t + 1)) % pow2 6 == 
    (pow2 6 * scalar_as_nat_ scalar (v (getScalarLen c) - (t + 6)) + i) % pow2 6); 

  pow2_multiplication_modulo_lemma_2 (scalar_as_nat_ scalar (v (getScalarLen c) - (t + 1))) 6 1;

  assert(scalar_as_nat_ scalar (v (getScalarLen c) - (t + 1)) * 2 % pow2 6 == 
    (pow2 6 * scalar_as_nat_ scalar (v (getScalarLen c) - (t + 6)) + i) % pow2 6);

  lemma_mod_plus i (scalar_as_nat_ scalar (v (getScalarLen c) - (t + 6))) (pow2 6);


  assert(scalar_as_nat_ scalar (v (getScalarLen c) - (t + 1)) % pow2 5 * 2 ==  i % pow2 6);

  scalar_compute_window_lemma_less sh0 sh1 sh2 sh3 sh4;
  small_mod i (pow2 6);

  Hacl.Impl.EC.Masking.ScalarAccess.Lemmas.test #c scalar ((v (getScalarLen c) - (t + 1)));
  assert(scalar_as_nat_ scalar (v (getScalarLen c) - (t + 1)) % pow2 5 * 2 == i);
  
  assert(scalar_as_nat_ scalar (v (getScalarLen c) - (t + 1)) == scalar_as_nat scalar / pow2 (t + 1));
  assert(scalar_as_nat scalar / pow2 (t + 1) % m * 2 == i)


val scalar_rwnaf_step_compute_window_: #c: curve 
  -> wStart: uint64 {v wStart < pow2 (64 - 5)}
  -> scalar: scalar_t #MUT #c 
  -> k: size_t {v k < getPower c / Spec.ECC.WNAF.w - 1} -> 
  Stack uint64 
  (requires fun h -> live h scalar)
  (ensures fun h0 w0 h1 -> modifies0 h0 h1 /\ v w0 - v wStart = 
    v (ith_bit (as_seq h0 scalar) ((v k + 1) * w + 1)) * pow2 1 + 
    v (ith_bit (as_seq h0 scalar) ((v k + 1) * w + 2)) * pow2 2 +
    v (ith_bit (as_seq h0 scalar) ((v k + 1) * w + 3)) * pow2 3 +
    v (ith_bit (as_seq h0 scalar) ((v k + 1) * w + 4)) * pow2 4 +
    v (ith_bit (as_seq h0 scalar) ((v k + 1) * w + 5)) * pow2 5)

let scalar_rwnaf_step_compute_window_ #c wStart scalar k = 
  let h0 = ST.get() in 
    assert_norm (pow2 (64 - 5) + pow2 1 + pow2 2 + pow2 3 + pow2 4 + pow2 5 < pow2 64);
  
  let i = (size 1 +! k) *! radix_u32 in 
  let w0 = wStart +! (shift_left (getScalarBit_leftEndian #c scalar (i +! size 1)) (size 1)) in 
  let w0 = w0 +! (shift_left (getScalarBit_leftEndian #c scalar (i +! (size 2))) (size 2)) in 
  let w0 = w0 +! (shift_left (getScalarBit_leftEndian #c scalar (i +! (size 3))) (size 3)) in 
  let w0 = w0 +! (shift_left (getScalarBit_leftEndian #c scalar (i +! (size 4))) (size 4)) in 
  let w0 = w0 +! (shift_left (getScalarBit_leftEndian #c scalar (i +! (size 5))) (size 5)) in 
  w0

#pop-options


inline_for_extraction noextract
val scalar_rwnaf_step_compute_window: #c: curve 
  -> wStart: uint64 {v wStart < pow2 (64 - 5)}
  -> scalar: scalar_t #MUT #c 
  -> k: size_t {v k < getPower c / Spec.ECC.WNAF.w - 1} -> 
  Stack uint64 
  (requires fun h -> live h scalar)
  (ensures fun h0 w0 h1 -> modifies0 h0 h1 /\ (
    let t = (v k + 1) * w in 
    scalar_as_nat_ (as_seq h0 scalar) (v (getScalarLen c) - (t + 1)) % m * 2 == v w0 - v wStart /\
    scalar_as_nat (as_seq h0 scalar) / pow2 (t + 1) % m * 2 == v w0 - v wStart))

let scalar_rwnaf_step_compute_window #c wStart scalar k = 
  let h0 = ST.get() in 
  scalar_compute_window_lemma (as_seq h0 scalar) k;
  scalar_rwnaf_step_compute_window_ #c wStart scalar k  


inline_for_extraction noextract
val scalar_rwnaf_step: #c: curve -> out: lbuffer uint64 (size ((getPower c / Spec.ECC.WNAF.w + 1) * 2))
  -> scalar: scalar_t #MUT #c 
  -> window: lbuffer uint64 (size 1) 
  -> mask: uint64 {v mask = pow2 (v radix + 1) - 1}
  -> r: lbuffer uint64 (size 1) 
  -> i: size_t {v i < getPower c / Spec.ECC.WNAF.w - 1} -> 
  Stack unit 
  (requires fun h -> live h out /\ live h scalar /\ live h window /\ live h r /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc out; loc scalar; loc window; loc r] /\ (
    let w0 = v (Lib.Sequence.index (as_seq h window) 0) in 
    w0 == scalar_as_nat (as_seq h scalar) / pow2 (v i * w + 1) % pow2 w * 2 + 1 /\
    w0 < 2 * m) /\ (
    let lastIndex = v (getScalarLen c) / w in 
    let signLast = Lib.Sequence.index (as_seq h out) (2 * lastIndex + 1) in 
    v signLast == 0))
  (ensures fun h0 _ h1 -> modifies (loc out |+| loc window |+| loc r) h0 h1 /\ (
    let k = v i + 1 in 
    let w0 = v (Lib.Sequence.index (as_seq h0 window) 0) in
    let wUpd = v (Lib.Sequence.index (as_seq h1 window) 0) in
    let sign = Lib.Sequence.index (as_seq h1 out) (2 * v i + 1) in 
    let abs =  Lib.Sequence.index (as_seq h1 out) (2 * v i) in 
    (if v sign = 0 then (w0 % (2 * m) - m) == v abs else - (w0 % (2 * m) - m) == v abs) /\
    (if w0 % (2 * m) - m >= 0 then v sign = 0 else v sign = maxint U64) /\
    wUpd < 2 * m /\ 
    wUpd == scalar_as_nat (as_seq h0 scalar) % pow2 (k * w + w + 1) / pow2 (k * w) / 2 * 2 + 1 /\
    wUpd == scalar_as_nat (as_seq h0 scalar) / pow2 (k * w + 1) % pow2 w * 2 + 1 /\ (
    forall (j: nat {j < 2 * v i}). 
      Lib.Sequence.index (as_seq h0 out) j == Lib.Sequence.index (as_seq h1 out) j)) /\ (
    let lastIndex = v (getScalarLen c) / w in 
    let signLast = Lib.Sequence.index (as_seq h1 out) (2 * lastIndex + 1) in 
    v signLast == 0))


let scalar_rwnaf_step #c out scalar window mask r i = 
    let h0 = ST.get() in 
  let wVar = to_u64 (index window (size 0)) in 
    assert(v wVar = v (Lib.Sequence.index (as_seq h0 window) 0));

  let wMask = logand wVar mask in 
    logand_mask wVar mask (v radix + 1); 
    FStar.Math.Lemmas.pow2_double_sum (v radix); 
  scalar_rwnaf_step_compute_di wMask out mask r i; 
    let h1 = ST.get() in 
  let d = wMask -. dradix in 
  let wStart = shift_right (wVar -. d) radix_shiftval in 
  
  FStar.Math.Lemmas.lemma_div_lt_nat (v (wVar -. d)) 64 (v radix_shiftval);

  let w0 = scalar_rwnaf_step_compute_window wStart scalar i in 
  upd window (size 0) w0;

    let h2 = ST.get() in   
  let d_i = v wVar % (2 * m) - m in 
    
    assert(
      let w0 = v (Lib.Sequence.index (as_seq h0 window) 0) in
      let sign = Lib.Sequence.index (as_seq h2 out) (2 * v i + 1) in 
      let abs =  Lib.Sequence.index (as_seq h2 out) (2 * v i) in 
      if v sign = 0 then (w0 % (2 * m) - m) == v abs else - (w0 % (2 * m) - m) == v abs);

    
      assert (v wStart = (v wVar - (d_i % pow2 64)) % pow2 64 / m);
      lemma_mod_sub_distr (v wVar)  (d_i) (pow2 64); 
      assert (v wStart = (v wVar - d_i) % pow2 64 / m);
      
      assert (v wStart =  (v wVar - v wVar % (2 * m) + m) % pow2 64  / m);

      small_mod ((v wVar / (2 * m) * (2 * m)) + m) (pow2 64);

      assert (v wStart =  v wVar / (2 * m) * 2 + 1);

      pow2_multiplication_modulo_lemma_2 (scalar_as_nat (as_seq h0 scalar) / pow2 ((v i + 1) * w  + 1)) (w + 1) 1;

      assert(scalar_as_nat (as_seq h0 scalar) / pow2 ((v i + 1) * w  + 1) % m * 2 + (v wVar / (2 * m) * 2 + 1) == v w0);
      assert(scalar_as_nat (as_seq h0 scalar) / pow2 ((v i + 1) * w  + 1) * 2 % pow2 (w + 1)  + (v wVar / (2 * m) * 2 + 1) == v w0);
    
      assert(v wVar < 2 * m);
	small_division_lemma_1 (v wVar) (2 * m);
      assert(v wVar / (2 * m) == 0);

      assert(2 * (scalar_as_nat (as_seq h0 scalar) / pow2 ((v i + 1) * w  + 1)) % (2 * m) + 1 == v w0);
      pow2_plus (v i * w) (w + 1); 
      division_multiplication_lemma (scalar_as_nat (as_seq h0 scalar)) (pow2 (w + 1)) (pow2 (v i * w));

      division_multiplication_lemma (scalar_as_nat (as_seq h0 scalar)  / (pow2 w)) 2 (pow2 (v i * w));
      pow2_double_mult (v i * w);
      assert((scalar_as_nat (as_seq h0 scalar)  / (pow2 w) / (2 * pow2 (v i * w))) % (pow2 w) * 2 + 1 == v w0);
    
      assert ((scalar_as_nat (as_seq h0 scalar)  / (pow2 w) / (pow2 (v i * w + 1))) % (pow2 w) * 2 + 1 == v w0);
      pow2_modulo_division_lemma_1 (scalar_as_nat (as_seq h0 scalar)  / pow2 w) (v i * w + 1) (v i * w + 1 + w);
      pow2_double_mult (v i * w); 
    
      division_multiplication_lemma (scalar_as_nat (as_seq h0 scalar) / (pow2 w) % pow2 (v i * w + 1 + w)) (pow2 (v i * w)) (pow2 1);

      assert(scalar_as_nat (as_seq h0 scalar)  / (pow2 w)  % pow2 (v i * w + 1 + w) / pow2 (v i * w) / pow2 1  * 2 + 1 == v w0);

      let k = v i + 1 in 
   
      assert(2 * (scalar_as_nat (as_seq h0 scalar) / pow2 (k * w  + 1)) % (pow2 (w + 1)) + 1 == v w0);
      assert(scalar_as_nat (as_seq h0 scalar) / pow2 (k * w  + 1) % pow2 w * 2 + 1 == v w0);

      pow2_modulo_division_lemma_1 (scalar_as_nat (as_seq h0 scalar)) (k * w + 1) (k * w + 1 + w);
      pow2_double_mult (k * w);
      division_multiplication_lemma (scalar_as_nat (as_seq h0 scalar) % pow2 (k * w + w + 1)) (pow2 (k * w)) 2;
      
      assert(scalar_as_nat (as_seq h0 scalar) % pow2 (k * w + w + 1) / pow2 (k * w) / 2 * 2 + 1 == v w0);
      assert(v w0 < 2 * m)


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
    v i0 + v i1 * pow2 1 + v i2 * pow2 2 + v i3 * pow2 3 + v i4 * pow2 4 + v i5 * pow2 5 + v i6 * pow2 6 + v i7  * pow2 7== v (Lib.Sequence.index scalar (v (getScalarLenBytes c) - 1)))

let scalar_rwnaf_lemma0_lemma_byte #c scalar = admit()


val scalar_rwnaf_lemma0: #c: curve -> scalar: scalar_bytes #c 
  -> Lemma (scalar_as_nat scalar % pow2 8 = v (Lib.Sequence.index scalar (v (getScalarLenBytes c) - 1)))

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


val logor_mask: a: uint64 -> Lemma (v (logor (u64 1) a) == v a / 2 * 2 + 1)

let logor_mask a = 
  if v a % 2 = 0 then 
    begin
      logor_disjoint (u64 1) a 1;
      assert(v a + 1 == v (logor (u64 1) a))
    end
  else
    begin
      assume (v (logor (u64 1) a) == v a)
    end


val getLenWnaf: #c: curve -> Tot (r: size_t {v r == v (getScalarLen c) / w})

let getLenWnaf #c = 
  match c with
  |P256 -> 
    assert (v (getScalarLen P256) / 5 == 51);
    size 51
  |P384 ->
    assert (v (getScalarLen P384) / 5 == 76);
    size 76


val scalar_rwnaf_loop: #c: curve -> out: lbuffer uint64 (size (2 * (v (getScalarLen c) / w + 1))) -> scalar: scalar_t #MUT #c 
  -> mask: uint64 {v mask = pow2 (v radix + 1) - 1}
  -> window: lbuffer uint64 (size 1) -> 
  Stack unit 
  (requires fun h -> live h out /\ live h scalar /\ live h window /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc out; loc scalar; loc window] /\ (
    let w0 = v (Lib.Sequence.index (as_seq h window) 0) in 
    w0 == scalar_as_nat #c (as_seq h scalar) / 2 % pow2 w * 2 + 1 /\
    w0 < 2 * m) /\ (
    let lastIndex = v (getScalarLen c) / w in 
    let signLast = Lib.Sequence.index (as_seq h out) (2 * lastIndex + 1) in 
    v signLast == 0))
  (ensures fun h0 _ h1 -> modifies (loc out |+| loc window) h0 h1 /\ (
    let w0 = v (Lib.Sequence.index (as_seq h1 window) 0) in 
    w0 == scalar_as_nat #c (as_seq h0 scalar) / pow2 ((v (getScalarLen c) / w - 1) * w + 1) % pow2 w * 2 + 1 /\
    w0 < 2 * m) /\ (
    forall (j: nat {j < v (getScalarLen c) / w - 1}). 
    let wUpd = v (Lib.Sequence.index (as_seq h1 window) 0) in
    let sign = Lib.Sequence.index (as_seq h1 out) (2 * j + 1) in 
    let abs =  Lib.Sequence.index (as_seq h1 out) (2 * j) in 
    let w0 = scalar_as_nat #c (as_seq h0 scalar) / pow2 (j * w + 1) % pow2 w * 2 + 1 in
    (if w0 % (2 * m) - m >= 0 then v sign = 0 else v sign = maxint U64) /\ (
    if v sign = 0 then (w0 % (2 * m) - m) == v abs else - (w0 % (2 * m) - m) == v abs) /\ (
    let lastIndex = v (getScalarLen c) / w in 
    let signLast = Lib.Sequence.index (as_seq h1 out) (2 * lastIndex + 1) in 
    v signLast == 0)))

let scalar_rwnaf_loop #c out scalar mask window = 
  push_frame(); 
  let r = create (size 1) (u64 0) in 
    let h0 = ST.get() in 
  
  let inv h (i:nat {i <= v (getScalarLen c) / w}) = 
    live h out /\ live h scalar /\ live h window /\ live h r /\
    modifies (loc out |+| loc window |+| loc r) h0 h /\ (
    let w0 = v (Lib.Sequence.index (as_seq h window) 0) in 
    w0 == scalar_as_nat #c (as_seq h0 scalar) / pow2 (i * w + 1) % pow2 w * 2 + 1 /\
    w0 < 2 * m /\ (
    forall (j: nat {j < i}). 
      let w0 = scalar_as_nat #c (as_seq h0 scalar) / pow2 (j * w + 1) % pow2 w * 2 + 1 in
      let wUpd = v (Lib.Sequence.index (as_seq h window) 0) in
      let sign = Lib.Sequence.index (as_seq h out) (2 * j + 1) in 
      let abs =  Lib.Sequence.index (as_seq h out) (2 * j) in 
      (if w0 % (2 * m) - m >= 0 then v sign = 0 else v sign = maxint U64) /\ (
      if v sign = 0 then (w0 % (2 * m) - m) == v abs else - (w0 % (2 * m) - m) == v abs)) /\ (
    let lastIndex = v (getScalarLen c) / w in 
    let signLast = Lib.Sequence.index (as_seq h out) (2 * lastIndex + 1) in 
    v signLast == 0)) in 

  Lib.Loops.for 0ul (getLenWnaf #c -. 1ul) inv (scalar_rwnaf_step #c out scalar window mask r);
  pop_frame()


inline_for_extraction noextract
val scalar_rwnaf_compute_start_window: #c: curve 
  -> scalar: scalar_t #MUT #c 
  -> mask: uint64 {v mask = pow2 (v radix + 1) - 1} -> 
  Stack uint64
  (requires fun h -> live h scalar)
  (ensures fun h0 window h1 -> modifies0 h0 h1 /\ v window == scalar_as_nat #c (as_seq h0 scalar) / 2 % pow2 w * 2 + 1)

let scalar_rwnaf_compute_start_window #c scalar mask = 
  let h0 = ST.get() in 
  
  let in0 = to_u64 (index scalar (getScalarLenBytes c -! size 1)) in 
  let windowStartValue = logor (u64 1) (logand in0 mask) in 

  assert_norm (pow2 6 == 64);
    logand_mask in0 mask 6;
    scalar_rwnaf_lemma0 #c (as_seq h0 scalar); 
    logor_mask (logand in0 mask); 
    pow2_modulo_modulo_lemma_1 (scalar_as_nat #c (as_seq h0 scalar)) 6 8;

    multiply_fractions (scalar_as_nat #c (as_seq h0 scalar) % pow2 6) 2;
    pow2_double_mult w;

  assert (v windowStartValue == scalar_as_nat #c (as_seq h0 scalar) % pow2 6 / 2 * 2 + 1);
  assume (v windowStartValue == scalar_as_nat #c (as_seq h0 scalar) / 2 % pow2 w * 2 + 1);
  
  windowStartValue


inline_for_extraction noextract
val scalar_rwnaf_tail_3: #c: curve -> scalar: scalar_t #MUT #c -> wStart: uint64 {v wStart < pow2 (64 - 5)} ->
  Stack uint64 
  (requires fun h -> live h scalar /\ 4 == v (getScalarLen c) - v (getScalarLen c) / w * w)
  (ensures fun h0 w0 h1 -> modifies0 h0 h1 /\ 
    2 * (scalar_as_nat (as_seq h0 scalar) / pow2 (v (getScalarLen c) / w * w + 1)) = v w0 - v wStart)

let scalar_rwnaf_tail_3 #c scalar wStart = 
  let h0 = ST.get() in 

  let i = getLenWnaf #c *! radix_u32 in 
  scalar_as_nat_def #c (as_seq h0 scalar) (v (getScalarLen c) - (v i + 1));
  scalar_as_nat_def #c (as_seq h0 scalar) (v (getScalarLen c) - (v i + 2));
  scalar_as_nat_def #c (as_seq h0 scalar) (v (getScalarLen c) - (v i + 3));

  Hacl.Impl.EC.Masking.ScalarAccess.Lemmas.test #c (as_seq h0 scalar) (v (getScalarLen c) - v (getScalarLen c) / w * w - 1);
  scalar_as_nat_zero (as_seq h0 scalar);

  assert_norm (pow2 (64 - 5) + pow2 1 + pow2 2 + pow2 3  < pow2 64);
  let w0 = wStart +! (shift_left (getScalarBit_leftEndian #c scalar (i +! size 1)) (size 1)) in 
  let w0 = w0 +! (shift_left (getScalarBit_leftEndian #c scalar (i +! (size 2))) (size 2)) in 
  w0 +! (shift_left (getScalarBit_leftEndian #c scalar (i +! (size 3))) (size 3))
  

val scalar_rwnaf_tail__: #c: curve
  -> scalar: scalar_t #MUT #c  -> wStart: uint64 {v wStart < pow2 (64 - 5)} ->
  Stack uint64 
  (requires fun h -> live h scalar /\ 
    scalar_as_nat (as_seq h scalar) < pow2 (v (getScalarLen c)))
  (ensures fun h0 w0 h1 -> modifies0 h0 h1 /\ 
    2 * (scalar_as_nat (as_seq h0 scalar) / pow2 (v (getScalarLen c) / w * w + 1)) = v w0 - v wStart)

let scalar_rwnaf_tail__ #c scalar wStart = 
  let h0 = ST.get() in 
  match c with 
  |P256 -> wStart
  |P384 -> scalar_rwnaf_tail_3 #P384 scalar wStart


val scalar_rwnaf_tail_: #c: curve
  -> scalar: scalar_t #MUT #c 
  -> mask: uint64 
  -> wVar: uint64 {v wVar < 2 * m /\ v mask == v wVar % pow2 (w + 1)}
  ->
  Stack uint64 
  (requires fun h -> live h scalar /\ 
    scalar_as_nat (as_seq h scalar) < pow2 (v (getScalarLen c)))
  (ensures fun h0 wLast h1 -> modifies0 h0 h1 /\ 
    2 * (scalar_as_nat (as_seq h0 scalar) / pow2 (v (getScalarLen c) / w * w + 1)) + 
     (v wVar / pow2 (w + 1) * pow2 (w + 1) + m) % pow2 64  / m = v wLast)

let scalar_rwnaf_tail_ #c scalar mask wVar = 
  let h0 = ST.get() in 
  
  let d = mask -. dradix in 
  let wStart = shift_right (wVar -. d) radix_shiftval in 
  
    shift_right_lemma (wVar -. d) radix_shiftval;

      assert(v d == (v mask - m) % pow2 64);
    lemma_mod_sub_distr (v wVar) (v mask - m) (pow2 64);
      assert(v wStart == (v wVar - v mask + m) % pow2 64  / pow2 w);
    
    lemma_div_lt_nat ((v wVar - v mask + m) % pow2 64) (64) w;
  
  scalar_rwnaf_tail__ scalar wStart


val scalar_rwnaf_lemma_tail: #c: curve -> s: nat {s < pow2 (v (getScalarLen c))} -> 
  Lemma (
    let len = v (getScalarLen c) in 
    ((s / pow2 ((len / w - 1) * w + 1) % pow2 w * 2 + 1) / pow2 (w + 1) * pow2 (w + 1) + m) % pow2 64 / m == ((s / pow2 ((len / w - 1) * w + 1) % pow2 w * 2 + 1) / pow2 (w + 1) * pow2 (w + 1) + m) / m)

let scalar_rwnaf_lemma_tail #c s = 
  let len = v (getScalarLen c) in 

  lemma_div_lt_nat s (v (getScalarLen c)) ((v (getScalarLen c) / w - 1) * w + 1);

  multiply_fractions (
    let len = v (getScalarLen c) in 
     s / pow2 ((len / w - 1) * w + 1) % pow2 w * 2 + 1) (pow2 (w + 1));

  assert_norm(pow2 w * 2 + 1 + m < pow2 64);

  assert(
      let len = v (getScalarLen c) in 
      s / pow2 ((len / w - 1) * w + 1) % pow2 w * 2 + 1 < pow2 w * 2 + 1);

  assert(
      let len = v (getScalarLen c) in 
      (s / pow2 ((len / w - 1) * w + 1) % pow2 w * 2 + 1) / pow2 (w + 1) * pow2 (w + 1) + m < pow2 64);

  small_mod (
      let len = v (getScalarLen c) in 
      (s / pow2 ((len / w - 1) * w + 1) % pow2 w * 2 + 1) / pow2 (w + 1) * pow2 (w + 1) + m) (pow2 64)


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

  assert ((s / pow2 ((len / w - 1) * w + 1) % pow2 w * 2 + 1 < pow2 (w + 1)));

  assert(1 == (s / pow2 ((len / w - 1) * w + 1) % pow2 w * 2 + 1) / pow2 (w + 1) * 2 + 1)



val scalar_rwnaf_tail: #c: curve 
  -> scalar: scalar_t #MUT #c 
  -> mask: uint64 
  -> wVar: uint64 {v wVar < 2 * m /\ v mask == v wVar % pow2 (w + 1)}
  ->
  Stack uint64 
  (requires fun h -> live h scalar /\ 
    scalar_as_nat (as_seq h scalar) < pow2 (v (getScalarLen c)) /\ 
    v wVar = scalar_as_nat #c (as_seq h scalar) / pow2 ((v (getScalarLen c) / w - 1) * w + 1) % pow2 w * 2 + 1)
  (ensures fun h0 wLast h1 -> modifies0 h0 h1 /\ (
    let s = scalar_as_nat (as_seq h0 scalar) in 
    let len = v (getScalarLen c) in 
    v wLast == 2 * (s / pow2 (len / w * w + 1)) + 1))

let scalar_rwnaf_tail #c scalar mask wVar = 
  let h0 = ST.get() in 

  let wLast = scalar_rwnaf_tail_ #c scalar mask wVar in 

  scalar_as_nat_upperbound  (as_seq h0 scalar) (v (getScalarLen c));
  scalar_rwnaf_lemma_tail #c (scalar_as_nat (as_seq h0 scalar));
  scalar_rwnaf_lemma0_tail #c (scalar_as_nat (as_seq h0 scalar));

  wLast



inline_for_extraction noextract
val scalar_rwnaf_: #c: curve -> out: lbuffer uint64 (size (2 * (v (getScalarLen c) / w + 1))) 
  -> scalar: scalar_t #MUT #c ->
  Stack unit 
  (requires fun h -> live h out /\ live h scalar /\ disjoint out scalar /\
    scalar_as_nat (as_seq h scalar) < pow2 (v (getScalarLen c)) /\ (
    let lastIndex = v (getScalarLen c) / w in 
    let signLast = Lib.Sequence.index (as_seq h out) (2 * lastIndex + 1) in 
    v signLast == 0))
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\ (
    forall (j: nat {j < v (getScalarLen c) / w }). 
      let sign = Lib.Sequence.index (as_seq h1 out) (2 * j + 1) in 
      let abs =  Lib.Sequence.index (as_seq h1 out) (2 * j) in 
      let w0 = scalar_as_nat #c (as_seq h0 scalar) / pow2 (j * w + 1) % pow2 w * 2 + 1 in
      (if w0 % (2 * m) - m >= 0 then v sign = 0 else v sign = maxint U64) /\ (
      if v sign = 0 then (w0 % (2 * m) - m) == v abs else - (w0 % (2 * m) - m) == v abs)) /\ (
      
    let lastIndex = v (getScalarLen c) / w in 
    let absLast = Lib.Sequence.index (as_seq h1 out) (2 * lastIndex) in 
    let signLast = Lib.Sequence.index (as_seq h1 out) (2 * lastIndex + 1) in 
    v signLast == 0 /\
    v absLast = scalar_as_nat #c (as_seq h0 scalar) / pow2 (v (getScalarLen c) / w * w + 1) * 2 + 1))


let scalar_rwnaf_ #c out scalar = 
  push_frame();
  let mask = dradix_wnaf -! (u64 1) in 
  let in0 = to_u64 (index scalar (getScalarLenBytes c -! size 1)) in 
    assert_norm (pow2 6 == 64);
  let windowStartValue = scalar_rwnaf_compute_start_window scalar mask in 

  let window = create (size 1) windowStartValue in 
  let r = create (size 1) (u64 0) in 
  
  scalar_rwnaf_loop #c out scalar mask window; 

  let wVar = index window (size 0) in 
  let wMask = logand wVar mask in 
    logand_mask wVar mask 6;

  scalar_rwnaf_step_compute_di #c wMask out mask r (getLenWnaf #c -! 1ul);
  let wLast = scalar_rwnaf_tail scalar wMask wVar in 

  upd out (size 2 *! getLenWnaf #c) wLast; 

  pop_frame()


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


val scalar_rwnaf_lemma_to_spec: n: nat {2 * (n / w + 1) < pow2 32}
  -> d: nat {d < pow2 n /\ d % 2 == 1} 
  -> out: lbuffer uint64 (size (2 * (n / w + 1))) -> h: mem 
  -> Lemma (requires (
    let wnaf_repr = to_wnaf n d in (
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
    let wnaf_repr = to_wnaf n d in 
    forall (j: nat {j <= n / w }). 
      let sign = Lib.Sequence.index (as_seq h out) (2 * j + 1) in 
      let abs =  Lib.Sequence.index (as_seq h out) (2 * j) in 
      let wf = Lib.Sequence.index #_ #(n / w + 1) wnaf_repr j in 
      (if wf >= 0 then v sign = 0 else v sign = maxint U64) /\ (
      if v sign = 0 then wf == v abs else - wf == v abs)))

let scalar_rwnaf_lemma_to_spec n d out h = 
  let wnaf_repr = to_wnaf n d in 

  assert(    let wnaf_repr = to_wnaf n d in
    let lastIndex = n / w in 
    let absLast = Lib.Sequence.index (as_seq h out) (2 * lastIndex) in 
    let signLast = Lib.Sequence.index (as_seq h out) (2 * lastIndex + 1) in 
    v signLast == 0 /\
    v absLast = Lib.Sequence.index #_ #(n / w + 1) wnaf_repr (n / w));

  assert (
    let wnaf_repr = to_wnaf n d in 
    let sign = Lib.Sequence.index (as_seq h out) (2 * (n / w) + 1) in 
    let abs =  Lib.Sequence.index (as_seq h out) (2 * (n / w)) in 
    let wf = Lib.Sequence.index #_ #(n / w + 1) wnaf_repr (n / w) in 
    (if wf >= 0 then v sign = 0 else v sign = maxint U64) /\ (
    if v sign = 0 then wf == v abs else - wf == v abs))


inline_for_extraction noextract
val scalar_rwnaf: #c: curve -> out: lbuffer uint64 (size (2 * (v (getScalarLen c) / w + 1))) 
  -> scalar: scalar_t #MUT #c ->
  Stack unit 
  (requires fun h -> live h out /\ live h scalar /\ disjoint out scalar /\ 
    scalar_as_nat (as_seq h scalar) < pow2 (v (getScalarLen c)) /\
    scalar_as_nat #c (as_seq h scalar) % 2 == 1 /\ (
    let lastIndex = v (getScalarLen c) / w in 
    let signLast = Lib.Sequence.index (as_seq h out) (2 * lastIndex + 1) in 
    v signLast == 0))
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\ (
    let n = v (getScalarLen c) in 
    let d = scalar_as_nat (as_seq h0 scalar) in
    let wnaf_repr = to_wnaf n d in 
    forall (j: nat {j <= v (getScalarLen c) / w }). 
      let sign = Lib.Sequence.index (as_seq h1 out) (2 * j + 1) in 
      let abs =  Lib.Sequence.index (as_seq h1 out) (2 * j) in 
      let wf = Lib.Sequence.index #_ #(n / w + 1) wnaf_repr j in 
      (if wf >= 0 then v sign = 0 else v sign = maxint U64) /\ (
      if v sign = 0 then wf == v abs else - wf == v abs)))

#push-options "--z3rlimit 200"

let scalar_rwnaf #c out scalar = 
  let h0 = ST.get() in
  scalar_rwnaf_ #c out scalar;
  scalar_as_nat_upperbound  (as_seq h0 scalar) (v (getScalarLen c));
  let h1 = ST.get() in 
  rwnaf_lemma0 (scalar_as_nat (as_seq h0 scalar));
  scalar_rwnaf_lemma_to_spec (v (getScalarLen c)) (scalar_as_nat (as_seq h0 scalar)) out h1

#pop-options


assume val getPointPrecomputed_P256: index: size_t {v index < (getPower P256 / w + 1) * pow2 (w - 1)} 
  -> result: pointAffine P256 ->
  Stack unit
  (requires fun h -> live h result)
  (ensures fun h0 r h1 -> modifies (loc result) h0 h1 /\ point_aff_eval P256 h1 result /\ (
    let j = v index / pow2 (w - 1) in 
    let i = v index % pow2 (w - 1) + 1 in 
    let p_i = point_mult #P256 (pow2 (j * w) * i) (basePoint #P256) in 
    let r = fromDomainPoint #P256 #DH (toJacobianCoordinates (point_affine_as_nat P256 h1 result)) in 
    pointEqual r p_i))


assume val getPointPrecomputed_P384: index: size_t {v index < (getPower P384 / w + 1) * pow2 (w - 1)} 
  -> result: pointAffine P384 ->
  Stack unit
  (requires fun h -> live h result)
  (ensures fun h0 r h1 -> modifies (loc result) h0 h1 /\ point_aff_eval P384 h1 result /\ (
    let j = v index / pow2 (w - 1) in 
    let i = v index % pow2 (w - 1) + 1 in 
    let p_i = point_mult #P384 (pow2 (j * w) * i) (basePoint #P384) in 
    let r = fromDomainPoint #P384 #DH (toJacobianCoordinates (point_affine_as_nat P384 h1 result)) in 
    pointEqual r p_i))


val getPointPrecomputed: #c: curve 
  -> index: size_t {v index < (getPower c / w + 1) * pow2 (w - 1)}
  -> result: pointAffine c ->
  Stack unit
  (requires fun h -> live h result)
  (ensures fun h0 r h1 -> modifies (loc result) h0 h1 /\ point_aff_eval c h1 result /\ (
    let j = v index / pow2 (w - 1) in 
    let i = v index % pow2 (w - 1) + 1 in 
    let p_i = point_mult #c (pow2 (j * w) * i) (basePoint #c) in 
    let r = fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h1 result)) in 
    pointEqual r p_i))

let getPointPrecomputed #c index result = 
  match c with 
  |P256 -> getPointPrecomputed_P256 index result
  |P384 -> getPointPrecomputed_P384 index result
  

val copy_point_conditional_affine: #c: curve 
  -> result: pointAffine c 
  -> p: pointAffine c 
  -> mask: uint64 {v mask = 0 \/ v mask = pow2 64 - 1} ->
  Stack unit
  (requires fun h -> 
    live h result /\ live h p /\ disjoint result p /\ point_aff_eval c h p)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ (
    let len = getCoordinateLenU64 c in 
    let pX, pY = gsub p (size 0) len, gsub p len len in 
    let rX, rY = gsub result (size 0) len, gsub result len len in 
    (v mask = pow2 64 - 1 ==> point_aff_eval c h1 result) /\ (
    if v mask = 0 then
      as_nat c h1 rX == as_nat c h0 rX /\ as_nat c h1 rY == as_nat c h0 rY
    else 
      as_nat c h1 rX == as_nat c h0 pX /\ as_nat c h1 rY == as_nat c h0 pY)))

let copy_point_conditional_affine #c result p mask = 
  let len = getCoordinateLenU64 c in
  let pX, pY = sub p (size 0) len, sub p len len in 
  Hacl.Impl.EC.Precomputed.copy_point_conditional_affine #MUT #c result pX pY mask


val loopK_step: #c: curve -> d: uint64 -> result: pointAffine c 
  -> j: size_t {v j < (getPower c / w + 1)} 
  -> k: size_t {v k < pow2 (w - 1)}
  -> tempPoint: pointAffine c -> Stack unit
  (requires fun h -> live h result /\ live h tempPoint /\ disjoint result tempPoint)
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc tempPoint) h0 h1 /\ (
    let len = getCoordinateLenU64 c in 
    let rX, rY = gsub result (size 0) len, gsub result len len in 
    (v d == v k ==> point_aff_eval c h1 result) /\ (
    if v d <> v k then
      as_nat c h1 rX == as_nat c h0 rX /\ as_nat c h1 rY == as_nat c h0 rY
    else 
      pointEqual (fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h1 result))) (point_mult #c (pow2 (v j * w) * v k) (basePoint #c)))))


let loopK_step #c d result j k tempPoint = 
  let mask = eq_mask d (to_u64 k) in 
    eq_mask_lemma d (to_u64 k); 
    let h0 = ST.get() in 
  getPointPrecomputed #c (j *! size 16 +! k) tempPoint;
    let h1 = ST.get() in 
  copy_point_conditional_affine result tempPoint mask;
    let h2 = ST.get() in 

  calc (==) {
    (v j * pow2 (w - 1) + v k) / pow2 (w - 1);
  (==) {}
    v j + v k / pow2 (w - 1);
  (==) {small_div (v k) (pow2 (w - 1))}
    v j;
  };

  calc (==) {
    (v j * pow2 (w - 1) + v k) % pow2 (w - 1);
  (==) {lemma_mod_plus (v k) (v j) (pow2 (w - 1))}
    v k;
  }


#push-options "--z3rlimit 300"


val loopK_loop: #c: curve 
  -> d: uint64 {v d < pow2 (w - 1)}
  -> result: pointAffine c
  -> j: size_t {v j < (getPower c / w + 1)} 
  -> tempPoint: pointAffine c -> Stack unit 
  (requires fun h -> live h result /\ live h tempPoint /\ disjoint result tempPoint)
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc tempPoint) h0 h1 /\ 
    point_aff_eval c h1 result /\
    pointEqual (fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h1 result)))
      (point_mult #c (pow2 (v j * w) * v d) (basePoint #c)))

let loopK_loop #c d result j tempPoint = 
  let h0 = ST.get() in 
   let invK h (k: nat) = live h result /\ live h tempPoint /\ modifies (loc result |+| loc tempPoint) h0 h /\ (
    let len = getCoordinateLenU64 c in 
    let rX, rY = gsub result (size 0) len, gsub result len len in 
    if k > v d then 
      point_aff_eval c h result /\
      pointEqual (fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h result))) (point_mult #c (pow2 (v j * w) * v d) (basePoint #c))
    else 
      as_nat c h rX == as_nat c h0 rX /\ as_nat c h rY == as_nat c h0 rY) in 
  Lib.Loops.for 0ul 16ul invK (fun k -> loopK_step d result j k tempPoint) 


val loopK: #c: curve -> d: uint64 {v d < pow2 (w - 1)} -> result: pointAffine c
  -> j: size_t {v j < (getPower c / w + 1)} -> Stack unit 
  (requires fun h -> live h result)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
    point_aff_eval c h1 result /\
  pointEqual (fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h1 result)))
    (point_mult #c (pow2 (v j * w) * v d) (basePoint #c)))

let loopK #c d result j = 
    let h0 = ST.get() in 
    push_frame(); 
  let tempPoint : pointAffine c = create (getCoordinateLenU64 c *! 2ul) (u64 0) in 
  loopK_loop d result j tempPoint; 
    let h1 = ST.get() in 
    pop_frame()


val copy_point_conditional: #c: curve -> result: point c
  -> x: point c -> mask: uint64 {uint_v mask == 0 \/ uint_v mask == pow2 64 - 1}  
  -> Stack unit
  (requires fun h -> live h result /\ live h x /\ disjoint result x /\ point_eval c h result /\ point_eval c h x)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ point_eval c h1 result /\ (
    if uint_v mask = 0 then 
      point_as_nat c h1 result == point_as_nat c h0 result
    else
      point_as_nat c h1 result == point_as_nat c h0 x))

let copy_point_conditional #c result p mask = 
  let h0 = ST.get() in 

  let len = getCoordinateLenU64 c in 

  let p_x = sub p (size 0) len in 
  let p_y = sub p len len in 
  let p_z = sub p (size 2 *! len) len in 

  let r_x = sub result (size 0) len in 
  let r_y = sub result len len in 
  let r_z = sub result (size 2 *! len) len in 

  copy_conditional #c r_x p_x mask;
  copy_conditional #c r_y p_y mask;
  copy_conditional #c r_z p_z mask


assume val lemma_inverse_existence: #c: curve 
  -> p0: Spec.ECC.point #c {~ (isPointAtInfinity #Jacobian p0)} 
  -> p:  Spec.ECC.point #c {~ (isPointAtInfinity #Jacobian p)}
  -> Lemma (
  exists (b: pos {b < getOrder #c}). 
    let bP = Spec.ECC.point_mult #c b p0 in
    isPointAtInfinity (pointAdd #c bP p))


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


val point_affine_neg: #c: curve -> p: pointAffine c -> result: pointAffine c -> Stack unit 
  (requires fun h -> live h p /\ live h result /\ disjoint p result /\ point_aff_eval c h p /\
    ~ (isPointAtInfinity (fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h p)))))
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ point_aff_eval c h1 result /\ (
    let pJ = fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h0 p)) in
    let b = getDLP #c pJ in 
    let rJ = fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h1 result)) in 
    pointEqual rJ (Spec.ECC.point_mult #c (-b) (basePoint #c))))

let point_affine_neg #c p result = 
    let h0 = ST.get() in 
  
  let len = getCoordinateLenU64 c in

  let pX, pY = sub p (size 0) len, sub p len len in 
  let rX, rY = sub result (size 0) len, sub result len len in 

  copy rX pX;
  felem_sub_zero #c pY rY;
    let h1 = ST.get() in 
    
    let prime = getPrime c in 

    let pJ = fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h0 p)) in
    let b = getDLP #c pJ in 

  point_neg_lemma_infinity_indexes #c pJ;
  assume (isPointAtInfinity (pointAdd #c pJ (fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h1 result)))));
  lemma_inverse_uniqueness pJ (fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h1 result))) (point_mult #c (-b) (basePoint #c))


val point_neg_conditional: #c: curve -> p: point c 
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) 
  -> mask: uint64 {v mask == 0 \/ v mask == pow2 64 - 1} -> Stack unit 
  (requires fun h -> live h p /\ live h tempBuffer /\ disjoint p tempBuffer /\ point_eval c h p /\
    ~ (isPointAtInfinity (fromDomainPoint #c #DH (point_as_nat c h p))))
  (ensures fun h0 _ h1 ->  modifies (loc p |+| loc tempBuffer) h0 h1 /\ 
    point_eval c h1 p /\ (
    if v mask = 0 then 
      fromDomainPoint #c #DH (point_as_nat c h0 p) == fromDomainPoint #c #DH (point_as_nat c h1 p) /\
      point_as_nat c h0 p == point_as_nat c h1 p
    else
      let pJ = fromDomainPoint #c #DH (point_as_nat c h0 p) in
      let rJ = fromDomainPoint #c #DH (point_as_nat c h1 p) in 
      pointEqual rJ (Spec.ECC.point_mult #c (- getDLP #c pJ) (basePoint #c))))


let point_neg_conditional #c p tempBuffer mask = 
    let h0 = ST.get() in 
  let len = getCoordinateLenU64 c in 
 
  let temp = sub tempBuffer (size 0) len in 
  
  let xLut = sub p (size 0) len in 
  let yLut = sub p len len in 
  let zLut = sub p (size 2 *! len) len in 
  
  felem_sub_zero #c yLut temp; 
  copy_conditional #c yLut temp mask;

   let pJ = fromDomainPoint #c #DH (point_as_nat c h0 p) in 
   let qJ = fromDomainPoint #c #DH (as_nat c h0 xLut, (0 - as_nat c h0 yLut) % getPrime c, as_nat c h0 zLut) in 

   let b = getDLP #c pJ in  


   assume (isPointAtInfinity (pointAdd #c pJ qJ));
   point_neg_lemma_infinity_indexes #c pJ;
   
   lemma_inverse_uniqueness pJ qJ (point_mult #c (-b) (basePoint #c))


val conditional_subtraction_compute_mask: #c: curve -> scalar: scalar_t #MUT #c ->
  Stack uint64 
  (requires fun h -> live h scalar)
  (ensures fun h0 mask h1 -> modifies0 h0 h1 /\ (
    let i0 = v (Lib.Sequence.index (as_seq h0 scalar) (v (getScalarLenBytes c) - 1)) in 
    if i0 % 2 = 0 then v mask == maxint U64 else v mask == 0))

let conditional_subtraction_compute_mask #c scalar = 
  let len = getScalarLenBytes c -! 1ul in 
  let i0 = index scalar len in 

  logand_mask i0 (u8 1) 1; 
  lognot_lemma (u64 0 -. to_u64 (logand i0 (u8 1)));
  lognot(u64 0 -. to_u64 (logand i0 (u8 1)))


val uploadBasePointAffine: #c: curve -> p: pointAffine c 
  -> Stack unit 
  (requires fun h -> live h p)
  (ensures fun h0 _ h1 -> modifies (loc p) h0 h1 /\ point_aff_eval c h1 p /\
    pointEqual #c (basePoint #c) (fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h1 p))))
   
let uploadBasePointAffine #c p = 
  admit();
  match c with 
  |P256 -> 
    upd p (size 0) (u64 0x1fb38ab1388ad777);
    upd p (size 1) (u64 0x1dfee06615fa309d);
    upd p (size 2) (u64 0xfcac986c3afea4a7);
    upd p (size 3) (u64 0xdf65c2da29fb821a);
    
    upd p (size 4) (u64 0xeff44e23f63f8f6d);
    upd p (size 5) (u64 0xaa02cd3ed4b681a4);
    upd p (size 6) (u64 0xdd5fda3363818af8);
    upd p (size 7) (u64 0xfc53bc2629fbf0b3)
  |P384 -> 
    upd p (size 0) (u64 0x32f2345cb5536b82);
    upd p (size 1) (u64 0x33ba95da2f7d6018);
    upd p (size 2) (u64 0xf2cd7729b1c03094);
    upd p (size 3) (u64 0x3159972fc3a90663);
    upd p (size 4) (u64 0x5827e6777fec9ce6);
    upd p (size 5) (u64 0x1af1e42821b04e1b);
    
    upd p (size 6) (u64 0xbbacc6d281184b31);
    upd p (size 7) (u64 0x5a08d98b36984428);
    upd p (size 8) (u64 0x73ba86bb86816030);
    upd p (size 9) (u64 0xe77b3c32da8c0cac);
    upd p (size 10) (u64 0x594336a7bc787585);
    upd p (size 11) (u64 0x7d25d16cde0af6c9)


val uploadMinusBasePointAffine: #c: curve 
  -> basePointNegative: pointAffine c 
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) 
  -> Stack unit 
  (requires fun h -> live h basePointNegative /\ live h tempBuffer /\ disjoint basePointNegative tempBuffer)
  (ensures fun h0 _ h1 -> modifies (loc basePointNegative |+| loc tempBuffer) h0 h1 /\
    point_aff_eval c h1 basePointNegative /\
    pointEqual #c (Spec.ECC.point_mult #c (- 1) (basePoint #c)) (fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h1 basePointNegative))))

let uploadMinusBasePointAffine #c p tempBuffer = 
  let tempBasePoint = sub tempBuffer (size 0) (getCoordinateLenU64 c *! 2ul) in 
  uploadBasePointAffine #c tempBasePoint;
    let h1 = ST.get() in 
    point_mult_1 #c (basePoint #c);
  point_affine_neg #c tempBasePoint p;
    getDLP_point_mult #c 1 (fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h1 tempBasePoint)))


val conditional_subtraction_upload_masked: #c: curve -> scalar: scalar_t #MUT #c
  -> tempPointJacobian: point c 
  -> result: point c ->
  Stack unit 
  (requires fun h -> live h scalar /\ live h tempPointJacobian /\ live h result /\ 
    disjoint result tempPointJacobian /\ point_eval c h result /\ point_eval c h tempPointJacobian)
  (ensures fun h0 _ h1 -> modifies (loc tempPointJacobian |+| loc result) h0 h1 /\ point_eval c h1 result /\ (
    let i0 = v (Lib.Sequence.index (as_seq h0 scalar) (v (getScalarLenBytes c) - 1)) in 
    if i0 % 2 = 1 then 
      point_as_nat c h1 result == point_as_nat c h0 result
    else
      point_as_nat c h1 result == point_as_nat c h0 tempPointJacobian))
      

let conditional_subtraction_upload_masked #c scalar tempPointJacobian result = 
    let h0 = ST.get() in 
  let mask = conditional_subtraction_compute_mask #c scalar in 
    let h1 = ST.get() in 
    Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h1 result;
    Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h1 tempPointJacobian;
  copy_point_conditional result tempPointJacobian mask


val conditional_substraction_: #c: curve -> result: point c -> p: point c -> scalar: scalar_t #MUT #c
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c)
  -> p0: pointAffine c 
  -> p1: point c ->
  Stack unit 
  (requires fun h -> 
    live h result /\ live h p /\ live h scalar /\ live h tempBuffer /\ live h p0 /\ live h p1 /\
    LowStar.Monotonic.Buffer.all_disjoint [loc result; loc p; loc scalar; loc tempBuffer; loc p0; loc p1] /\
    point_eval c h p /\ point_eval c h result /\
    ~ (pointEqual #c (fromDomainPoint #c #DH (point_as_nat c h p)) (Spec.ECC.point_mult #c (- 1) (basePoint #c))))
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc tempBuffer |+| loc p0 |+| loc p1) h0 h1 /\ point_eval c h1 result /\ (
    let p0 = fromDomainPoint #c #DH (point_as_nat c h0 p) in 
    let i0 = v (Lib.Sequence.index (as_seq h0 scalar) (v (getScalarLenBytes c) - 1)) in 
    if i0 % 2 = 1 then
      point_as_nat c h1 result == point_as_nat c h0 result
    else
      pointEqual #c (fromDomainPoint #c #DH (point_as_nat c h1 result)) (pointAdd #c p0 (Spec.ECC.point_mult #c (- 1) (basePoint #c)))))


let conditional_substraction_ #c result p scalar tempBuffer precompNegativePoint tempPointJacobian = 
    let h0 = ST.get() in 
  uploadMinusBasePointAffine precompNegativePoint tempBuffer;
      let h1 = ST.get() in 
      Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h1 p;
  Hacl.Impl.EC.PointAddMixed.point_add_mixed p precompNegativePoint tempPointJacobian tempBuffer;
      let h2 = ST.get() in 
      Hacl.Impl.EC.ScalarMult.Radix.curve_compatibility_with_translation_lemma_1 (fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h2 precompNegativePoint))) (Spec.ECC.point_mult #c (- 1) (basePoint #c)) (fromDomainPoint #c #DH (point_as_nat c h0 p));
      Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h2 result;
    conditional_subtraction_upload_masked #c scalar tempPointJacobian result


val conditional_substraction: #c: curve -> result: point c -> p: point c -> scalar: scalar_t #MUT #c
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) ->
  Stack unit 
  (requires fun h -> live h result /\ live h p /\ live h scalar /\ live h tempBuffer /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc result; loc p; loc scalar; loc tempBuffer] /\
    point_eval c h p /\ point_eval c h result /\
      ~ (pointEqual #c (fromDomainPoint #c #DH (point_as_nat c h p)) (Spec.ECC.point_mult #c (- 1) (basePoint #c))))
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc tempBuffer) h0 h1 /\ point_eval c h1 result /\ (
    let p0 = fromDomainPoint #c #DH (point_as_nat c h0 p) in 
    let i0 = v (Lib.Sequence.index (as_seq h0 scalar) (v (getScalarLenBytes c) - 1)) in 
    if i0 % 2 = 1 then
      point_as_nat c h1 result == point_as_nat c h0 result
    else
      pointEqual #c (fromDomainPoint #c #DH (point_as_nat c h1 result)) (pointAdd #c p0 (Spec.ECC.point_mult #c (- 1) (basePoint #c)))))

let conditional_substraction #c result p scalar tempBuffer = 
  push_frame();
    let h0 = ST.get() in 
    let len = getCoordinateLenU64 c in 
    let tempPointJacobian = create (getPointLenU64 c) (u64 0) in 
    let precompNegativePoint = create (size 2 *! len) (u64 0) in 
    conditional_substraction_ #c result p scalar tempBuffer precompNegativePoint tempPointJacobian;
  pop_frame()


val getPointDoubleNTimes: #c: curve 
  -> p: point c 
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) 
  -> k: size_t ->
  Stack unit
  (requires fun h -> live h p /\ live h tempBuffer /\ disjoint p tempBuffer /\ point_eval c h p)
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc tempBuffer) h0 h1 /\ point_eval c h1 p /\
    fromDomainPoint #c #DH (point_as_nat c h1 p) == Spec.ECC.Radix.getPointDoubleNTimes #c
      (fromDomainPoint #c #DH (point_as_nat c h0 p)) (v k))

open Lib.LoopCombinators
open Lib.Loops

let getPointDoubleNTimes #c p tempBuffer k = 
  let h0 = ST.get() in 
  let inv h (k: nat) = live h p /\ live h tempBuffer /\ disjoint p tempBuffer /\ point_eval c h p /\ 
    modifies (loc p |+| loc tempBuffer) h0 h /\
    fromDomainPoint #c #DH (point_as_nat c h p) ==
      Lib.LoopCombinators.repeat k (_point_double #c) (fromDomainPoint #c #DH (point_as_nat c h0 p)) in 
  Lib.LoopCombinators.eq_repeat0 (_point_double #c) (fromDomainPoint #c #DH (point_as_nat c h0 p));  
  for 0ul k inv (fun i -> 
    Hacl.Impl.EC.PointDouble.point_double p p tempBuffer; 
    unfold_repeat (v k) (_point_double #c) (fromDomainPoint #c #DH (point_as_nat c h0 p)) (v i))


val scalar_multiplication_cmb_step_2: #c: curve 
  -> rnaf: lbuffer uint64 (size (2 * (v (getScalarLen c) / w + 1)))
  -> result: point c
  -> j: size_t {v j < v (getLenWnaf #c) + 1}
  -> pointPrecomputed: pointAffine c
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) ->
  Stack unit 
  (requires fun h -> live h rnaf /\ live h result /\ live h pointPrecomputed /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint[loc result; loc pointPrecomputed;  loc tempBuffer] /\ (
    forall (i: nat {i < v (getScalarLen c) / w + 1}). 
      let ri = Lib.Sequence.index (as_seq h rnaf) (2 * i) in 
      v ri >= 1 /\ v ri < pow2 (w - 1)) /\ (
    forall (i: nat {i < v (getScalarLen c) / w + 1}). 
      let ri = Lib.Sequence.index (as_seq h rnaf) (2 * i + 1) in 
      v ri == 0 \/ v ri == maxint U64))
  (ensures fun h0 _ h1 -> True)
  
let scalar_multiplication_cmb_step_2 #c rnaf result j pointPrecomputed tempBuffer = 
    let h0 = ST.get() in 
  let d = index rnaf (size 2 *! j) in
  let is_neg = index rnaf (size 2 *! j +! size 1) in 
  let d = shift_right (d -! u64 1) (size 1) in 
  loopK #c d pointPrecomputed j;
  point_neg_conditional #c pointPrecomputed tempBuffer is_neg;
  Hacl.Impl.EC.PointAddMixed.point_add_mixed result pointPrecomputed result tempBuffer


inline_for_extraction noextract
val scalar_multiplication_cmb_: #c: curve -> result: point c -> 
  scalar: scalar_t #MUT #c -> 
  tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) -> 
  Stack unit
  (requires fun h -> True )
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc tempBuffer) h0 h1)

let scalar_multiplication_cmb_ #c  result scalar tempBuffer = 
  push_frame();
    let lenWnaf = getLenWnaf #c +! 1ul in 
    let rnaf2 = create (size 2 *! lenWnaf) (u64 0) in 
    let len = getCoordinateLenU64 c in
    let lut = create (size 2 *! getCoordinateLenU64 c) (u64 0) in 

    scalar_rwnaf #c rnaf2 scalar;
    
    let invJ h1 (j:nat) = True in  
    Lib.Loops.for 0ul lenWnaf invJ (fun j -> scalar_multiplication_cmb_step_2 rnaf2 result j lut tempBuffer);


    conditional_substraction #c result result scalar tempBuffer;

  pop_frame()


let scalar_multiplication_cmb_p256 = scalar_multiplication_cmb_ #P256

let scalar_multiplication_cmb_p384 = scalar_multiplication_cmb_ #P384


inline_for_extraction noextract
val scalar_multiplication_cmb: #c: curve -> result: point c -> 
  scalar: scalar_t #MUT #c -> 
  tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) -> 
  Stack unit
  (requires fun h -> True )
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc tempBuffer) h0 h1)

let scalar_multiplication_cmb #c result scalar tempBuffer = 
  match c with 
  |P256 -> scalar_multiplication_cmb_p256 result scalar tempBuffer
  |P384 -> scalar_multiplication_cmb_p384 result scalar tempBuffer
