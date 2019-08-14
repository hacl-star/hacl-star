module Hacl.Spec.P256.Core

open Lib.IntTypes
open FStar.Math.Lemmas
open FStar.Math.Lib

open Hacl.Spec.P256.Definitions
open Hacl.Spec.P256.Lemmas
open Hacl.Spec.P256.Basic

open FStar.Mul


inline_for_extraction noextract
val lt_u64:a:uint64 -> b:uint64 -> Tot bool

let lt_u64 a b =
  let open Lib.RawIntTypes in
  FStar.UInt64.(u64_to_UInt64 a <^ u64_to_UInt64 b)


inline_for_extraction noextract
val gt: a: uint64 -> b: uint64 -> Tot uint64

let gt a b = 
  if lt_u64 b a then u64 1 else u64 0


let eq_u64 a b =
  let open Lib.RawIntTypes in
  FStar.UInt64.(u64_to_UInt64 a =^ u64_to_UInt64 b)


let eq_0_u64 a = 
  let b = u64 0 in 
  eq_u64 a b


inline_for_extraction noextract
val cmovznz: cin : uint64 ->  x: uint64 -> y: uint64 -> 
  Pure uint64
  (requires True)
  (ensures fun r -> if uint_v cin = 0 then uint_v r == uint_v x else uint_v r == uint_v y)

let cmovznz cin x y  = 
    let x2 = neq_mask cin (u64 0) in 
    let x3 = logor (logand y x2) (logand x (lognot x2)) in
    let ln = lognot (neq_mask cin (u64 0)) in 
    cmovznz4_lemma cin x y;
    x3

inline_for_extraction noextract
val cmovznz4: cin: uint64 -> x: felem4 -> y: felem4 -> Pure (r: felem4)
(requires True)
(ensures fun r -> if uint_v cin = 0 then as_nat4 r == as_nat4 x else as_nat4 r == as_nat4 y)

let cmovznz4 cin (x0, x1, x2, x3) (y0, y1, y2, y3) = 
  let mask = neq_mask cin (u64 0) in 
  let r0 = logor (logand y0 mask) (logand x0 (lognot mask)) in 
        cmovznz4_lemma cin x0 y0;
  let r1 = logor (logand y1 mask) (logand x1 (lognot mask)) in 
        cmovznz4_lemma cin x1 y1;
  let r2 = logor (logand y2 mask) (logand x2 (lognot mask))  in 
        cmovznz4_lemma cin x2 y2;
  let r3 = logor (logand y3 mask) (logand x3 (lognot mask))  in 
        cmovznz4_lemma cin x3 y3;
  (r0, r1, r2, r3)


val reduction_prime_2prime_with_carry: carry: uint64{uint_v carry <= 1} -> 
  a: felem4{as_nat4 a + uint_v carry * pow2 256 < 2 * prime256} -> 
  Tot (r: felem4 {as_nat4 r == (as_nat4 a + uint_v carry * pow2 256) % prime256})


#set-options "--z3rlimit 300 --z3refresh"

let reduction_prime_2prime_with_carry carry a = 
  lemma_nat_4 a;
    assert_norm (as_nat4  (u64 0xffffffffffffffff, u64 0xffffffff, u64 0, u64 0xffffffff00000001) == prime256);
  let (cin, (r0, r1, r2, r3)) = sub4 a  (u64 0xffffffffffffffff, u64 0xffffffff, u64 0, u64 0xffffffff00000001) in 
    assert(as_nat4 (r0, r1, r2, r3) - uint_v cin * pow2 256 = as_nat4 a - prime256);
  let (r, c) = subborrow carry (u64 0) cin  in  
  let result = cmovznz4 c (r0, r1, r2, r3) a in
    assert(if uint_v carry > 0 then uint_v c == 0 else if  uint_v carry = 0 && uint_v cin = 0 then uint_v c = 0 else uint_v c = 1);

    assert(if (uint_v carry * pow2 256 + as_nat4 a) >= prime256 then
      begin
	if uint_v cin = 0 then 
	  as_nat4 result == (as_nat4 a + uint_v carry * pow2 256) % prime256
	else 
	  as_nat4 result == (as_nat4 a + uint_v carry * pow2 256) % prime256
      end
      else as_nat4 result == (as_nat4 a + uint_v carry * pow2 256) % prime256);
  result


let felem_add arg1 arg2 = 
  let (x8, c) = add4 arg1 arg2 in 
  let result = reduction_prime_2prime_with_carry x8 c in 
  result

val lemma_felem_sub: r: nat {r < pow2 256} -> r_: nat {r_ < pow2 256} -> a: nat {a < prime256} -> b: nat {b < prime256} -> 
  c0: nat {c0 <= 1} -> c1: nat {c1 <=1} -> prime256_temp: nat -> Lemma
    (requires (
      (if c0 = 0 then prime256_temp == 0  else prime256_temp = prime256) /\
      r_ - c0 * pow2 256 = a - b /\
      r + c1 * pow2 256 = r_ + prime256_temp))
    (ensures ( r = (a - b) % prime256)) 
      

let lemma_felem_sub r r_ a b c0 c1 prime256_temp = 
  assert(r + c1 * pow2 256 = a - b + c0 * pow2 256 + prime256_temp);
  assert(if c0 = 0 then c1 = 0 else True);
  assert(if c1 = 1 then c0 = 1 else True);

  assert(if c0 = 0 then r = a - b  else r = a - b + prime256);
  modulo_addition_lemma (a - b) prime256 1;
  assert((a - b + prime256) % prime256 == (a - b) % prime256);

  assert(if c0 = 0 
    then 
      begin 
      modulo_lemma r prime256;
      r = (a - b) % prime256
      end
    else 
      begin
	modulo_lemma r prime256;
	r = (a - b) % prime256

      end )

val lemma_felem_sub_types: r: felem4 -> r_: felem4 -> a: felem4{as_nat4 a < prime256} -> b: felem4{as_nat4 b < prime256} -> 
  c0: uint64 {uint_v c0 <= 1} -> c1: uint64 {uint_v c1 <= 1} -> 
  prime256_temp: felem4 {if uint_v c0 = 0 then as_nat4 prime256_temp == 0 else as_nat4 prime256_temp == prime256} -> 
  Lemma (requires
      (as_nat4 r_ - uint_v c0 * pow2 256 = as_nat4 a - as_nat4 b /\
      as_nat4 r + uint_v c1 * pow2 256 = as_nat4 r_ + as_nat4 prime256_temp))
      (ensures (as_nat4 r == (as_nat4 a - as_nat4 b) % prime256))

let lemma_felem_sub_types r r_ a b c0 c1 prime256_temp = 
  let r = as_nat4 r in 
  let r_ = as_nat4 r_ in 
  let a = as_nat4 a in 
  let b = as_nat4 b in 
  let c0 = uint_v c0 in 
  let c1 = uint_v c1 in 
  let prime256_temp = as_nat4 prime256_temp in 
  lemma_felem_sub r r_ a b c0 c1 prime256_temp


(*  opening anything calls growing up the code*)
#reset-options "--z3rlimit 1000"
let felem_sub (a0, a1, a2, a3) (b0, b1, b2, b3) = 
  let (c0, (r_0, r_1, r_2, r_3)) = sub4  (a0, a1, a2, a3) (b0, b1, b2, b3) in 
    assert(if as_nat4 (a0, a1, a2, a3) < as_nat4 (b0, b1, b2, b3) then uint_v c0 == 1 else uint_v c0 == 0);

  let x9 = cmovznz c0 (u64 0) (u64 0xffffffffffffffff) in  
 
  let prime_temp_0 = logand (u64 0xffffffffffffffff) x9 in 
  let prime_temp_1 = logand (u64 0xffffffff) x9 in 
  let prime_temp_2 = u64 0 in 
  let prime_temp_3 = logand (u64 0xffffffff00000001) x9 in 
  let prime_temp = (prime_temp_0, prime_temp_1, prime_temp_2, prime_temp_3) in  

  log_and (u64 0xffffffffffffffff) x9;
  log_and (u64 0xffffffff) x9;
  log_and (u64 0xffffffff00000001) x9;
  assert_norm (as_nat4 (u64 0xffffffffffffffff, u64 0xffffffff, u64 0, u64 0xffffffff00000001) == prime256);

  let (c1, (r0, r1, r2, r3)) = add4 (prime_temp_0, prime_temp_1, prime_temp_2, prime_temp_3) (r_0, r_1, r_2, r_3) in 
  
  assert(if uint_v c0 = 0 then as_nat4 prime_temp == 0 else as_nat4 prime_temp == prime256);
  assert(as_nat4 (r_0, r_1, r_2, r_3) - uint_v c0 * pow2 256 = as_nat4 (a0, a1, a2, a3) -  as_nat4 (b0, b1, b2, b3));
  assert(as_nat4 (r0, r1, r2, r3) + uint_v c1 * pow2 256 = as_nat4 (r_0, r_1, r_2, r_3) + as_nat4 (prime_temp_0, prime_temp_1, prime_temp_2, prime_temp_3));
  
  lemma_felem_sub_types (r0, r1, r2, r3) (r_0, r_1, r_2, r_3) (a0, a1, a2, a3) (b0, b1, b2, b3) c0 c1 prime_temp;
  (r0, r1, r2, r3)



#reset-options "--z3rlimit 300 --z3refresh"

(*to prove *)
let reduction_prime_2prime (a0, a1, a2, a3) = 
  assert_norm (as_nat4 (u64 0xffffffffffffffff, u64 0xffffffff, u64 0, u64 0xffffffff00000001) == prime256);
  let (x16, (r0, r1, r2, r3)) = sub4 (a0, a1, a2, a3) (u64 0xffffffffffffffff, u64 0xffffffff, u64 0, u64 0xffffffff00000001) in 
  assert(if as_nat4 (a0, a1, a2, a3) < prime256 then uint_v x16 == 1 else uint_v x16 == 0);
  let result = cmovznz4 x16 (r0, r1, r2, r3) (a0, a1, a2, a3) in
  assert(if as_nat4 (a0, a1, a2, a3) >= prime256 then as_nat4 result == (as_nat4 (a0, a1, a2, a3) - prime256) % prime256 else as_nat4 result == as_nat4 (a0, a1, a2, a3) % prime256);
  result


inline_for_extraction noextract
val shift_carry: x: uint64 -> cin: uint64{uint_v cin <=1} -> Tot (r: uint64 {uint_v r = (uint_v x * 2) % pow2 64 + uint_v cin})

let shift_carry x cin = 
  add (Lib.IntTypes.shift_left x (size 1)) cin


val lemma_get_number: a: nat {a < pow2 64} -> Lemma (
	let mask = 0x7fffffffffffffff in 
	let carry= if a> mask then 1 else 0 in 
	(a * 2) = (a * 2) % pow2 64 + carry * pow2 64)	

let lemma_get_number a = ()


val shift_left_lemma: a0: nat {a0 < pow2 64} -> a1: nat {a1 < pow2 64} -> a2: nat {a2 < pow2 64} -> a3: nat {a3 < pow2 64 /\
a0 + a1 * pow2 64 + a2 * pow2 128 + a3 * pow2 192 < prime256} -> Lemma (let input = a0 + a1 * pow2 64 + a2 * pow2 128 + a3 * pow2 192 in 
  let mask = 0x7fffffffffffffff in 
 
  let carry0 = if a0 > mask then 1 else 0 in 
  let carry1 = if a1 > mask then 1 else 0 in 
  let carry2 = if a2 > mask then 1 else 0 in 
  let carry3 = if a3 > mask then 1 else 0 in 

  let a0_u = (a0 * 2) % pow2 64 + 0 in 
  let a1_u = (a1 * 2) % pow2 64 + carry0 in    
  let a2_u = (a2 * 2) % pow2 64 + carry1 in 
  let a3_u = (a3 * 2) % pow2 64 + carry2 in

  input * 2 = a0_u + a1_u * pow2 64 + a2_u * pow2 128 + a3_u * pow2 192 + carry3 * pow2 256 /\
  a0_u + a1_u * pow2 64 + a2_u * pow2 128 + a3_u * pow2 192 + carry3 * pow2 256 < 2 * prime256)


let shift_left_lemma a0 a1 a2 a3 = 
  let input: nat = a0+ a1 * pow2 64 + a2 * pow2 128 + a3 * pow2 192 in 

  let mask = 0x7fffffffffffffff in 
  let carry0 = if a0 > mask then 1 else 0 in 
  let carry1 = if a1 > mask then 1 else 0 in 
  let carry2 = if a2 > mask then 1 else 0 in 
  let carry3 = if a3 > mask then 1 else 0 in 


  let a0_u = (a0 * 2) % pow2 64  in 
   lemma_get_number a0;
  let a1_u = (a1 * 2) % pow2 64 + carry0 in   
    lemma_get_number a1;
  let a2_u = (a2 * 2) % pow2 64 + carry1 in 
    lemma_get_number a2;
  let a3_u = (a3 * 2) % pow2 64 + carry2 in 
    lemma_get_number a3;

  assert_norm (pow2 64 * pow2 64 = pow2 128);
  assert_norm (pow2 64 * pow2 128 = pow2 192);
  assert_norm (pow2 64 * pow2 192 = pow2 256)


#reset-options "--z3rlimit 500"
let shift_left_felem (a0, a1, a2, a3) =  
  let mask = u64 0x7fffffffffffffff in   
  let carry0 = gt a0 mask in 
  let carry1 = gt a1 mask in 
  let carry2 = gt a2 mask in 
  let carry3 = gt a3 mask in 

  let a0_updated = shift_carry a0 (u64 0) in 
  let a1_updated = shift_carry a1 carry0 in 
  let a2_updated = shift_carry a2 carry1 in 
  let a3_updated = shift_carry a3 carry2 in 

  assert_norm(pow2 64 * pow2 64 = pow2 128);
  assert_norm(pow2 64 * pow2 64 * pow2 64 = pow2 192);

  shift_left_lemma (uint_v a0) (uint_v a1) (uint_v a2) (uint_v a3); 
  assert(as_nat4 (a0, a1, a2, a3) * 2 = uint_v a0_updated + uint_v a1_updated * pow2 64 + uint_v a2_updated * pow2 128 + uint_v  a3_updated * pow2 192 + uint_v carry3 * pow2 256);
  assert_norm(uint_v a2_updated * pow2 64 * pow2 64 == uint_v a2_updated * pow2 128);
  assert_norm(uint_v a3_updated * pow2 64 * pow2 64 * pow2 64 == uint_v a3_updated * pow2 192);
  reduction_prime_2prime_with_carry carry3 (a0_updated,  a1_updated,  a2_updated, a3_updated)


let upload_prime () = 
  assert_norm (as_nat4 (u64 (0xffffffffffffffff), u64 (0x00000000ffffffff), u64 (0), u64 (0xffffffff00000001))  == prime256);
  (u64 (0xffffffffffffffff), u64 (0x00000000ffffffff), u64 (0), u64 (0xffffffff00000001)) 


let shift_256 (c0, c1, c2, c3)  = 
    assert_norm(pow2 64 * pow2 64 = pow2 128);
    assert_norm(pow2 64 * pow2 64 * pow2 64 = pow2 192);
    assert_norm(pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
    assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64= pow2 (5 * 64));
    assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64 * pow2 64 = pow2 (6 * 64));
    assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64* pow2 64 * pow2 64 = pow2 (7 * 64));
    assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64* pow2 64 * pow2 64 * pow2 64 = pow2 (8 * 64));
    (u64(0), u64(0), u64 (0), u64 (0), c0, c1, c2, c3)


val lemma_wide: o: felem8 -> Lemma (wide_as_nat4 o =
  (let (o0, o1, o2, o3, o4, o5, o6, o7) = o in 
   v o0 + v o1 * pow2 64 +  v o2 * pow2 (64 * 2) + v o3 * pow2 (3 * 64) + 
   v o4 * pow2 (4 * 64) + v o5 * pow2 (5 * 64) +  v o6 * pow2 (6 * 64) + v o7 * pow2 (7 * 64)))

let lemma_wide o = 
    assert_norm(pow2 64 * pow2 64 = pow2 128);
    assert_norm(pow2 64 * pow2 64 * pow2 64 = pow2 192);
    assert_norm(pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
    assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64= pow2 (5 * 64));
    assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64 * pow2 64 = pow2 (6 * 64));
    assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64* pow2 64 * pow2 64 = pow2 (7 * 64));
    ()


let add8  (a0, a1, a2, a3, a4, a5, a6, a7) (b0, b1, b2, b3, b4, b5, b6, b7) = 
    assert_norm(pow2 64 * pow2 64 = pow2 128);
    assert_norm(pow2 64 * pow2 64 * pow2 64 = pow2 192);
    assert_norm(pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
    assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64= pow2 (5 * 64));
    assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64 * pow2 64 = pow2 (6 * 64));
    assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64* pow2 64 * pow2 64 = pow2 (7 * 64));
    assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64* pow2 64 * pow2 64 * pow2 64 = pow2 512);
  let c3, (o0, o1, o2, o3) = add4 (a0, a1, a2, a3) (b0, b1, b2, b3) in 
  let o4, c4 = addcarry a4 b4 c3 in
  let o5, c5 = addcarry a5 b5 c4 in 
  let o6, c6 = addcarry a6 b6 c5 in 
  let o7, c7 = addcarry a7 b7 c6 in 
  assert(wide_as_nat4 (a0, a1, a2, a3, a4, a5, a6, a7)  + wide_as_nat4 (b0, b1, b2, b3, b4, b5, b6, b7) = 
   v o0 + v o1 * pow2 64 +  v o2 * pow2 (2 * 64) + v o3 * pow2 (3 * 64) + 
   v o4 * pow2 (4 * 64) + v o5 * pow2 (5 * 64) +  v o6 * pow2 (6 * 64) + v o7 * pow2 (7 * 64) + v c7 * pow2 512);
  lemma_wide (o0, o1, o2, o3, o4, o5, o6, o7);
  (c7, o0, o1, o2, o3, o4, o5, o6, o7)


 
inline_for_extraction noextract
val add8_without_carry: a: felem8 {wide_as_nat4 a < prime256 * prime256} -> b: felem8 {wide_as_nat4 b < pow2 320}  -> Tot (r:felem8 {wide_as_nat4 r = wide_as_nat4 a + wide_as_nat4 b})


let add8_without_carry (a0, a1, a2, a3, a4, a5, a6, a7) (b0, b1, b2, b3, b4, b5, b6, b7) = 
  let (carry, r0, r1, r2, r3, r4, r5, r6, r7)  = add8 (a0, a1, a2, a3, a4, a5, a6, a7) (b0, b1, b2, b3, b4, b5, b6, b7) in 
  assert_norm(pow2 320 + pow2 449 < pow2 512);   
  assert(uint_v carry = 0);
  (r0, r1, r2, r3, r4, r5, r6, r7)

#reset-options "--z3refresh --z3rlimit 500"

val lemma_add: a: felem8 -> b: felem8{wide_as_nat4 a + wide_as_nat4 b < pow2 512} -> Lemma 
  (
    let (carry, r0, r1, r2, r3, r4, r5, r6, r7) = add8 a b in 
     wide_as_nat4 (r0, r1, r2, r3, r4, r5, r6, r7) == wide_as_nat4 a + wide_as_nat4 b)
     

let lemma_add a b = 
  let (carry, r0, r1, r2, r3, r4, r5, r6, r7) = add8 a b in 
    assert(uint_v carry * pow2 512 + wide_as_nat4 (r0, r1, r2, r3, r4, r5, r6, r7) = wide_as_nat4 a  + wide_as_nat4 b);
    assert(uint_v carry * pow2 512 + wide_as_nat4 (r0, r1, r2, r3, r4, r5, r6, r7) < pow2 512);
    assert(uint_v carry = 0);
    assert(wide_as_nat4 (r0, r1, r2, r3, r4, r5, r6, r7) = wide_as_nat4 a  + wide_as_nat4 b)


let add8_without_carry1 (a0, a1, a2, a3, a4, a5, a6, a7) (b0, b1, b2, b3, b4, b5, b6, b7) =
  let (carry, r0, r1, r2, r3, r4, r5, r6, r7)  = add8 (a0, a1, a2, a3, a4, a5, a6, a7) (b0, b1, b2, b3, b4, b5, b6, b7) in 
  assert(uint_v carry * pow2 512 + wide_as_nat4 (r0, r1, r2, r3, r4, r5, r6, r7) == wide_as_nat4 (a0, a1, a2, a3, a4, a5, a6, a7) + wide_as_nat4 (b0, b1, b2, b3, b4, b5, b6, b7));
  assert_norm(prime256 * prime256  + pow2 320 < pow2 512);   
  lemma_add (a0, a1, a2, a3, a4, a5, a6, a7) (b0, b1, b2, b3, b4, b5, b6, b7); 
  (r0, r1, r2, r3, r4, r5, r6, r7)

#reset-options "--z3refresh --z3rlimit 300"
noextract inline_for_extraction
val shortened_mul: a: felem4 -> b: uint64 -> Tot (r: felem8 {as_nat4 a * uint_v b = wide_as_nat4 r
  /\ wide_as_nat4 r < pow2 320})

let shortened_mul arg b = 
  let (c, (f0, f1, f2, f3)) = mul1 arg b in 
  assert(as_nat4 (f0, f1, f2, f3) + uint_v c * pow2 256 == as_nat4 arg * uint_v b);
   assert_norm(pow2 64 * pow2 64 = pow2 128);
   assert_norm(pow2 64 * pow2 64 * pow2 64 = pow2 192);
   assert_norm(pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
   assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64= pow2 320);
   assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64 * pow2 64 = pow2 (6 * 64));
   assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64* pow2 64 * pow2 64 = pow2 (7 * 64));
   f0, f1, f2, f3, c, (u64 0), (u64 0), u64(0)


inline_for_extraction noextract
val mod_64: a: felem8 -> Tot (r: uint64 {wide_as_nat4 a % pow2 64 = uint_v r})

let mod_64 (a0, a1, a2, a3, a4, a5, a6, a7) =  a0

inline_for_extraction noextract
val shift_8: a: felem8 -> Tot (r: felem8 {wide_as_nat4 a / pow2 64 = wide_as_nat4 r})

let shift_8 (a0, a1, a2, a3, a4, a5, a6, a7) = 
  (a1, a2, a3, a4, a5, a6, a7, (u64 0))

 
#reset-options "--z3rlimit 1000 --z3refresh"  
val lemma_less_than_primes : a: nat {a < prime256} -> b: nat {b < prime256} -> Lemma (ensures (
  let s = 64 in 
  let t = a * b in 

  let t1 = t % pow2 s in 
  let t2 = t1 * prime256 in 
  let t3 = t + t2 in 
  let tU = t3 / pow2 s in 
 
  let t = tU in 
  let t1 = t % pow2 s in 
  let t2 = t1 * prime256 in 
  let t3 = t + t2 in 
  let tU = t3 / pow2 s in 

  let t = tU in 
  let t1 = t % pow2 s in 
  let t2 = t1 * prime256 in 
  let t3 = t + t2 in 
  let tU = t3 / pow2 s in 

  let t = tU in 
  let t1 = t % pow2 s in  
  let t2 = t1 * prime256 in 
  let t3 = t + t2 in 
  let tU = t3 / pow2 s in 
  tU < 2 * prime256))


private let mul_lemma_ (a: nat) (b: nat) (c: nat) : Lemma (requires (a < c /\ b < c)) (ensures (a * b < c * c)) = ()
private let mul_lemma_st (a: nat) (b: nat) (c: nat) : Lemma (requires (a <= c /\ b <= c)) (ensures (a * b <= c * c)) = ()

private let mul_lemma_1 (a: nat) (c: nat) (b: pos) : Lemma (requires (a < c)) (ensures (a * b < c * b)) = ()

private let add_l (a: nat) (b: nat) (c: nat) (d: nat) : Lemma (requires a < c /\ b < d) (ensures (a + b < c + d)) = ()

private let add_l2 (a: nat) (b: nat) (c: nat) (d: nat) : Lemma (requires a <= c /\ b < d) (ensures (a + b < c + d)) = ()

#reset-options "--z3rlimit 100 --z3refresh"  

private let reduced_prime_sq (a: nat {a < prime256}) (b: nat {b < prime256}) : Lemma (a * b < prime256 * prime256 - 2 * prime256 + 2) = 
  mul_lemma_ a b prime256;
  assert(a <= prime256 - 1);
  assert(b <= prime256 - 1);
  mul_lemma_st a b prime256;
  assert(a * b <= (prime256 -1) * (prime256 -1));
  assert(a * b <= prime256 * prime256 - 2 * prime256 + 1)


let lemma_less_than_primes a b = 
  let s = 64 in 
  let t = a * b in
    mul_lemma_ a b prime256;
    reduced_prime_sq a b; 
    assert(t < prime256 * prime256 -  2 * prime256 + 2);
  let t1 = t % pow2 64 in 
  let t2 = t1 * prime256 in 
  let t3 = t + t2 in 
  let tU = t3 / pow2 64 in 
    mul_lemma_1 t1 (pow2 64) prime256;
    add_l t t2 (prime256 * prime256 -  2 * prime256 + 2) (pow2 64 * prime256);
    assert(t3 < (prime256 * prime256 -  2 * prime256 + 2 + pow2 64 * prime256));
    assert(tU <= (prime256 * prime256 -  2 * prime256 + 2 + pow2 64 * prime256) / pow2 64);

  let tNew0 = tU in 
    let r = (prime256 * prime256 -  2 * prime256 + 2 + pow2 64 * prime256) / pow2 64 in 
    assert(tNew0 <= r); 
  let t1 = tNew0 % pow2 s in 
  let t2 = t1 * prime256 in 
  let t3 = tNew0 + t2 in 
  let tU = t3 / pow2 s in 
    mul_lemma_1 t1 (pow2 64) prime256;
    add_l2 tNew0 t2 r (pow2 64 * prime256);
    assert(t3 < pow2 64 * prime256 + r);
    assert(tU <= (pow2 64 * prime256 + r) / pow2 64);
    
  let tNew1 = tU in 
    let r = (pow2 64 * prime256 + r) / pow2 64 in 
    assert(tNew1 <= r);
  let t1 = tNew1 % pow2 s in 
  let t2 = t1 * prime256 in 
  let t3 = tNew1 + t2 in 
  let tU = t3 / pow2 s in 
    mul_lemma_1 t1 (pow2 64) prime256;
    add_l2 tNew1 t2 r (pow2 64 * prime256);
    assert(tU <= (pow2 64 * prime256 + r) / pow2 64);
    
  let t = tU in 
    let r = (pow2 64 * prime256 + r) / pow2 64 in 
    assert(t <= r);
  let t1 = t % pow2 s in  
  let t2 = t1 * prime256 in 
  let t3 = t + t2 in 
  let tU = t3 / pow2 s in 
    mul_lemma_1 t1 (pow2 64) prime256;
    add_l2 t t2 r (pow2 64 * prime256);
    assert(tU <= (pow2 64 * prime256 + r) / pow2 64);
    assert_norm((pow2 64 * prime256 + r) / pow2 64 < 2 * prime256);
  assert(tU < 2 * prime256)


val montgomery_multiplication_one_round_proof: t: felem8 {wide_as_nat4 t < pow2 449} -> 
  result: felem8 {wide_as_nat4 result = (wide_as_nat4 t + (wide_as_nat4 t % pow2 64) * prime256) / pow2 64} ->
  co: nat{ co % prime256 == wide_as_nat4 t % prime256} -> Lemma (
    wide_as_nat4 result % prime256 == co * modp_inv2 (pow2 64) % prime256 /\
    wide_as_nat4 result = (wide_as_nat4 t + (wide_as_nat4 t % pow2 64) * prime256) / pow2 64 /\
    wide_as_nat4 result < pow2 449)

let montgomery_multiplication_one_round_proof t result co = 
  let prime256U = upload_prime () in 
  let t1 = mod_64 t in 
  let t2 = shortened_mul prime256U t1 in 
    assert_norm(pow2 256 * pow2 64 = pow2 320);
    assert(wide_as_nat4 t2 = uint_v t1 * prime256);
  let t3 = add8_without_carry t t2 in 
    assert_norm (pow2 320 + pow2 449 < pow2 513);
  let result = shift_8 t3 in 
    lemma_div_lt (wide_as_nat4 t3) 513 64;
    mult_one_round (wide_as_nat4 t) co


inline_for_extraction noextract
val montgomery_multiplication_one_round: t: felem8{wide_as_nat4 t < pow2 449} -> 
  prime256U: felem4 {as_nat4 prime256U == prime256} -> 
Tot (result: felem8 { wide_as_nat4 result = (wide_as_nat4 t + (wide_as_nat4 t % pow2 64) * prime256) / pow2 64 /\wide_as_nat4 result < pow2 449})

let montgomery_multiplication_one_round (a0, a1, a2, a3, a4, a5, a6, a7) (prim0, prim1, prim2, prim3) = 
  let t1 = mod_64 (a0, a1, a2, a3, a4, a5, a6, a7) in 
  let (t2_0, t2_1, t2_2, t2_3, t2_4, t2_5, t2_6, t2_7) = shortened_mul (prim0, prim1, prim2, prim3) t1 in 
    assert_norm(pow2 256 * pow2 64 = pow2 320);
    assert(wide_as_nat4 (t2_0, t2_1, t2_2, t2_3, t2_4, t2_5, t2_6, t2_7) = uint_v t1 * prime256);
  let (t3_0, t3_1, t3_2, t3_3, t3_4, t3_5, t3_6, t3_7) = add8_without_carry (a0, a1, a2, a3, a4, a5, a6, a7) (t2_0, t2_1, t2_2, t2_3, t2_4, t2_5, t2_6, t2_7) in 
    assert_norm (pow2 320 + pow2 449 < pow2 513); 
    lemma_div_lt (wide_as_nat4 (t3_0, t3_1, t3_2, t3_3, t3_4, t3_5, t3_6, t3_7)) 513 64;
  let (r_0, r_1, r_2, r_3, r_4, r_5, r_6, r_7)  = shift_8 (t3_0, t3_1, t3_2, t3_3, t3_4, t3_5, t3_6, t3_7)  in 
    lemma_div_lt (wide_as_nat4 (t3_0, t3_1, t3_2, t3_3, t3_4, t3_5, t3_6, t3_7)) 513 64;
  (r_0, r_1, r_2, r_3, r_4, r_5, r_6, r_7)


#reset-options "--z3refresh --z3rlimit  500" 
let montgomery_multiplication (a0, a1, a2, a3) (b0, b1, b2, b3) = 
  let (prim0, prim1, prim2, prim3) = upload_prime () in 
  assert_norm(as_nat4 (prim0, prim1, prim2, prim3) == prime256);
  assert_norm(prime256 < pow2 256);
  assert_norm (pow2 256 * pow2 256 = pow2 512);
  assert_norm (pow2 320 + pow2 512 < pow2 513); 
 
  border_felem4 (a0, a1, a2, a3) ;
  border_felem4 (b0, b1, b2, b3) ;
  lemma_mult_lt_sqr (as_nat4 (a0, a1, a2, a3)) (as_nat4 (b0, b1, b2, b3)) (pow2 256);

    let (t_0, t_1, t_2, t_3, t_4, t_5, t_6, t_7) = mul4 (a0, a1, a2, a3)  (b0, b1, b2, b3) in 
    let t1 = mod_64 (t_0, t_1, t_2, t_3, t_4, t_5, t_6, t_7) in 
    let (t2_0, t2_1, t2_2, t2_3, t2_4, t2_5, t2_6, t2_7) = shortened_mul (prim0, prim1, prim2, prim3) t1 in 
      mul_lemma_ (as_nat4(a0, a1, a2, a3)) (as_nat4(b0, b1, b2, b3)) prime256;
    let (t3_0, t3_1, t3_2, t3_3, t3_4, t3_5, t3_6, t3_7) = add8_without_carry1 (t_0, t_1, t_2, t_3, t_4, t_5, t_6, t_7) (t2_0, t2_1, t2_2, t2_3, t2_4, t2_5, t2_6, t2_7) in  
    let (st0, st1, st2, st3, st4, st5, st6, st7) = shift_8 (t3_0, t3_1, t3_2, t3_3, t3_4, t3_5, t3_6, t3_7) in  
      lemma_div_lt (wide_as_nat4 (t3_0, t3_1, t3_2, t3_3, t3_4, t3_5, t3_6, t3_7)) 513 64; 
      mult_one_round (wide_as_nat4 (t_0, t_1, t_2, t_3, t_4, t_5, t_6, t_7)) (as_nat4 (a0, a1, a2, a3) * as_nat4  (b0, b1, b2, b3) );
      lemma_mul_nat (as_nat4  (a0, a1, a2, a3)) (as_nat4  (b0, b1, b2, b3)) (modp_inv2 (pow2 64));

    let (st10, st11, st12, st13, st14, st15, st16, st17)  = montgomery_multiplication_one_round (st0, st1, st2, st3, st4, st5, st6, st7) (prim0, prim1, prim2, prim3) in
    montgomery_multiplication_one_round_proof (st0, st1, st2, st3, st4, st5, st6, st7)  (st10, st11, st12, st13, st14, st15, st16, st17) (as_nat4  (a0, a1, a2, a3) * as_nat4 (b0, b1, b2, b3) * modp_inv2 (pow2 64));
    lemma_mul_nat4 (as_nat4  (a0, a1, a2, a3)) (as_nat4 (b0, b1, b2, b3)) (modp_inv2 (pow2 64)) (modp_inv2(pow2 64));
  let (st20, st21, st22, st23, st24, st25, st26, st27) = montgomery_multiplication_one_round (st10, st11, st12, st13, st14, st15, st16, st17) (prim0, prim1, prim2, prim3) in 
    montgomery_multiplication_one_round_proof (st10, st11, st12, st13, st14, st15, st16, st17) (st20, st21, st22, st23, st24, st25, st26, st27) (as_nat4  (a0, a1, a2, a3) * as_nat4  (b0, b1, b2, b3) * modp_inv2 (pow2 64) * modp_inv2 (pow2 64));
    lemma_mul_nat5 (as_nat4  (a0, a1, a2, a3)) (as_nat4 (b0, b1, b2, b3)) (modp_inv2 (pow2 64)) (modp_inv2 (pow2 64)) (modp_inv2 (pow2 64));
  let (st30, st31, st32, st33, st34, st35, st36, st37) = montgomery_multiplication_one_round (st20, st21, st22, st23, st24, st25, st26, st27) (prim0, prim1, prim2, prim3) in 
    montgomery_multiplication_one_round_proof (st20, st21, st22, st23, st24, st25, st26, st27) 
      (st30, st31, st32, st33, st34, st35, st36, st37)  (as_nat4 (a0, a1, a2, a3)* as_nat4 (b0, b1, b2, b3) * modp_inv2 (pow2 64) * modp_inv2 (pow2 64) * modp_inv2(pow2 64));
    lemma_decrease_pow (as_nat4  (a0, a1, a2, a3) * as_nat4 (b0, b1, b2, b3));
    lemma_less_than_primes (as_nat4  (a0, a1, a2, a3)) (as_nat4 (b0, b1, b2, b3));
    assert(wide_as_nat4  (st30, st31, st32, st33, st34, st35, st36, st37) < 2 * prime256);
    lemma_prime_as_wild_nat  (st30, st31, st32, st33, st34, st35, st36, st37);
  reduction_prime_2prime_with_carry st34 (st30, st31, st32, st33)


let cube_tuple (a0, a1, a2, a3) = 
  let (s0, s1, s2, s3) = montgomery_multiplication (a0, a1, a2, a3) (a0, a1, a2, a3) in 
  let (c0, c1, c2, c3) = montgomery_multiplication (s0, s1, s2, s3) (a0, a1, a2, a3) in 
    lemma_mul_nat (as_nat4 (a0, a1, a2, a3)) (as_nat4 (a0, a1, a2, a3)) (modp_inv2 (pow2 256));
    lemma_mul_nat2   (as_nat4 (a0, a1, a2, a3)) (modp_inv2 (pow2 256));
    lemma_brackets ((as_nat4 (a0, a1, a2, a3) * as_nat4 (a0, a1, a2, a3) * modp_inv2(pow2 256)) % prime256) (as_nat4 (a0, a1, a2, a3)) (modp_inv2 (pow2 256));
    lemma_mod_mul_distr_l (as_nat4 (a0, a1, a2, a3) * as_nat4 (a0, a1, a2, a3) * modp_inv2(pow2 256)) (as_nat4 (a0, a1, a2, a3) * modp_inv2 (pow2 256)) prime256;
    lemma_brackets5 (as_nat4 (a0, a1, a2, a3)) (as_nat4 (a0, a1, a2, a3)) (modp_inv2 (pow2 256)) (as_nat4 (a0, a1, a2, a3)) (modp_inv2 (pow2 256));
    lemma_distr_mult (as_nat4 (a0, a1, a2, a3)) (as_nat4 (a0, a1, a2, a3)) (modp_inv2 (pow2 256)) (as_nat4 (a0, a1, a2, a3)) (modp_inv2 (pow2 256));
  (c0, c1, c2, c3) 


let quatre_tuple (a0, a1, a2, a3) = 
  let (s0, s1, s2, s3) = montgomery_multiplication (a0, a1, a2, a3) (a0, a1, a2, a3) in 
  let (c0, c1, c2, c3) = montgomery_multiplication (s0, s1, s2, s3) (s0, s1, s2, s3) in 
  let a = (a0, a1, a2, a3) in 
     lemma_brackets ((as_nat4 a * as_nat4 a * modp_inv2 (pow2 256)) % prime256) ((as_nat4 a * as_nat4 a * modp_inv2 (pow2 256)) % prime256) (modp_inv2 (pow2 256));
    lemma_mod_mul_distr_l (as_nat4 a * as_nat4 a * modp_inv2 (pow2 256)) (((as_nat4 a * as_nat4 a * modp_inv2 (pow2 256)) % prime256) * modp_inv2 (pow2 256)) prime256;
    lemma_brackets (as_nat4 a * as_nat4 a * modp_inv2 (pow2 256)) ((as_nat4 a * as_nat4 a * modp_inv2 (pow2 256)) % prime256) (modp_inv2 (pow2 256));
    lemma_distr_mult3 (as_nat4 a * as_nat4 a * modp_inv2 (pow2 256)) ((as_nat4 a * as_nat4 a * modp_inv2 (pow2 256)) % prime256) (modp_inv2 (pow2 256));
    lemma_brackets_l (as_nat4 a * as_nat4 a * modp_inv2 (pow2 256)) (modp_inv2 (pow2 256)) ((as_nat4 a * as_nat4 a * modp_inv2 (pow2 256)) % prime256);
    lemma_mod_mul_distr_r ((as_nat4 a * as_nat4 a * modp_inv2 (pow2 256)) * modp_inv2 (pow2 256)) (as_nat4 a * as_nat4 a * modp_inv2 (pow2 256)) prime256;
    lemma_brackets_l (as_nat4 a * as_nat4 a * modp_inv2 (pow2 256))(modp_inv2 (pow2 256)) (as_nat4 a * as_nat4 a * modp_inv2 (pow2 256));
    lemma_distr_mult3 (as_nat4 a * as_nat4 a * modp_inv2 (pow2 256)) (modp_inv2 (pow2 256)) (as_nat4 a * as_nat4 a * modp_inv2 (pow2 256));
    lemma_twice_brackets (as_nat4 a) (as_nat4 a) (modp_inv2 (pow2 256)) (as_nat4 a) (as_nat4 a) (modp_inv2 (pow2 256)) (modp_inv2 (pow2 256));
    lemma_distr_mult7  (as_nat4 a) (as_nat4 a) (modp_inv2 (pow2 256)) (as_nat4 a) (as_nat4 a) (modp_inv2 (pow2 256)) (modp_inv2 (pow2 256));
    (c0, c1, c2, c3)

val lemma_three: a: nat -> Lemma (a * 2 + a == 3 * a)
let lemma_three a = ()

val lemma_four: a: nat -> Lemma ((a * 2) * 2 == 4 * a)
let lemma_four a = ()

val lemma_eight: a: nat -> Lemma  ((a * 4) * 2 == 8 * a)
let lemma_eight a = ()

val lemma_minus_three: a: nat -> Lemma (0 - 3 * a == (-3) * a)
let lemma_minus_three a = ()


let multByThree_tuple (a0, a1, a2, a3) = 
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 
    let (m0, m1, m2, m3) = shift_left_felem (a0, a1, a2, a3) in 
    let (th0, th1, th2, th3) = felem_add (m0, m1, m2, m3) (a0, a1, a2, a3) in 
    lemma_mod_plus_distr_l (as_nat4 (a0, a1, a2, a3)  * 2) (as_nat4 (a0, a1, a2, a3) ) prime256;
    lemma_three (as_nat4 (a0, a1, a2, a3) );
    (th0, th1, th2, th3) 


let multByFour_tuple (a0, a1, a2, a3) = 
  let (m0, m1, m2, m3) = shift_left_felem (a0, a1, a2, a3) in 
  let (th0, th1, th2, th3) = shift_left_felem (m0, m1, m2, m3) in 
    lemma_mod_mul_distr_l (as_nat4 (a0, a1, a2, a3) * 2) 2 prime256;
    lemma_four (as_nat4 (a0, a1, a2, a3));
  (th0, th1, th2, th3)


let multByEight_tuple (a0, a1, a2, a3) = 
  let (m0, m1, m2, m3) = multByFour_tuple (a0, a1, a2, a3)  in 
  let  (th0, th1, th2, th3)  = shift_left_felem (m0, m1, m2, m3) in 
    lemma_mod_mul_distr_l (as_nat4 (a0, a1, a2, a3)  * 4) 2 prime256;
    lemma_eight (as_nat4 (a0, a1, a2, a3) );
  (th0, th1, th2, th3) 


let multByMinusThree_tuple (a0, a1, a2, a3) = 
  let (th0, th1, th2, th3) = multByThree_tuple (a0, a1, a2, a3) in 
  (* let zero = (u64 (0), u64(0), u64(0), u64(0)) in  *)
    assert_norm (as_nat4 (u64 (0), u64(0), u64(0), u64(0))  = 0);
  let (c0, c1, c2, c3) = felem_sub (u64 (0), u64(0), u64(0), u64(0))  (th0, th1, th2, th3) in 
  lemma_mod_sub_distr 0 (as_nat4 (a0, a1, a2, a3) * 3) prime256;
  lemma_minus_three (as_nat4 (a0, a1, a2, a3));
  (c0, c1, c2, c3)

 
(* takes felem4 and returns boolean *)
let isOne_tuple (a0, a1, a2, a3) = 
  let r0 = eq_mask a0 (u64 1) in 
  let r1 = eq_mask a1 (u64 0) in 
  let r2 = eq_mask a2 (u64 0) in 
  let r3 = eq_mask a3 (u64 0) in  
  let r01 = logand r0 r1 in 
    logand_lemma r0 r1;
  let r23 = logand r2 r3 in 
    lemma_log_and1 r2 r3;
  let r = logand r01 r23 in 
    lemma_log_and1 r01 r23;
  let f = eq_u64 r (u64 0xffffffffffffffff) in  
  f


let equalFelem (a_0, a_1, a_2, a_3) (b_0, b_1, b_2, b_3) = 
    let r_0 = eq_mask a_0 b_0 in 
      eq_mask_lemma a_0 b_0;
    let r_1 = eq_mask a_1 b_1 in 
      eq_mask_lemma a_1 b_1;
    let r_2 = eq_mask a_2 b_2 in 
      eq_mask_lemma a_2 b_2;
    let r_3 = eq_mask a_3 b_3 in 
      eq_mask_lemma a_3 b_3;
    let r01 = logand r_0 r_1 in 
      logand_lemma r_0 r_1;
    let r23 = logand r_2 r_3 in 
      logand_lemma r_2 r_3;
    let r = logand r01 r23 in 
      logand_lemma r01 r23;
      lemma_equality (a_0, a_1, a_2, a_3) (b_0, b_1, b_2, b_3) ; 
    r


let isZero_tuple_u (a0, a1, a2, a3)  = 
  let r0 = eq_mask a0 (u64 0) in 
  let r1 = eq_mask a1 (u64 0) in 
  let r2 = eq_mask a2 (u64 0) in 
  let r3 = eq_mask a3 (u64 0) in 
  let r01 = logand r0 r1 in 
     lemma_log_and1 r0 r1;
  let r23 = logand r2 r3 in 
     lemma_log_and1 r2 r3;
  let r = logand r01 r23 in 
   lemma_log_and1 r01 r23;
      r
  

let isZero_tuple_b (a0, a1, a2, a3)  = 
  assert_norm (0xffffffffffffffff = pow2 64 - 1);
  let r0 = eq_mask a0 (u64 0) in 
  let r1 = eq_mask a1 (u64 0) in 
  let r2 = eq_mask a2 (u64 0) in 
  let r3 = eq_mask a3 (u64 0) in 
  let r01 = logand r0 r1 in 
    lemma_log_and1 r0 r1;
  let r23 = logand r2 r3 in 
    lemma_log_and1 r2 r3;
  let r = logand r01 r23 in 
    lemma_log_and1 r01 r23;    
  let f = eq_u64 r (u64 0xffffffffffffffff) in  
   f
   
