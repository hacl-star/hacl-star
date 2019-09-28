module Hacl.Impl.LowLevel

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.Definitions
open Hacl.Spec.P256.Lemmas
open Hacl.Spec.P256.Basic
open Hacl.Spec.P256.MontgomeryMultiplication

open FStar.Math.Lemmas

open FStar.Mul

inline_for_extraction
let prime256_buffer: x: ilbuffer uint64 (size 4) {witnessed #uint64 #(size 4) x (Lib.Sequence.of_list p256_prime_list) /\ recallable x /\ felem_seq_as_nat (Lib.Sequence.of_list (p256_prime_list)) == prime256} = 
  assert_norm (felem_seq_as_nat (Lib.Sequence.of_list (p256_prime_list)) == prime256);
  createL_global p256_prime_list

open FStar.Mul

#reset-options "--z3refresh --z3rlimit 100"

val add_carry: cin: uint64 -> x: uint64 -> y: uint64 -> r: lbuffer uint64 (size 1) -> 
  Stack uint64 
    (requires fun h -> live h r)
    (ensures fun h0 c h1 -> modifies1 r h0 h1 /\ uint_v c <= 2 /\ 
      (
  let r = as_seq h1 r in 
  let r = Seq.index r 0 in 
  uint_v r + uint_v c * pow2 64 == uint_v x + uint_v y + uint_v cin)
    )

let add_carry cin x y result1 = 
  let res1 = x +. cin in 
  let c = if lt_u64 res1 cin then u64 1 else u64 0 in
  let res = res1 +. y in
  let c = if lt_u64 res res1 then c +. u64 1 else c in
  Lib.Buffer.upd result1 (size 0) res;
  c

#reset-options "--z3refresh --z3rlimit 200"

inline_for_extraction noextract
val add4: x: felem -> y: felem -> result: felem -> 
  Stack uint64
    (requires fun h -> live h x /\ live h y /\ live h result /\ eq_or_disjoint x result /\eq_or_disjoint y result )
    (ensures fun h0 c h1 -> modifies (loc result) h0 h1 /\ v c <= 1 /\
      (
  let result = as_seq h1 result in 
  let x = as_seq h0 x in 
  let y = as_seq h0 y in 
  felem_seq_as_nat result + v c * pow2 256 == felem_seq_as_nat x + felem_seq_as_nat y
      )
   )   


let add4 x y result = 
    let r0 = sub result (size 0) (size 1) in 
    let r1 = sub result (size 1) (size 1) in 
    let r2 = sub result (size 2) (size 1) in 
    let r3 = sub result (size 3) (size 1) in 

      let h0 = ST.get() in 
    let cc = add_carry (u64 0) x.(0ul) y.(0ul) r0 in 
    let cc = add_carry cc x.(1ul) y.(1ul) r1 in 
    let cc = add_carry cc x.(2ul) y.(2ul) r2 in 
    let cc = add_carry cc x.(3ul) y.(3ul) r3 in 
      
    assert(let r1_0 = as_seq h0 r1 in let r0_ = as_seq h0 result in Seq.index r0_ 1 == Seq.index r1_0 0);
    assert(let r2_0 = as_seq h0 r2 in let r0_ = as_seq h0 result in Seq.index r0_ 2 == Seq.index r2_0 0);
    assert(let r3_0 = as_seq h0 r3 in let r0_ = as_seq h0 result in Seq.index r0_ 3 == Seq.index r3_0 0);
  cc


inline_for_extraction noextract
val add4_variables: x: felem -> cin: uint64 {uint_v cin <=1} ->  y0: uint64 -> y1: uint64 -> y2: uint64 -> y3: uint64 -> result: felem -> 
  Stack uint64
    (requires fun h -> live h x /\ live h result /\ eq_or_disjoint x result )
    (ensures fun h0 c h1 -> modifies (loc result) h0 h1 /\ v c <= 1 /\  
      (
  let result = as_seq h1 result in 
  let x = as_seq h0 x in 
  let y = uint_v y0 + uint_v y1 * pow2 64 + uint_v y2 * pow2 128 + uint_v y3 * pow2 192 in 
  felem_seq_as_nat result + uint_v c * pow2 256 == felem_seq_as_nat x + y + uint_v cin 
      )
   )   


let add4_variables x cin y0 y1 y2 y3 result = 
  let h0 = ST.get() in 
    let r0 = sub result (size 0) (size 1) in      
    let r1 = sub result (size 1) (size 1) in 
    let r2 = sub result (size 2) (size 1) in 
    let r3 = sub result (size 3) (size 1) in 

    let cc0 = add_carry cin x.(0ul) y0 r0 in 
      let h1 = ST.get() in 
    let cc1 = add_carry cc0 x.(1ul) y1 r1 in 
      let h2 = ST.get() in 
    let cc = add_carry cc1 x.(2ul) y2 r2 in 
      let h3 = ST.get() in 
    let cc = add_carry cc x.(3ul) y3 r3 in 
      
    assert_norm (pow2 64 * pow2 64 = pow2 128);
    assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);
    
    assert(let r1_0 = as_seq h0 r1 in let r0_ = as_seq h0 result in Seq.index r0_ 1 == Seq.index r1_0 0);
    assert(let r2_0 = as_seq h0 r2 in let r0_ = as_seq h0 result in Seq.index r0_ 2 == Seq.index r2_0 0);
    assert(let r3_0 = as_seq h0 r3 in let r0_ = as_seq h0 result in Seq.index r0_ 3 == Seq.index r3_0 0);
    cc


val sub_borrow: cin: uint64{uint_v cin <= 1} -> x: uint64 -> y: uint64 -> r: lbuffer uint64 (size 1) -> 
  Stack uint64
    (requires fun h -> live h r)
    (ensures fun h0 c h1 -> modifies1 r h0 h1 /\ 
      (
  let r = as_seq h1 r in 
  let r = Seq.index r 0 in 
  v r - v c * pow2 64 == v x - v y - v cin)
      )


let sub_borrow cin x y result1 = 
  let res = x -. y -. cin in
  let c =
    if eq_u64 cin (u64 1) then
      (if le_u64 x y then u64 1 else u64 0)
    else
      (if lt_u64 x y then u64 1 else u64 0) in
  Lib.Buffer.upd result1 (size 0) res;
  c


val sub4_il: x: felem -> y: ilbuffer uint64 (size 4) -> result: felem -> 
  Stack uint64
    (requires fun h -> live h x /\ live h y /\ live h result /\ disjoint x result /\ disjoint y result)
    (ensures fun h0 c h1 -> modifies1 result h0 h1 /\ v c <= 1 /\
      (
  let result = as_seq h1 result in 
  let x = as_seq h0 x in 
  let y = as_seq h0 y in 
  felem_seq_as_nat result - v c * pow2 256 == felem_seq_as_nat x - felem_seq_as_nat y /\
  (if uint_v c = 0 then felem_seq_as_nat x >= felem_seq_as_nat y else felem_seq_as_nat x < felem_seq_as_nat y)
      )
   )

let sub4_il x y result = 
    let r0 = sub result (size 0) (size 1) in 
    let r1 = sub result (size 1) (size 1) in 
    let r2 = sub result (size 2) (size 1) in 
    let r3 = sub result (size 3) (size 1) in 

    let cc = sub_borrow (u64 0) x.(size 0) y.(size 0) r0 in 
    let cc = sub_borrow cc x.(size 1) y.(size 1) r1 in 
    let cc = sub_borrow cc x.(size 2) y.(size 2) r2 in 
    let cc = sub_borrow cc x.(size 3) y.(size 3) r3 in 
    cc


val sub4: x: felem -> y:felem -> result: felem -> 
  Stack uint64
    (requires fun h -> live h x /\ live h y /\ live h result /\ eq_or_disjoint x result /\ eq_or_disjoint y result)
    (ensures fun h0 c h1 -> modifies1 result h0 h1 /\ v c <= 1 /\
      (
  let result = as_seq h1 result in 
  let x = as_seq h0 x in 
  let y = as_seq h0 y in 
  felem_seq_as_nat result - v c * pow2 256 == felem_seq_as_nat x - felem_seq_as_nat y
      )
   )

let sub4 x y result = 
    let r0 = sub result (size 0) (size 1) in 
    let r1 = sub result (size 1) (size 1) in 
    let r2 = sub result (size 2) (size 1) in 
    let r3 = sub result (size 3) (size 1) in 
      
      let h0 = ST.get() in 
    let cc = sub_borrow (u64 0) x.(size 0) y.(size 0) r0 in 
    let cc = sub_borrow cc x.(size 1) y.(size 1) r1 in 
    let cc = sub_borrow cc x.(size 2) y.(size 2) r2 in 
    let cc = sub_borrow cc x.(size 3) y.(size 3) r3 in 
    
    assert(let r1_0 = as_seq h0 r1 in let r0_ = as_seq h0 result in Seq.index r0_ 1 == Seq.index r1_0 0);
    assert(let r2_0 = as_seq h0 r2 in let r0_ = as_seq h0 result in Seq.index r0_ 2 == Seq.index r2_0 0);
    assert(let r3_0 = as_seq h0 r3 in let r0_ = as_seq h0 result in Seq.index r0_ 3 == Seq.index r3_0 0);
    cc



val cmovznz4: cin: uint64 -> x: felem -> y: felem -> result: felem ->
  Stack unit
    (requires fun h -> live h x /\ live h y /\ live h result /\ disjoint x result /\ eq_or_disjoint y result)
    (ensures fun h0 _ h1 -> modifies1 result h0 h1 /\ 
      (
  let r = as_seq h1 result in 
  let x = as_seq h0 x in 
  let y = as_seq h0 y in 
  if uint_v cin = 0 then felem_seq_as_nat r == felem_seq_as_nat x else felem_seq_as_nat r == felem_seq_as_nat y
      )
    )

let cmovznz4 cin x y r =  
  let h0 = ST.get() in 
  let mask = neq_mask cin (u64 0) in 
  let r0 = logor (logand y.(size 0) mask) (logand x.(size 0) (lognot mask)) in 
  let r1 = logor (logand y.(size 1) mask) (logand x.(size 1) (lognot mask)) in 
  let r2 = logor (logand y.(size 2) mask) (logand x.(size 2) (lognot mask)) in 
  let r3 = logor (logand y.(size 3) mask) (logand x.(size 3) (lognot mask)) in 
  
  upd r (size 0) r0;
  upd r (size 1) r1;
  upd r (size 2) r2;
  upd r (size 3) r3;

  let x = as_seq h0 x in 
  let y = as_seq h0 y in 
    
    cmovznz4_lemma cin (Seq.index x 0) (Seq.index y 0);
    cmovznz4_lemma cin (Seq.index x 1) (Seq.index y 1);
    cmovznz4_lemma cin (Seq.index x 2) (Seq.index y 2);
    cmovznz4_lemma cin (Seq.index x 3) (Seq.index y 3)


#reset-options "--z3refresh --z3rlimit 200"

val reduction_prime_2prime_impl: x: felem -> result: felem -> 
  Stack unit
    (requires fun h -> live h x /\ live h result /\ eq_or_disjoint x result)
    (ensures fun h0 _ h1 -> modifies1 result h0 h1 /\ as_nat h1 result == as_nat h0 x % prime256)

#reset-options "--z3refresh --z3rlimit 300"

val lemma_reduction1: a: nat {a < pow2 256} -> r: nat{if a >= prime256 then r = a - prime256 else r = a} -> 
  Lemma (r = a % prime256)

let lemma_reduction1 a r = 
  assert_norm (pow2 256 - prime256 < prime256);
  assert(if a >= prime256 then a - prime256 < prime256 else True);
  assert(if a >= prime256 then r < prime256 else True);
  assert(if a >= prime256 then r = a % prime256 else True);
  assert(if a < prime256 then r < prime256 else True);
  assert(if a < prime256 then r = a % prime256 else True);
  assert(r = a % prime256)



let reduction_prime_2prime_impl x result = 
  push_frame();
  let tempBuffer = create (size 4) (u64 0) in 
    recall_contents prime256_buffer (Lib.Sequence.of_list p256_prime_list);
        let h0 = ST.get() in 
    let c = sub4_il x prime256_buffer tempBuffer in 
      let h1 = ST.get() in 
      assert(felem_seq_as_nat (as_seq h1 tempBuffer) = felem_seq_as_nat (as_seq h0 x) - prime256 + uint_v c * pow2 256);

      assert(let x = felem_seq_as_nat (as_seq h0 x) in if x < prime256 then uint_v c = 1 else uint_v c = 0);
    cmovznz4 c tempBuffer x result;
      let h2 = ST.get() in 
    lemma_reduction1 (felem_seq_as_nat (as_seq h0 x)) (felem_seq_as_nat (as_seq h2 result));
  pop_frame()  


inline_for_extraction noextract
val reduction_prime256_2prime256_with_carry_impl: cin: uint64 -> x: felem -> result: felem ->
  Stack unit 
    (requires fun h -> live h x /\ live h result /\  eq_or_disjoint x result /\ 
      (let x = as_seq h x in  felem_seq_as_nat x + uint_v cin * pow2 256) < 2 * prime256)
    (ensures fun h0 _ h1 -> modifies1 result h0 h1 /\ 
      (
  let r = as_seq h1 result in 
  let x = as_seq h0 x in 
  felem_seq_as_nat r = (felem_seq_as_nat x + uint_v cin * pow2 256) % prime256
      )
    )  


let reduction_prime256_2prime256_with_carry_impl cin x result = 
  push_frame();
    let tempBuffer = create (size 4) (u64 0) in 
    let tempBufferForSubborrow = create (size 1) (u64 0) in 
    recall_contents prime256_buffer (Lib.Sequence.of_list p256_prime_list);
      let h0  = ST.get() in 
    let c = sub4_il x prime256_buffer tempBuffer in
      let h1 = ST.get() in 
	assert(let x = felem_seq_as_nat (as_seq h0 x) in if x < prime256 then uint_v c = 1 else uint_v c = 0);
	assert(felem_seq_as_nat (as_seq h1 tempBuffer)  = felem_seq_as_nat (as_seq h0 x) - prime256 + uint_v c * pow2 256);
    let carry = sub_borrow c cin (u64 0) tempBufferForSubborrow in 
      assert(if uint_v cin > 0 then uint_v carry == 0 else if uint_v c = 0 then uint_v carry = 0 else uint_v carry = 1);
      cmovznz4 carry tempBuffer x result;
      let h3 = ST.get() in 
      modulo_addition_lemma (felem_seq_as_nat (as_seq h3 result)) prime256 1;
      assert((felem_seq_as_nat (as_seq h3 result) + prime256) % prime256 = (felem_seq_as_nat (as_seq h3 result)) % prime256);
      small_modulo_lemma_1 (as_nat h3 result) prime256;
      assert(let resultN = felem_seq_as_nat (as_seq h3 result) in 
	if uint_v cin = 1 then 
	  if uint_v c = 0 then 
	    resultN = felem_seq_as_nat (as_seq h0 x) - prime256 /\
	    (felem_seq_as_nat (as_seq h0 x) + uint_v cin * pow2 256) % prime256 = resultN
	  else 
	    resultN = felem_seq_as_nat (as_seq h0 x) - prime256 + pow2 256 /\
	    resultN < prime256 /\
	    resultN % prime256 == resultN  /\
	    (felem_seq_as_nat (as_seq h0 x) + uint_v cin * pow2 256) % prime256 == resultN  
       else 
        True );

      assert(let resultN = felem_seq_as_nat (as_seq h3 result) in 
	if uint_v cin = 0 then 
	  if uint_v c = 0 then 
	    uint_v carry = 0 /\
	    resultN = felem_seq_as_nat (as_seq h0 x) - prime256 /\
	    (felem_seq_as_nat (as_seq h0 x) + uint_v carry * pow2 256) % prime256  == resultN
	  else 
	    uint_v carry = 1 /\
	    resultN = felem_seq_as_nat (as_seq h0 x) /\
	    (felem_seq_as_nat (as_seq h0 x) + uint_v cin * pow2 256) % prime256  = resultN % prime256 
	  else True  );
 
 pop_frame()   



val shift_256_impl: i: felem -> o: lbuffer uint64 (size 8) -> 
  Stack unit 
    (requires fun h -> live h i /\ live h o /\ disjoint i o)
    (ensures fun h0 _ h1 -> modifies1 o h0 h1 /\ 
      (
  let i = as_seq h0 i in 
  let o = as_seq h1 o in 
  felem_seq_as_nat_8 o == felem_seq_as_nat i * pow2 256 
      )
    )

let shift_256_impl i o = 
  upd o (size 0) (u64 0);
  upd o (size 1) (u64 0);
  upd o (size 2) (u64 0);
  upd o (size 3) (u64 0);
  upd o (size 4) i.(size 0);
  upd o (size 5) i.(size 1);
  upd o (size 6) i.(size 2);
  upd o (size 7) i.(size 3);

  assert_norm(pow2 64 * pow2 64 * pow2 64 = pow2 192);
  assert_norm(pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
  assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64= pow2 (5 * 64));
  assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64 * pow2 64 = pow2 (6 * 64));
  assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64* pow2 64 * pow2 64 = pow2 (7 * 64));
  assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64* pow2 64 * pow2 64 * pow2 64 = pow2 (8 * 64))

val lemma_t_computation: t: uint64{uint_v t == 0 \/ uint_v t == 1} -> 
  Lemma
    (
        let t0 = u64 0 in 
  let t1 = (u64 0) -. (t <<. (size 32)) in 
  let t2 = (u64 0) -. t in 
  let t3 = (t <<. (size 32)) -. (t <<. (size 1)) in 
  let s = uint_v t0 + uint_v t1 * pow2 64 + uint_v t2 * pow2 128 + uint_v t3 * pow2 192 in 
  if uint_v t = 1 then s == pow2 256 - prime256 - 1 else s == 0
    )

let lemma_t_computation t = 
  let t0 = u64 0 in 
  let t1 = (u64 0) -. (t <<. (size 32)) in 
  let t2 = (u64 0) -. t in 
  let t3 = (t <<. (size 32)) -. (t <<. (size 1)) in 

  let s = uint_v t0 + uint_v t1 * pow2 64 + uint_v t2 * pow2 128 + uint_v t3 * pow2 192 in  

  assert_norm(if uint_v t = 1 then uint_v t1 = 18446744069414584320 else uint_v t1 = 0);
  assert_norm(if uint_v t = 1 then uint_v t2 = 18446744073709551615 else uint_v t2 = 0);
  assert_norm(if uint_v t = 1 then uint_v t3 = 4294967294 else uint_v t3 = 0);
 
  assert_norm(18446744069414584320 * pow2 64 + 18446744073709551615 * pow2 128 + 4294967294 * pow2 192 = pow2 256 - prime256 - 1)


val lemma_t_computation2: t: uint64 {uint_v t == 0 \/ uint_v t == 1} ->
  Lemma
    (
      let t0 = (u64 0) -. t in 
      let t1 = ((u64 0) -. t) >>. (size 32) in 
      let t2 = u64 0 in 
      let t3 = t -. (t <<. (size 32)) in 
      let s = uint_v t0 + uint_v t1 * pow2 64 + uint_v t2 * pow2 128 + uint_v t3 * pow2 192 in 
  if uint_v t = 1 then s == prime256 else s == 0
    )

let lemma_t_computation2 t = 
      let t0 = (u64 0) -. t in 
      let t1 = ((u64 0) -. t) >>. (size 32) in 
      let t2 = u64 0 in 
      let t3 = t -. (t <<. (size 32)) in 

  let s = uint_v t0 + uint_v t1 * pow2 64 + uint_v t2 * pow2 128 + uint_v t3 * pow2 192 in  

  assert_norm(if uint_v t = 1 then uint_v t0 == 18446744073709551615 else uint_v t0 = 0);
  assert_norm(if uint_v t = 1 then uint_v t1 == 4294967295 else uint_v t1 = 0);
  assert_norm(if uint_v t = 1 then uint_v t3 == 18446744069414584321 else uint_v t3 = 0);

  assert_norm(18446744073709551615 + 4294967295 * pow2 64 + 18446744069414584321 * pow2 192 = prime256)


#set-options "--z3rlimit 500" 
val p256_add: arg1: felem -> arg2: felem ->  out: felem -> Stack unit 
  (requires (fun h0 ->  
    live h0 arg1 /\ live h0 arg2 /\ live h0 out /\ eq_or_disjoint arg1 out /\ eq_or_disjoint arg2 out /\
    (
      let arg1_as_seq = as_seq h0 arg1 in let arg2_as_seq = as_seq h0 arg2 in 
      felem_seq_as_nat arg1_as_seq < prime256 /\ felem_seq_as_nat arg2_as_seq < prime256 
    )
   )
  )
  (ensures (fun h0 _ h1 -> modifies1 out h0 h1 /\ 
    (
      let x = as_seq h0 arg1 in  
      let y = as_seq h0 arg2 in 
      let out = as_seq h1 out in 
      felem_seq_as_nat out == (felem_seq_as_nat x + felem_seq_as_nat y) % prime256 /\
      out == felem_add_seq (as_seq h0 arg1) (as_seq h0 arg2)
    )
  ))


let p256_add arg1 arg2 out = 
  let h0 = ST.get() in   
  let t = add4 arg1 arg2 out in 
    let h1 = ST.get() in 
      assert(let out = as_seq h1 out in let x = as_seq h0 arg1 in let y = as_seq h0 arg2 in 
      felem_seq_as_nat out + uint_v t * pow2 256 == felem_seq_as_nat x + felem_seq_as_nat y);
  lemma_t_computation t;
  reduction_prime256_2prime256_with_carry_impl t out out;
    let h2 = ST.get() in 
    assert(felem_seq_as_nat (as_seq h2 out) == (felem_seq_as_nat (as_seq h0 arg1) + felem_seq_as_nat (as_seq h0 arg2)) % prime256);
    additionInDomain2Nat (felem_seq_as_nat (as_seq h0 arg1)) (felem_seq_as_nat (as_seq h0 arg2));
    inDomain_mod_is_not_mod (fromDomain_ (felem_seq_as_nat (as_seq h0 arg1)) + fromDomain_ (felem_seq_as_nat (as_seq h0 arg2)));
    lemma_eq_funct (as_seq h2 out) (felem_add_seq (as_seq h0 arg1) (as_seq h0 arg2))


#set-options "--z3rlimit 500" 
val p256_double: arg1: felem ->  out: felem -> Stack unit 
  (requires (fun h0 ->  live h0 arg1 /\ live h0 out /\  eq_or_disjoint arg1 out /\
    (
      let arg1_as_seq = as_seq h0 arg1 in felem_seq_as_nat arg1_as_seq < prime256
    )
  ))
  (ensures (fun h0 _ h1 -> modifies1 out h0 h1 /\ 
    (
      let x = as_seq h0 arg1 in 
      let out = as_seq h1 out in 
      felem_seq_as_nat out == (2 * felem_seq_as_nat x) % prime256 /\
      felem_seq_as_nat out < prime256
    )
  ))


let p256_double arg1 out = 
    push_frame();
  let h0 = ST.get() in 
  let t = add4 arg1 arg1 out in 
    let h1 = ST.get() in 
      assert(let out = as_seq h1 out in let x = as_seq h0 arg1 in 
      felem_seq_as_nat out + uint_v t * pow2 256 == felem_seq_as_nat x + felem_seq_as_nat x);
  lemma_t_computation t;
  reduction_prime256_2prime256_with_carry_impl t out out;
  pop_frame()



val p256_sub: arg1: felem -> arg2: felem -> out: felem -> Stack unit 
  (requires 
    (fun h0 -> live h0 out /\ live h0 arg1 /\ live h0 arg2 /\ eq_or_disjoint arg1 out /\ eq_or_disjoint arg2 out /\
    as_nat h0 arg1 < prime256 /\ as_nat h0 arg2 < prime256))
    (ensures (fun h0 _ h1 -> modifies1 out h0 h1 /\ 
      (
	let x = as_seq h0 arg1 in 
	let y = as_seq h0 arg2 in 
	let out = as_seq h1 out in 
	felem_seq_as_nat out == (felem_seq_as_nat x - felem_seq_as_nat y) % prime256 /\
	out == felem_sub_seq (as_seq h0 arg1) (as_seq h0 arg2)
      )
  ))

let p256_sub arg1 arg2 out = 
    push_frame();
    let h0 = ST.get() in 
  let t = sub4 arg1 arg2 out in 
    let h1 = ST.get() in 
    lemma_t_computation2 t;
    assert(let out = as_seq h1 out in let x = as_seq h0 arg1 in let y = as_seq h0 arg2 in 
      felem_seq_as_nat out - uint_v t * pow2 256 == felem_seq_as_nat x - felem_seq_as_nat y);
    assert(if felem_seq_as_nat (as_seq h0 arg1) < felem_seq_as_nat (as_seq h0 arg2) then uint_v t == 1 else uint_v t == 0);
    
  let t0 = (u64 0) -. t in 
  let t1 = ((u64 0) -. t) >>. (size 32) in 
  let t2 = u64 0 in 
  let t3 = t -. (t <<. (size 32)) in 
    assert(if uint_v t = 1 then uint_v t0 + uint_v t1 * pow2 64 + uint_v t2 * pow2 128 + uint_v t3 * pow2 192 == prime256 else True);
    modulo_addition_lemma  (let x = as_seq h0 arg1 in let y = as_seq h0 arg2 in (felem_seq_as_nat x - felem_seq_as_nat y)) prime256 1;
    assert(let x = as_seq h0 arg1 in let y = as_seq h0 arg2 in  (felem_seq_as_nat x - felem_seq_as_nat y + prime256) % prime256 = (felem_seq_as_nat x - felem_seq_as_nat y) % prime256);

  let c = add4_variables out (u64 0)  t0 t1 t2 t3 out in 
    let h2 = ST.get() in 
      assert(let result = as_seq h2 out in 
      let x = as_seq h0 arg1 in let y = as_seq h0 arg2 in 
      let s = uint_v t0 + uint_v t1 * pow2 64 + uint_v t2 * pow2 128 + uint_v t3 * pow2 192 in 
      if felem_seq_as_nat x - felem_seq_as_nat y >= 0 then 
      begin
	  modulo_lemma (felem_seq_as_nat x - felem_seq_as_nat y) prime256;
	  felem_seq_as_nat result == (felem_seq_as_nat x - felem_seq_as_nat y) % prime256
      end
      else
          begin
	    modulo_lemma (felem_seq_as_nat result) prime256;
            felem_seq_as_nat result == (felem_seq_as_nat x - felem_seq_as_nat y) % prime256
	  end
  );

    substractionInDomain2Nat (felem_seq_as_nat (as_seq h0 arg1)) (felem_seq_as_nat (as_seq h0 arg2));
    inDomain_mod_is_not_mod (fromDomain_ (felem_seq_as_nat (as_seq h0 arg1)) - fromDomain_ (felem_seq_as_nat (as_seq h0 arg2)));
    lemma_eq_funct (as_seq h2 out) (felem_sub_seq (as_seq h0 arg1) (as_seq h0 arg2));
    
    pop_frame()
    
