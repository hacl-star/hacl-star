module Hacl.Impl.LowLevel

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open FStar.Mul

open Hacl.Spec.P384.Definition
open Lib.IntTypes.Intrinsics


#set-options " --z3rlimit 100 --ifuel  0 --fuel 0"
inline_for_extraction noextract
val add6_0: x: felem6_buffer -> y: felem6_buffer-> result: felem6_buffer -> Stack uint64 
  (requires fun h -> live h x /\ live h y /\ live h result /\ eq_or_disjoint x result /\ eq_or_disjoint y result)
  (ensures fun h0 c h1 -> modifies (loc result) h0 h1 /\ 
    v c <= 1 /\
    (
      let r0 = Lib.Sequence.index (as_seq h1 result) 0 in 
      let r1 = Lib.Sequence.index (as_seq h1 result) 1 in 
      let r2 = Lib.Sequence.index (as_seq h1 result) 2 in 
  
      let a0 = Lib.Sequence.index (as_seq h0 x) 0 in 
      let a1 = Lib.Sequence.index (as_seq h0 x) 1 in 
      let a2 = Lib.Sequence.index (as_seq h0 x) 2 in 

      let b0 = Lib.Sequence.index (as_seq h0 y) 0 in 
      let b1 = Lib.Sequence.index (as_seq h0 y) 1 in 
      let b2 = Lib.Sequence.index (as_seq h0 y) 2 in 

      let r3_0 = Lib.Sequence.index (as_seq h0 result) 3 in 
      let r3_1 = Lib.Sequence.index (as_seq h1 result) 3 in 
      
      let r4_0 = Lib.Sequence.index (as_seq h0 result) 4 in 
      let r4_1 = Lib.Sequence.index (as_seq h1 result) 4 in 
      
      let r5_0 = Lib.Sequence.index (as_seq h0 result) 5 in 
      let r5_1 = Lib.Sequence.index (as_seq h1 result) 5 in 

      v r0 + v r1 * pow2 (1 * 64) + v r2 * pow2 (2 * 64) + v c * pow2 (3 * 64) ==
      v a0 + v b0 + v a1 * pow2 64 + v b1 * pow2 64 + v a2 * pow2 (2 * 64) + v b2 * pow2 (2 * 64) /\

      r3_0 == r3_1 /\ r4_0 == r4_1 /\ r5_0 == r5_1

    )
  )

let add6_0 x y result =
  let h0 = ST.get() in 
  assert_norm (pow2 64 * pow2 64 = pow2 (2 * 64));
  assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 (3 * 64));
  let r0 = sub result (size 0) (size 1) in 
  let r1 = sub result (size 1) (size 1) in 
  let r2 = sub result (size 2) (size 1) in 

  let r3 = sub result (size 3) (size 1) in 
  let r4 = sub result (size 4) (size 1) in 
  let r5 = sub result (size 5) (size 1) in 

  assert(Lib.Sequence.index (as_seq h0 r3) 0 == Lib.Sequence.index (as_seq h0 result) 3);
  assert(Lib.Sequence.index (as_seq h0 r4) 0 == Lib.Sequence.index (as_seq h0 result) 4);
  assert(Lib.Sequence.index (as_seq h0 r5) 0 == Lib.Sequence.index (as_seq h0 result) 5);

  assert(let r4_0 = as_seq h0 r1 in let r0_ = as_seq h0 result in Seq.index r0_ 1 == Seq.index r4_0 0);
  assert(let r5_0 = as_seq h0 r2 in let r0_ = as_seq h0 result in Seq.index r0_ 2 == Seq.index r5_0 0);

  let cc0 = add_carry_u64 (u64 0) x.(0ul) y.(0ul) r0 in 
  let cc1 = add_carry_u64 cc0 x.(1ul) y.(1ul) r1 in 
  let cc2 = add_carry_u64 cc1 x.(2ul) y.(2ul) r2 in 
  
  cc2


inline_for_extraction noextract
val add6_with_carry0: cc2: uint64 ->  x: felem6_buffer -> y: felem6_buffer-> result: felem6_buffer -> Stack uint64 
  (requires fun h -> live h x /\ live h y /\ live h result /\ eq_or_disjoint x result /\ eq_or_disjoint y result /\ uint_v cc2 <= 1)
  (ensures fun h0 c h1 -> modifies (loc result) h0 h1 /\ 
    v c <= 1 /\
    (
      let r0 = Lib.Sequence.index (as_seq h1 result) 0 in 
      let r1 = Lib.Sequence.index (as_seq h1 result) 1 in 
      let r2 = Lib.Sequence.index (as_seq h1 result) 2 in 
  
      let a0 = Lib.Sequence.index (as_seq h0 x) 0 in 
      let a1 = Lib.Sequence.index (as_seq h0 x) 1 in 
      let a2 = Lib.Sequence.index (as_seq h0 x) 2 in 

      let b0 = Lib.Sequence.index (as_seq h0 y) 0 in 
      let b1 = Lib.Sequence.index (as_seq h0 y) 1 in 
      let b2 = Lib.Sequence.index (as_seq h0 y) 2 in 

      let r3_0 = Lib.Sequence.index (as_seq h0 result) 3 in 
      let r3_1 = Lib.Sequence.index (as_seq h1 result) 3 in 
      
      let r4_0 = Lib.Sequence.index (as_seq h0 result) 4 in 
      let r4_1 = Lib.Sequence.index (as_seq h1 result) 4 in 
      
      let r5_0 = Lib.Sequence.index (as_seq h0 result) 5 in 
      let r5_1 = Lib.Sequence.index (as_seq h1 result) 5 in 

      v r0 + v r1 * pow2 (1 * 64) + v r2 * pow2 (2 * 64) + v c * pow2 (3 * 64) ==
      v a0 + v b0 + v a1 * pow2 64 + v b1 * pow2 64 + v a2 * pow2 (2 * 64) + v b2 * pow2 (2 * 64) + uint_v cc2 /\

      r3_0 == r3_1 /\ r4_0 == r4_1 /\ r5_0 == r5_1

    )
  )


let add6_with_carry0 cc2 x y result =
  let h0 = ST.get() in 
  assert_norm (pow2 64 * pow2 64 = pow2 (2 * 64));
  assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 (3 * 64));
  let r0 = sub result (size 0) (size 1) in 
  let r1 = sub result (size 1) (size 1) in 
  let r2 = sub result (size 2) (size 1) in 

  let r3 = sub result (size 3) (size 1) in 
  let r4 = sub result (size 4) (size 1) in 
  let r5 = sub result (size 5) (size 1) in 

  assert(Lib.Sequence.index (as_seq h0 r3) 0 == Lib.Sequence.index (as_seq h0 result) 3);
  assert(Lib.Sequence.index (as_seq h0 r4) 0 == Lib.Sequence.index (as_seq h0 result) 4);
  assert(Lib.Sequence.index (as_seq h0 r5) 0 == Lib.Sequence.index (as_seq h0 result) 5);

  assert(let r4_0 = as_seq h0 r1 in let r0_ = as_seq h0 result in Seq.index r0_ 1 == Seq.index r4_0 0);
  assert(let r5_0 = as_seq h0 r2 in let r0_ = as_seq h0 result in Seq.index r0_ 2 == Seq.index r5_0 0);

  let cc0 = add_carry_u64 cc2 x.(0ul) y.(0ul) r0 in 
  let cc1 = add_carry_u64 cc0 x.(1ul) y.(1ul) r1 in 
  let cc2 = add_carry_u64 cc1 x.(2ul) y.(2ul) r2 in 
  
  cc2



inline_for_extraction noextract
val add6_1: x: felem6_buffer -> y: felem6_buffer -> result: felem6_buffer -> cc2: uint64 -> 
  Stack uint64 
  (requires fun h -> live h x /\ live h y /\ live h result /\ eq_or_disjoint x result /\
    eq_or_disjoint y result /\ v cc2 <= 1)
  (ensures fun h0 c h1 -> modifies (loc result) h0 h1 /\ 
    uint_v c <= 1 /\
    (
      let r0_0 = Lib.Sequence.index (as_seq h0 result) 0 in 
      let r0_1 = Lib.Sequence.index (as_seq h1 result) 0 in 
      
      let r1_0 = Lib.Sequence.index (as_seq h0 result) 1 in 
      let r1_1 = Lib.Sequence.index (as_seq h1 result) 1 in 
      
      let r2_0 = Lib.Sequence.index (as_seq h0 result) 2 in 
      let r2_1 = Lib.Sequence.index (as_seq h1 result) 2 in 
	   
      let r3 = Lib.Sequence.index (as_seq h1 result) 3 in 
      let r4 = Lib.Sequence.index (as_seq h1 result) 4 in 
      let r5 = Lib.Sequence.index (as_seq h1 result) 5 in 
  
      let a3 = Lib.Sequence.index (as_seq h0 x) 3 in 
      let a4 = Lib.Sequence.index (as_seq h0 x) 4 in 
      let a5 = Lib.Sequence.index (as_seq h0 x) 5 in 

      let b3 = Lib.Sequence.index (as_seq h0 y) 3 in 
      let b4 = Lib.Sequence.index (as_seq h0 y) 4 in 
      let b5 = Lib.Sequence.index (as_seq h0 y) 5 in 
  
      v r3 * pow2 (3 * 64) + v r4 * pow2 (4 * 64) + v r5 * pow2 (5 * 64) + v c * pow2 (6 * 64) ==
      v a3 * pow2 (3 * 64) + v b3 * pow2 (3 * 64) + v a4 * pow2 (4 * 64) + v b4 * pow2 (4 * 64) + v a5 * pow2 (5 * 64) + v b5 * pow2 (5 * 64) + uint_v cc2 * pow2 (3 * 64) /\
      r0_0 == r0_1 /\ r1_0 == r1_1 /\ r2_0 == r2_1
    )
  )

let add6_1 x y result cc2 =
  let h0 = ST.get() in 
  
  assert_norm (pow2 64 * pow2 64 = pow2 (2 * 64));
  assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 (3 * 64));
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (4 * 64));
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (5 * 64));
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (6 * 64));

  let r0 = sub result (size 0) (size 1) in 
  let r1 = sub result (size 1) (size 1) in 
  let r2 = sub result (size 2) (size 1) in 

  let r3 = sub result (size 3) (size 1) in 
  let r4 = sub result (size 4) (size 1) in 
  let r5 = sub result (size 5) (size 1) in 

  let cc3 = add_carry_u64 cc2 x.(3ul) y.(3ul) r3 in 
  let cc4 = add_carry_u64 cc3 x.(4ul) y.(4ul) r4 in 
  let cc5 = add_carry_u64 cc4 x.(5ul) y.(5ul) r5 in 

  let h1 = ST.get() in 


  assert(let r3_0 = as_seq h0 r3 in let r0_ = as_seq h0 result in Seq.index r0_ 3 == Seq.index r3_0 0);   
  assert(let r4_0 = as_seq h0 r4 in let r0_ = as_seq h0 result in Seq.index r0_ 4 == Seq.index r4_0 0);
  assert(let r5_0 = as_seq h0 r5 in let r0_ = as_seq h0 result in Seq.index r0_ 5 == Seq.index r5_0 0);

  assert(Lib.Sequence.index (as_seq h0 r0) 0 == Lib.Sequence.index (as_seq h0 result) 0);
  assert(Lib.Sequence.index (as_seq h0 r1) 0 == Lib.Sequence.index (as_seq h0 result) 1);
  assert(Lib.Sequence.index (as_seq h0 r2) 0 == Lib.Sequence.index (as_seq h0 result) 2);


  cc5



val add6: x: felem6_buffer -> y: felem6_buffer -> result: felem6_buffer -> 
  Stack uint64
    (requires fun h -> live h x /\ live h y /\ live h result /\ eq_or_disjoint x result /\ eq_or_disjoint y result)
    (ensures fun h0 c h1 -> modifies (loc result) h0 h1 /\ v c <= 1 /\ 
      as_nat6 h1 result + v c * pow2 (6 * 64) == as_nat6 h0 x + as_nat6 h0 y)   

let add6 x y result =    
  let cc2 = add6_0 x y result in 
  add6_1 x y result cc2


val add6_with_carry: c: uint64 -> x: felem6_buffer -> y: felem6_buffer -> result: felem6_buffer -> 
  Stack uint64 
    (requires fun h -> uint_v c <= 1 /\ live h x /\ live h y /\ live h result /\ 
      eq_or_disjoint x result /\ eq_or_disjoint y result)
    (ensures fun h0 cc5 h1 -> modifies (loc result) h0 h1 /\ uint_v cc5 <= 1 /\
      as_nat6 h1 result + v cc5 * pow2 (6 * 64) == as_nat6 h0 x + as_nat6 h0 y + v c)

let add6_with_carry c x y result = 
  let cc2 = add6_with_carry0 c x y result in 
  let cc5 = add6_1 x y result cc2 in 
  cc5
  

val lemmaFelem6asFelem12: x: felem12_buffer -> h: mem -> Lemma
    (
      let x0 = gsub x (size 0) (size 6) in 
      let x1 = gsub x (size 6) (size 6) in 
      as_nat6 h x0 + as_nat6 h x1 * pow2 (6 * 64) == as_nat12 h x
    )

let lemmaFelem6asFelem12 x h = 
     assert_norm (pow2 (1 * 64) * pow2 (6 * 64) = pow2 (7 * 64));
    assert_norm (pow2 (2 * 64) * pow2 (6 * 64) = pow2 (8 * 64));
    assert_norm (pow2 (3 * 64) * pow2 (6 * 64) = pow2 (9 * 64));
    assert_norm (pow2 (4 * 64) * pow2 (6 * 64) = pow2 (10 * 64));
    assert_norm (pow2 (5 * 64) * pow2 (6 * 64) = pow2 (11 * 64));
    assert_norm (pow2 (6 * 64) * pow2 (6 * 64) = pow2 (12 * 64))


val add12: x: felem12_buffer -> y: felem12_buffer -> result: felem12_buffer -> Stack uint64
  (requires fun h -> live h x /\ live h y /\ live h result /\ eq_or_disjoint x result /\ eq_or_disjoint y result)
  (ensures (fun h0 c h1 -> modifies (loc result) h0 h1 /\ v c <= 1 /\
    as_nat12 h1 result + v c * pow2 (12 * 64) == as_nat12 h0 x + as_nat12 h0 y))

let add12 x y result = 
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 
  assert_norm (pow2 (6 * 64) * pow2 (6 * 64) = pow2 (12 * 64));

  let h0 = ST.get() in 

    let a0 = sub x (size 0) (size 6) in 
    let a1 = sub x (size 6) (size 6) in 


    let b0 = sub y (size 0) (size 6) in 
    let b1 = sub y (size 6) (size 6) in 

    let c0 = sub result (size 0) (size 6) in 
    let c1 = sub result (size 6) (size 6) in 

    let carry0 = add6 a0 b0 c0 in 
    let carry1 = add6_with_carry carry0 a1 b1 c1 in 

  let h1 = ST.get() in 
  
    assert_by_tactic (pow2 (6 * 64) * (as_nat6 h1 c1 + v carry1 * pow2 (6 * 64)) == as_nat6 h1 c1 * pow2 (6 * 64) + v carry1 * pow2 (6 * 64) * pow2 (6 * 64)) canon;
    assert_by_tactic (pow2 (6 * 64) * (as_nat6 h0 a1 + as_nat6 h0 b1 + v carry0) = as_nat6 h0 a1 * pow2 (6 * 64) + as_nat6 h0 b1 * pow2 (6 * 64) +  v carry0 * pow2 (6 * 64)) canon;


    calc (==) {
      as_nat12 h1 result + v carry1 * pow2 (12 * 64);
      (==) {lemmaFelem6asFelem12 result h1}
      as_nat6 h1 c0 + as_nat6 h1 c1 * pow2 (6 * 64) + v carry1 * pow2 (12 * 64);
      (==) {assert((as_nat6 h1 c1) * pow2 (6 * 64) == (- v carry1 * pow2 (6 * 64)  + as_nat6 h0 a1 + as_nat6 h0 b1 + v carry0) * pow2 (6 * 64))}
      as_nat6 h1 c0 + (- v carry1 * pow2 (6 * 64)  + as_nat6 h0 a1 + as_nat6 h0 b1 + v carry0) * pow2 (6 * 64) + v carry1 * pow2 (12 * 64);
      (==) {}
      (as_nat6 h0 a0 + as_nat6 h0 a1 * pow2 (6 * 64)) + (as_nat6 h0 b0  + as_nat6 h0 b1 * pow2 (6 * 64));
      (==) {lemmaFelem6asFelem12 x h0}
      as_nat12 h0 x + (as_nat6 h0 b0  + as_nat6 h0 b1 * pow2 (6 * 64));
      (==) {lemmaFelem6asFelem12 y h0}
      as_nat12 h0 x + as_nat12 h0 y;};

    carry1


val mul64: x: uint64 -> y: uint64 -> result: lbuffer uint64 (size 1) -> temp: lbuffer uint64 (size 1) ->
  Stack unit
    (requires fun h -> live h result /\ live h temp /\ disjoint result temp)
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc temp) h0 h1 /\ 
    (
      let h0 = Seq.index (as_seq h1 temp) 0 in 
      let result = Seq.index (as_seq h1 result) 0 in 
      uint_v result + uint_v h0 * pow2 64 = uint_v x * uint_v y     
      )
    )

let mul64 x y result temp = 
  let res = mul64_wide x y in 
  let l0, h0 = to_u64 res, to_u64 (res >>. 64ul) in 
  upd result (size 0) l0;
  upd temp (size 0) h0



val mult64_0il: x: ilbuffer uint64 (size 6) -> u: uint64 -> result:  lbuffer uint64 (size 1) -> temp: lbuffer uint64 (size 1) -> Stack unit 
  (requires fun h -> live h x /\ live h result /\ live h temp /\ disjoint result temp)
  (ensures fun h0 _ h1 -> 
    let result_ = Seq.index (as_seq h1 result) 0 in 
    let c = Seq.index (as_seq h1 temp) 0 in 
    let f0 = Seq.index (as_seq h0 x) 0 in 
    uint_v result_ + uint_v c * pow2 64 = uint_v f0 * uint_v u /\ modifies (loc result |+| loc temp) h0 h1)

let mult64_0il x u result temp = 
  let f0 = index x (size 0) in 
  mul64 f0 u result temp


val mult64_c: x: uint64 -> u: uint64 -> cin: uint64{uint_v cin <= 1} -> result: lbuffer uint64 (size 1) -> temp: lbuffer uint64 (size 1) -> Stack uint64 
  (requires fun h -> live h result /\ live h temp /\ disjoint result temp)
  (ensures fun h0 c2 h1 -> modifies (loc result |+| loc temp) h0 h1 /\ uint_v c2 <= 1 /\
    (
      let r = Seq.index (as_seq h1 result) 0 in 
      let h1 = Seq.index (as_seq h1 temp) 0 in 
      let h0 = Seq.index (as_seq h0 temp) 0 in 
      uint_v r + uint_v c2 * pow2 64 == uint_v x * uint_v u - uint_v h1 * pow2 64 + uint_v h0 + uint_v cin)
)

let mult64_c x u cin result temp = 
  let h = index temp (size 0) in 
  mul64 x u result temp;
  let l = index result (size 0) in     
  add_carry_u64 cin l h result


val lemma_mult: a: int -> b: int -> c: int -> d: int -> e: int -> f: nat ->  Lemma
   (requires (a = b + c + d + e))
   (ensures (a * f = b * f + c * f + d * f + e * f))

let lemma_mult a b c d e f = ()


val lemma_mult5: a: int -> b: int -> c: int -> d: int -> e: int -> f: int -> j: nat -> Lemma
   (requires (a = b + c + d + e + f))
   (ensures (a * j = b * j + c * j + d * j + e * j + f * j ))

let lemma_mult5 a b c d e f j = ()


val mul1_il0: f: ilbuffer uint64 (size 6) -> u: uint64 -> result: lbuffer uint64 (size 6) -> temp: lbuffer uint64 (size 1) -> Stack uint64
  (requires fun h -> live h result /\ live h f /\ live h temp /\  disjoint result temp)
  (ensures fun h0 c h1 -> modifies (loc result |+| loc temp) h0 h1  /\
    uint_v c <= 1 /\
    
      uint_v (Seq.index (as_seq h1 result) 0) + 
      uint_v (Seq.index (as_seq h1 result) 1) * pow2 64 +
      uint_v (Seq.index (as_seq h1 result) 2) * pow2 (2 * 64) + 
      uint_v (Seq.index (as_seq h1 result) 3) * pow2 (3 * 64) + 
      uint_v c * pow2 (4 * 64) + uint_v (Seq.index (as_seq h1 temp) 0) * pow2 (4 * 64) ==
      
      uint_v (Seq.index (as_seq h0 f) 0) * uint_v u + 
      uint_v (Seq.index (as_seq h0 f) 1) * uint_v u * pow2 64 + 
      uint_v (Seq.index (as_seq h0 f) 2) * uint_v u * pow2 (2 * 64) + 
      uint_v (Seq.index (as_seq h0 f) 3) * uint_v u * pow2 (3 * 64)
  )


let mul1_il0 f u result temp = 
  let h0 = ST.get() in 

  let f0 = index f (size 0) in 
  let f1 = index f (size 1) in 
  let f2 = index f (size 2) in 
  let f3 = index f (size 3) in 

  let o0 = sub result (size 0) (size 1) in 
  let o1 = sub result (size 1) (size 1) in 
  let o2 = sub result (size 2) (size 1) in 
  let o3 = sub result (size 3) (size 1) in 

  assert_norm (pow2 64 * pow2 64 = pow2 (2 * 64));
  assert_norm (pow2 64 * pow2 (2 * 64) = pow2 (3 * 64));
  assert_norm (pow2 64 * pow2 (3 * 64) = pow2 (4 * 64));

   mult64_0il f u o0 temp;
    let h1 = ST.get() in 
    
  let c1 = mult64_c f1 u (u64 0) o1 temp in 
    let h2 = ST.get() in 
     lemma_mult (uint_v f1 * uint_v u) (uint_v (Seq.index (as_seq h2 o1) 0)) (uint_v c1 * pow2 64) (uint_v (Seq.index (as_seq h2 temp) 0) * pow2 64) (- uint_v (Seq.index (as_seq h1 temp) 0)) (pow2 64); 
    
  let c2 = mult64_c f2 u c1 o2 temp in 
    let h3 = ST.get() in 
    lemma_mult5 (uint_v f2 * uint_v u) (uint_v (Seq.index (as_seq h3 o2) 0)) (uint_v c2 * pow2 64) (uint_v (Seq.index (as_seq h3 temp) 0) * pow2 64) (- uint_v (Seq.index (as_seq h2 temp) 0)) (- uint_v c1) (pow2 (2 * 64));

  let c3 = mult64_c f3 u c2 o3 temp in 
    let h4 = ST.get() in 
    lemma_mult5 (uint_v f3 * uint_v u) (uint_v (Seq.index (as_seq h4 o3) 0)) (uint_v c3 * pow2 64) (uint_v (Seq.index (as_seq h4 temp) 0) * pow2 64) (- uint_v (Seq.index (as_seq h3 temp) 0)) (- uint_v c2) (pow2 (3 * 64));

  c3
  



val mul1_il: f:  ilbuffer uint64 (size 6) -> u: uint64 -> result: lbuffer uint64 (size 6) -> Stack uint64
  (requires fun h -> live h result /\ live h f)
  (ensures fun h0 c h1 -> modifies (loc result) h0 h1 /\ 
    as_nat6_il h0 f * uint_v u = uint_v c * pow2 (6 * 64) + as_nat6 h1 result /\ 
    as_nat6_il h0 f * uint_v u < pow2 (7 * 64) /\
    uint_v c < pow2 64 - 1 
  )


let mul1_il f u result = 
  push_frame();

  let temp = create (size 1) (u64 0) in 

  let f4 = index f (size 4) in 
  let f5 = index f (size 5) in 
    

  let o4 = sub result (size 4) (size 1) in 
  let o5 = sub result (size 5) (size 1) in 
  
  let c3 = mul1_il0 f u result temp in 
  let h4 = ST.get() in

  let c4 = mult64_c f4 u c3 o4 temp in 
    let h5 = ST.get() in 
    assert(uint_v (Seq.index (as_seq h5 o4) 0) + uint_v c4 * pow2 64 + uint_v (Seq.index (as_seq h5 temp) 0) * pow2 64 - uint_v (Seq.index (as_seq h4 temp) 0) - uint_v c3 == uint_v f4 * uint_v u);

    lemma_mult5 (uint_v f4 * uint_v u) (uint_v (Seq.index (as_seq h5 o4) 0)) (uint_v c4 * pow2 64) (uint_v (Seq.index (as_seq h5 temp) 0) * pow2 64) (- uint_v (Seq.index (as_seq h4 temp) 0)) (- uint_v c3) (pow2 (4 * 64));

     assert(uint_v (Seq.index (as_seq h5 o4) 0) * pow2 (4 * 64) + uint_v c4 * pow2 64 * pow2 (4 * 64) + uint_v (Seq.index (as_seq h5 temp) 0) * pow2 64 * pow2 (4 * 64) - uint_v (Seq.index (as_seq h4 temp) 0) * pow2 (4 * 64) - uint_v c3 * pow2 (4 * 64) == uint_v f4 * uint_v u * pow2 (4 * 64));


  let c5 = mult64_c f5 u c4 o5 temp in 
      let h6 = ST.get() in 
     assert(uint_v (Seq.index (as_seq h6 o5) 0) + uint_v c5 * pow2 64 + uint_v (Seq.index (as_seq h6 temp) 0) * pow2 64 - uint_v (Seq.index (as_seq h5 temp) 0) - uint_v c4 == uint_v f5 * uint_v u);

    lemma_mult5 (uint_v f5 * uint_v u) (uint_v (Seq.index (as_seq h6 o5) 0)) (uint_v c5 * pow2 64) (uint_v (Seq.index (as_seq h6 temp) 0) * pow2 64) (- uint_v (Seq.index (as_seq h5 temp) 0)) (- uint_v c4) (pow2 (5 * 64));

     assert(uint_v (Seq.index (as_seq h6 o5) 0) * pow2 (5 * 64) + uint_v c5 * pow2 64 * pow2 (5 * 64) + uint_v (Seq.index (as_seq h6 temp) 0) * pow2 64 * pow2 (5 * 64) - uint_v (Seq.index (as_seq h5 temp) 0) * pow2 (5 * 64) - uint_v c4 * pow2 (5 * 64) == uint_v f5 * uint_v u * pow2 (5 * 64));


  let temp0 = index temp (size 0) in 


  pop_frame();  
  admit();
  c5 +! temp0


val shortened_mul: a: ilbuffer uint64 (size 6) -> b: uint64 -> result: felem12_buffer -> Stack unit
  (requires fun h -> live h a /\ live h result)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
    as_nat6_il h0 a * uint_v b = as_nat12 h1 result)


let shortened_mul a b result = 
  let result0 = sub result (size 0) (size 4) in 
  let result4 = sub result (size 4) (size 4) in 
  let c = mul1_il a b result0 in 
  upd result (size 6) c;
  upd result (size 7) (u64 0);
  upd result (size 8) (u64 0);
  upd result (size 9) (u64 0);
  upd result (size 10) (u64 0);
  upd result (size 11) (u64 0)
  



inline_for_extraction noextract
val mod64: a: felem12_buffer -> Stack uint64 
  (requires fun h -> live h a) 
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\  as_nat12 h1 a % pow2 64 = uint_v r)

let mod64 a = index a (size 0)


val shift12: t: felem12_buffer -> t1: felem12_buffer -> Stack unit 
  (requires fun h -> live h t /\ live h t1 /\ eq_or_disjoint t t1)
  (ensures fun h0 _ h1 -> modifies (loc t1) h0 h1 /\ as_nat12 h0 t / pow2 64 = as_nat12 h1 t1)

let shift12 t out = 
  let t1 = index t (size 1) in 
  let t2 = index t (size 2) in 
  let t3 = index t (size 3) in 
  let t4 = index t (size 4) in 
  let t5 = index t (size 5) in 
  let t6 = index t (size 6) in 
  let t7 = index t (size 7) in 
  let t8 = index t (size 8) in 
  let t9 = index t (size 9) in 
  let t10 = index t (size 10) in 
  let t11 = index t (size 11) in 

  upd out (size 0) t1;
  upd out (size 1) t2;
  upd out (size 2) t3;
  upd out (size 3) t4;
  upd out (size 4) t5;
  upd out (size 5) t6;
  upd out (size 6) t7;
  upd out (size 7) t8;  upd out (size 8) t9;
  upd out (size 9) t10;
  upd out (size 10) t11;
  upd out (size 11) (u64 0)
