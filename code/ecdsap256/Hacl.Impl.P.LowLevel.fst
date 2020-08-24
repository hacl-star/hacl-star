module Hacl.Impl.P.LowLevel

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.Definition
open Hacl.Lemmas.P256

open Spec.P256

open FStar.Math
open FStar.Math.Lemmas
open FStar.Mul

open FStar.Tactics
open FStar.Tactics.Canon

open Hacl.Impl.P256.LowLevel
open Hacl.Impl.P384.LowLevel

open Lib.IntTypes.Intrinsics


open Lib.Loops


#set-options "--fuel 0 --ifuel 0 --z3rlimit 200"

let uploadZeroImpl #c f =
  let h0 = ST.get() in 
  let len = getCoordinateLenU64 c in 
  let inv h (i: nat {i <= uint_v (getCoordinateLenU64 c)}) = live h f /\ modifies (loc f) h0 h /\
    (forall (j: nat {j < i}). 
      let elemUpdated = Lib.Sequence.index (as_seq h f) j in uint_v elemUpdated = 0) in 
  for 0ul len inv (fun i -> 
    upd f i (u64 0); 
    let h = ST.get() in 
    assert(
      forall (j: nat {j < uint_v i}). 
      let elemUpdated = Lib.Sequence.index (as_seq h f) j in uint_v elemUpdated = 0))


let uploadZeroPoint #c p =
  let len = getCoordinateLenU64 c in 
  
  let x = sub p (size 0) len in 
  let y = sub p len len in 
  let z = sub p (size 2 *! len) len in 
  
  uploadZeroImpl #c x;
  uploadZeroImpl #c y;
  uploadZeroImpl #c z


let cmovznz4 #c  cin x y r =
  let h0 = ST.get() in
  let mask = neq_mask cin (u64 0) in
  
  let len = getCoordinateLenU64 c in 
  let inv h (i: nat { i <= uint_v (getCoordinateLenU64 c)}) = 
    live h x /\ live h y /\ modifies (loc r) h0 h /\ 
    (
      forall (j: nat {j >= i && j < v (getCoordinateLenU64 c)}).
      let y_i = Lib.Sequence.index (as_seq h y) j in 
      let y_0 = Lib.Sequence.index (as_seq h0 y) j in 
      uint_v y_i == uint_v y_0
    ) /\
    
    (
      forall (j: nat {j < i}).
	let x_i = Lib.Sequence.index (as_seq h0 x) j in 
	let y_i = Lib.Sequence.index (as_seq h0 y) j in 
	let r_i = Lib.Sequence.index (as_seq h r) j in 
	if uint_v cin = 0 then 
	  uint_v r_i == uint_v x_i
	else
	  uint_v r_i == uint_v y_i
    ) in 
  for 0ul len inv (fun i -> 
    let h_ = ST.get() in 
    let x_i = index x i in 
    let y_i = index y i in 
    let r_i = logor (logand y_i mask) (logand x_i (lognot mask)) in 
    upd r i r_i;
    cmovznz4_lemma cin (Seq.index (as_seq h0 x) (v i)) (Seq.index (as_seq h0 y) (v i))
  )



let add_bn #c x y result =
  match c with
  |P256 -> add4 x y result
  |P384 -> add6 x y result

let add_long_bn #c x y result = 
  match c with 
  |P256 -> add8 x y result
  |P384 -> add12 x y result

let add_dep_prime #c x t result =
  match c with
  |P256 -> add_dep_prime_p256 x t result
  |P384 -> add_dep_prime_p384 x t result

let sub_bn #c x y result =
  match c with
  |P256 -> sub4 x y result
  |P384 -> sub6 x y result

let sub_bn_gl #c x y result =
  match c with
  |P256 -> sub4_il x y result
  |P384 -> sub6_il x y result

let short_mul_bn #c x y result = 
  match c with
  | P256 -> shortened_mul_p256 x y result
  | P384 -> shortened_mul_p384 x y result

let square_bn #c x result = 
  match c with 
  |P256 -> square_p256 x result
  |P384 -> square_p384 x result


let uploadOneImpl #c f =
  upd f (size 0) (u64 1);
  let h0 = ST.get() in 
  let len = getCoordinateLenU64 c in 
  let inv h (i: nat { i <= uint_v (getCoordinateLenU64 c)}) = live h f /\ modifies (loc f) h0 h /\
    v (Lib.Sequence.index (as_seq h f) 0) == 1 /\
    (forall (j: nat {j > 0 /\ j < i}). 
      let elemUpdated = Lib.Sequence.index (as_seq h f) j in uint_v elemUpdated = 0)
  in 
  for 1ul len inv (fun i -> 
    upd f i (u64 0);
    let h = ST.get() in 
        assert(
      forall (j: nat {j > 0 /\ j < uint_v i}). 
      let elemUpdated = Lib.Sequence.index (as_seq h f) j in uint_v elemUpdated = 0))


let toUint8 #c i o =
  match c with
  |P256 -> Lib.ByteBuffer.uints_to_bytes_be (getCoordinateLenU64 P256) o i
  |P384 -> Lib.ByteBuffer.uints_to_bytes_be (getCoordinateLenU64 P384) o i


open Lib.ByteBuffer

let changeEndian #c b =
  let h0 = ST.get() in 
  let len = getCoordinateLenU64 c in 
  let lenByTwo = shift_right len 1ul in 

  [@inline_let]
  let spec h0 = Hacl.Spec.P256.Definition.changeEndianStep #c  in 

   [@inline_let]
  let acc (h: mem) : GTot (felem_seq c) = as_seq h b in 
  Lib.LoopCombinators.eq_repeati0 256 (spec h0) (acc h0);

   [@inline_let]
  let inv h (i: nat { i <= uint_v lenByTwo}) = live h b /\ modifies (loc b) h0 h /\
    (forall (j: nat {j < i}). 
      let leftStart = Lib.Sequence.index (as_seq h0 b) j in 
      let rightIndex = v len - 1 - j in 
      let rightStart = Lib.Sequence.index (as_seq h0 b) rightIndex in 

      let leftH = Lib.Sequence.index (as_seq h b) j in 
      let rightH = Lib.Sequence.index (as_seq h b) rightIndex in 

      uint_v leftStart == uint_v rightH /\
      uint_v rightStart == uint_v leftH) /\
    (forall (j: nat {j >= i && j < v lenByTwo}).
      Lib.Sequence.index (as_seq h0 b) j == Lib.Sequence.index (as_seq h b) j) /\
    (forall (j: nat {j >= v lenByTwo &&  j <= v len - 1 - i}).
      Lib.Sequence.index (as_seq h0 b) j == Lib.Sequence.index (as_seq h b) j) in 
  for 0ul lenByTwo inv (fun i -> 
    let h_0 = ST.get() in 
    
    let left = index b i in 
    let rightIndex = len -. 1ul -. i in 
    let right = index b rightIndex in 
    upd b i right;
    upd b rightIndex left
    
    );
    let h1 = ST.get() in 
    assert(
      forall (j: nat {j < v (shift_right len 1ul)}). 
      
      let leftStart = Lib.Sequence.index (as_seq h0 b) j in 
      let rightIndex = v len - 1 - j in 
      let rightStart = Lib.Sequence.index (as_seq h0 b) rightIndex in 

      let leftH = Lib.Sequence.index (as_seq h1 b) j in 
      let rightH = Lib.Sequence.index (as_seq h1 b) rightIndex in 

      uint_v leftStart == uint_v rightH /\
      uint_v rightStart == uint_v leftH);
      
  
    admit()
  




let toUint64ChangeEndian #c i o =
  Lib.ByteBuffer.uints_from_bytes_be o i;
  changeEndian o


val reduction_prime_2prime_with_carry_cin: #c: curve ->
  cin: uint64 -> x: felem c -> result: felem c ->
  Stack unit
    (requires fun h -> live h x /\ live h result /\ eq_or_disjoint x result /\
      (as_nat c h x + uint_v cin * getPower2 c) < 2 * getPrime c)
    (ensures fun h0 _ h1 ->
      modifies (loc result) h0 h1 /\
      as_nat c h1 result = (as_nat c h0 x + uint_v cin * getPower2 c) % getPrime c
      
      )


#set-options " --z3rlimit 400"

val lemma_test: 
  c: curve ->
  cin: nat {cin <= 1} ->
  x: nat {x + cin * getPower2 c < 2 * getPrime c /\ x < getPower2 c} -> 
  carry0 : nat {carry0 <= 1 /\ (if carry0 = 0 then x >= getPrime c else x < getPrime c)} -> 
  result: nat {if cin < carry0 then result = x else result = x - getPrime c + carry0 * getPower2 c}
  -> Lemma (result = (x + cin * getPower2 c) % getPrime c)

let lemma_test c cin x carry0 result = 
  let n = x + cin * getPower2 c in 
  assert(if cin < carry0 then result = x else result = x - getPrime c + carry0 * getPower2 c);
  assert(cin < carry0 <==> cin = 0 && carry0 = 1);
  assert(if (cin = 0 && carry0 = 1) then result = x else result = x - getPrime c + carry0 * getPower2 c);
  assert(if (cin = 0 && carry0 = 1) then result = x else result = x - getPrime c + carry0 * getPower2 c);
  assert(if ((cin = 1 && carry0 = 1) || (cin = 0 && carry0 = 0)) then 
    result = x - getPrime c + carry0 * getPower2 c else result = x);

  assert(if cin = 0 && carry0 = 0 then
    begin
      small_modulo_lemma_1 result (getPrime c);
      result = n % getPrime c end else True);


  assert(if cin = 1 && carry0 = 1 then 
    begin 
      modulo_addition_lemma result (getPrime c) 1; 
      result = n % getPrime c end 
   else True); 

    assert (if (cin = 0 && carry0 = 1) then begin
      small_modulo_lemma_1 result(getPrime c); 
      result = n % getPrime c end else True)
  

val lemma_cin_1: #c: curve -> x: nat -> cin : nat {x + cin * getPower2 c < 2 * getPrime c} -> 
  Lemma (cin <= 1)


let lemma_cin_1 #c x cin = 
  assert_norm(getPower2 P256 < 2 * getPrime P256);
  assert_norm(getPower2 P384 < 2 * getPrime P384)



let reduction_prime_2prime_with_carry_cin #c cin x result =
  push_frame();

  let h0 = ST.get() in 

  let len = getCoordinateLenU64 c in

  let tempBuffer = create len (u64 0) in
  let tempBufferForSubborrow = create (size 1) (u64 0) in
 
  recall_contents (prime_buffer #c) (Lib.Sequence.of_list (prime_list c));
  let carry0 = sub_bn_gl x prime_buffer tempBuffer in
  let carry = sub_borrow_u64 carry0 cin (u64 0) tempBufferForSubborrow in
  cmovznz4 carry tempBuffer x result;
  pop_frame();
  
  let h2 = ST.get() in 

  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 384);

  lemma_cin_1 #c (as_nat c h0 x) (uint_v cin);
  lemma_test c (v cin) (as_nat c h0 x) (uint_v carry0) (as_nat c h2 result)


let reduction_prime_2prime_with_carry #c x result =
  push_frame();
    let h0 = ST.get() in
    let len = getCoordinateLenU64 c in
    let tempBuffer = create len (u64 0) in
    let tempBufferForSubborrow = create (size 1) (u64 0) in

    let cin = Lib.Buffer.index x len in
    let x_ = Lib.Buffer.sub x (size 0) len in

    recall_contents (prime_buffer #c) (Lib.Sequence.of_list (prime_list c));

    let c = sub_bn_gl x_ (prime_buffer #c) tempBuffer in
    let carry = sub_borrow_u64 c cin (u64 0) tempBufferForSubborrow in
    cmovznz4 carry tempBuffer x_ result;
    admit();
 pop_frame()


val lemma_reduction1: #c: curve -> a: nat {a < getPower2 c}
  -> r: nat{if a >= getPrime c then r = a - getPrime c else r = a} ->
  Lemma (r = a % getPrime c)

let lemma_reduction1 #c a r =
  if a >= getPrime c then begin
    assert_norm (getPower2 P256 - getPrime P256 < getPrime P256);
    assert_norm (getPower2 P384 - getPrime P384 < getPrime P384);
    small_modulo_lemma_1 r (getPrime c);
    lemma_mod_sub_distr a (getPrime c) (getPrime c) end
  else
    small_mod r (getPrime c)


let reduction_prime_2prime #c x result =
  push_frame();
  let len = getCoordinateLenU64 c in
  let tempBuffer = create len (u64 0) in
  recall_contents (prime_buffer #c) (Lib.Sequence.of_list (prime_list c));

    let h0 = ST.get() in
  let r = sub_bn_gl x (prime_buffer #c) tempBuffer in
  cmovznz4 r tempBuffer x result;
    let h1 = ST.get() in
    lemma_reduction1 #c (as_nat c h0 x) (as_nat c h1 result);
  pop_frame()


let felem_add #c arg1 arg2 out =
  let h0 = ST.get() in

  let t = add_bn arg1 arg2 out in
  reduction_prime_2prime_with_carry_cin t out out;

  additionInDomain #c (as_nat c h0 arg1) (as_nat c h0 arg2);
  inDomain_mod_is_not_mod #c (fromDomain_ #c (as_nat c h0 arg1) + fromDomain_ #c (as_nat c h0 arg2))


let felem_double #c arg1 out =
  let h0 = ST.get() in

  let t = add_bn arg1 arg1 out in
  reduction_prime_2prime_with_carry_cin t out out;

  additionInDomain #c (as_nat c h0 arg1) (as_nat c h0 arg1);
  inDomain_mod_is_not_mod #c (fromDomain_ #c (as_nat c h0 arg1) + fromDomain_ #c (as_nat c h0 arg1))


let felem_sub #c arg1 arg2 out =
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
    let h0 = ST.get() in
  let t = sub_bn arg1 arg2 out in
  let cc = add_dep_prime #c out t out in
  (*
  modulo_addition_lemma  (as_nat P256 h0 arg1 - as_nat P256  h0 arg2) prime256 1;
    let h2 = ST.get() in
      assert(
      if as_nat P256 h0 arg1 - as_nat P256 h0 arg2 >= 0 then
      begin
	modulo_lemma (as_nat P256 h0 arg1 - as_nat P256 h0 arg2) prime256;
	as_nat P256 h2 out == (as_nat P256 h0 arg1 - as_nat P256 h0 arg2) % prime256
  end
      else
          begin
      modulo_lemma (as_nat P256 h2 out) prime256;
            as_nat P256 h2 out == (as_nat P256 h0 arg1 - as_nat P256 h0 arg2) % prime256
    end);

    substractionInDomain #P256 (felem_seq_as_nat P256 (as_seq h0 arg1)) (felem_seq_as_nat P256 (as_seq h0 arg2));
    inDomain_mod_is_not_mod #P256 (fromDomain_ #P256 (felem_seq_as_nat P256 (as_seq  h0 arg1)) - fromDomain_ #P256 (felem_seq_as_nat P256 (as_seq h0 arg2))) *)
    admit();
    cc


let mul #c f r out =
  match c with
  |P256 -> mul_p256 f r out
  |P384 -> mul_p384 f r out


let eq0_u64 a =
  eq_mask_lemma a (u64 0);
  eq_mask a (u64 0)


let eq1_u64 a =
  neq_mask_lemma a (u64 0);
  neq_mask a (u64 0)



let isZero_uint64_CT #c f =
  let len = getCoordinateLenU64 c in 
  let inv h (i: nat { i <= uint_v (getCoordinateLenU64 c)}) = True in
  push_frame();
    let tmp = create (size 1) (u64 18446744073709551615) in

   for 0ul len inv (fun i -> 
    let a_i = index f i in 
    let r_i = eq_mask a_i (u64 0) in 
    upd tmp (size 0) (logand r_i (index tmp (size 0))));

  let r = index tmp (size 0) in 
  pop_frame();
  r

(*
  match c with
  |P256 ->
    let a0 = index f (size 0) in
    let a1 = index f (size 1) in
    let a2 = index f (size 2) in
    let a3 = index f (size 3) in

    let r0 = eq_mask a0 (u64 0) in
    let r1 = eq_mask a1 (u64 0) in
    let r2 = eq_mask a2 (u64 0) in
    let r3 = eq_mask a3 (u64 0) in

    let r01 = logand r0 r1 in
      logand_lemma r0 r1;
    let r23 = logand r2 r3 in
      logand_lemma r2 r3;
    let r = logand r01 r23 in
      logand_lemma r01 r23;
    r
  |P384 ->
    let a0 = index f (size 0) in
    let a1 = index f (size 1) in
    let a2 = index f (size 2) in
    let a3 = index f (size 3) in
    let a4 = index f (size 4) in
    let a5 = index f (size 5) in

    let r0 = eq_mask a0 (u64 0) in
    let r1 = eq_mask a1 (u64 0) in
    let r2 = eq_mask a2 (u64 0) in
    let r3 = eq_mask a3 (u64 0) in
    let r4 = eq_mask a4 (u64 0) in
    let r5 = eq_mask a5 (u64 0) in

    let r01 = logand r0 r1 in
      logand_lemma r0 r1;
    let r23 = logand r2 r3 in
      logand_lemma r2 r3;
    let r = logand r01 r23 in
      logand_lemma r01 r23;
    let r45 = logand r4 r5 in
    let r = logand r r45 in
    r
*)


let compare_felem #c a b =
  let len = getCoordinateLenU64 c in 
  let inv h (i: nat { i <= uint_v (getCoordinateLenU64 c)}) = True in
  push_frame();
    let tmp = create (size 1) (u64 0) in 
    upd tmp (size 0) (u64 18446744073709551615);
    
  for 0ul len inv (fun i -> 
    let a_i = index a i in 
    let b_i = index b i in 
    let r_i = eq_mask a_i b_i in 
    upd tmp (size 0) (logand r_i (index tmp (size 0))));

  let r = index tmp (size 0) in 
  pop_frame(); 
  r


(*
  |P256 ->
    let a_0 = index a (size 0) in
    let a_1 = index a (size 1) in
    let a_2 = index a (size 2) in
    let a_3 = index a (size 3) in

    let b_0 = index b (size 0) in
    let b_1 = index b (size 1) in
    let b_2 = index b (size 2) in
    let b_3 = index b (size 3) in

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
  lemma_equality (a_0, a_1, a_2, a_3) (b_0, b_1, b_2, b_3);
    r
  |P384 ->
      let a_0 = index a (size 0) in
      let a_1 = index a (size 1) in
      let a_2 = index a (size 2) in
      let a_3 = index a (size 3) in
      let a_4 = index a (size 4) in
      let a_5 = index a (size 5) in

      let b_0 = index b (size 0) in
      let b_1 = index b (size 1) in
      let b_2 = index b (size 2) in
      let b_3 = index b (size 3) in
      let b_4 = index b (size 4) in
      let b_5 = index b (size 5) in

      let r_0 = eq_mask a_0 b_0 in
      let r_1 = eq_mask a_1 b_1 in
      let r_2 = eq_mask a_2 b_2 in
      let r_3 = eq_mask a_3 b_3 in
      let r_4 = eq_mask a_4 b_4 in
      let r_5 = eq_mask a_5 b_5 in

      let r01 = logand r_0 r_1 in
      let r23 = logand r_2 r_3 in
      let r45 = logand r_4 r_5 in

      let r = logand(logand r01 r23) r45 in
      lemma_equality (a_0, a_1, a_2, a_3, a_4, a_5) (b_0, b_1, b_2, b_3, b_4, b_5);
      r
*)

let copy_conditional #c out x mask =
  let len = getCoordinateLenU64 c in 
  let inv h (i: nat { i <= uint_v (getCoordinateLenU64 c)}) = True in 
  for 0ul len inv (fun i -> 
    let out_i = index out i in 
    let x_i = index x i in 
    let r_i = logxor out_i (logand mask (logxor out_i x_i)) in 
    upd out i r_i)
  (*
  match c with
  |P256 ->
    let h0 = ST.get() in
    let out_0 = index out (size 0) in
    let out_1 = index out (size 1) in
    let out_2 = index out (size 2) in
    let out_3 = index out (size 3) in

    let x_0 = index x (size 0) in
    let x_1 = index x (size 1) in
    let x_2 = index x (size 2) in
    let x_3 = index x (size 3) in

    let r_0 = logxor out_0 (logand mask (logxor out_0 x_0)) in
    let r_1 = logxor out_1 (logand mask (logxor out_1 x_1)) in
    let r_2 = logxor out_2 (logand mask (logxor out_2 x_2)) in
    let r_3 = logxor out_3 (logand mask (logxor out_3 x_3)) in

    lemma_xor_copy_cond out_0 x_0 mask;
    lemma_xor_copy_cond out_1 x_1 mask;
    lemma_xor_copy_cond out_2 x_2 mask;
    lemma_xor_copy_cond out_3 x_3 mask;

    upd out (size 0) r_0;
    upd out (size 1) r_1;
    upd out (size 2) r_2;
    upd out (size 3) r_3;
      let h1 = ST.get() in

    lemma_eq_funct_ (as_seq h1 out) (as_seq h0 out);
    lemma_eq_funct_ (as_seq h1 out) (as_seq h0 x)
  |P384 ->
    let h0 = ST.get() in

    let out_0 = index out (size 0) in
    let out_1 = index out (size 1) in
    let out_2 = index out (size 2) in
    let out_3 = index out (size 3) in
    let out_4 = index out (size 4) in
    let out_5 = index out (size 5) in

    let x_0 = index x (size 0) in
    let x_1 = index x (size 1) in
    let x_2 = index x (size 2) in
    let x_3 = index x (size 3) in
    let x_4 = index x (size 4) in
    let x_5 = index x (size 5) in

    let r_0 = logxor out_0 (logand mask (logxor out_0 x_0)) in
    let r_1 = logxor out_1 (logand mask (logxor out_1 x_1)) in
    let r_2 = logxor out_2 (logand mask (logxor out_2 x_2)) in
    let r_3 = logxor out_3 (logand mask (logxor out_3 x_3)) in
    let r_4 = logxor out_4 (logand mask (logxor out_4 x_4)) in
    let r_5 = logxor out_5 (logand mask (logxor out_5 x_5)) in

    lemma_xor_copy_cond out_0 x_0 mask;
    lemma_xor_copy_cond out_1 x_1 mask;
    lemma_xor_copy_cond out_2 x_2 mask;
    lemma_xor_copy_cond out_3 x_3 mask;
    lemma_xor_copy_cond out_4 x_4 mask;
    lemma_xor_copy_cond out_5 x_5 mask;
 
    upd out (size 0) r_0;
    upd out (size 1) r_1;
    upd out (size 2) r_2;
    upd out (size 3) r_3;
    upd out (size 4) r_4;
    upd out (size 5) r_5;
      let h1 = ST.get() in

    lemma_eq_funct_ (as_seq h1 out) (as_seq h0 out);
    lemma_eq_funct_ (as_seq h1 out) (as_seq h0 x) *)


let shiftLeftWord #c i o =
  let len = getCoordinateLenU64 c in 
  let inv h (i: nat { i <= uint_v (getCoordinateLenU64 c)}) = True in 
  for 0ul len inv (fun j -> upd o j (u64 0));

  for len (size 2 *! len) inv (fun j -> upd o j i.(j -! len))

(*


  assert_norm(pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
  assert_norm(pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 384);
  match c with
  |P384 ->
    upd o (size 0) (u64 0);
    upd o (size 1) (u64 0);
    upd o (size 2) (u64 0);
    upd o (size 3) (u64 0);
    upd o (size 4) (u64 0);
    upd o (size 5) (u64 0);
    upd o (size 6) i.(size 0);
    upd o (size 7) i.(size 1);
    upd o (size 8) i.(size 2);
    upd o (size 9) i.(size 3);
    upd o (size 10) i.(size 4);
    upd o (size 11) i.(size 5)
  |P256 ->
    upd o (size 0) (u64 0);
    upd o (size 1) (u64 0);
    upd o (size 2) (u64 0);
    upd o (size 3) (u64 0);
    upd o (size 4) i.(size 0);
    upd o (size 5) i.(size 1);
    upd o (size 6) i.(size 2);
    upd o (size 7) i.(size 3) *)


let mod64 #c a =
  match c with 
  |P256 -> 
    let r = index a (size 0) in 
    (* let h1 = ST.get() in  *)
(*   assert(
  let open Lib.Sequence in
  let s = as_seq h1 a in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  let s4 = s.[4] in
  let s5 = s.[5] in
  let s6 = s.[6] in
  let s7 = s.[7] in
  wide_as_nat c h1 a ==  
  v s0 + v s1 * pow2 64 + v s2 * pow2 64 * pow2 64 +
  v s3 * pow2 64 * pow2 64 * pow2 64 +
  v s4 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
  v s5 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
  v s6 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
  v s7 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 /\
  wide_as_nat c h1 a % pow2 64 == v s0); *)
  r
   |P384 -> index a (size 0)


let shift1 #c t out = 
  let len = getCoordinateLenU64 c *! 2 in 
  let inv h (i: nat { i <= uint_v (getCoordinateLenU64 c)}) = True in 
  for 0ul (len -! 1) inv (fun i -> 
    let elem = index t (size 1 +! i) in 
    upd out i elem);
 upd out (len -! 1) (u64 0)
  
(*

  |P256 -> 
    let t1 = index t (size 1) in 
    let t2 = index t (size 2) in 
    let t3 = index t (size 3) in 
    let t4 = index t (size 4) in 
    let t5 = index t (size 5) in 
    let t6 = index t (size 6) in 
    let t7 = index t (size 7) in 

    upd out (size 0) t1;
    upd out (size 1) t2;
    upd out (size 2) t3;
    upd out (size 3) t4;
    upd out (size 4) t5;
    upd out (size 5) t6;
    upd out (size 6) t7;
    upd out (size 7) (u64 0)
*)


let upload_one_montg_form #c b =
  match c with 
  |P256 -> 
    upd b (size 0) (u64 1);
    upd b (size 1) (u64 18446744069414584320);
    upd b (size 2) (u64 18446744073709551615);
    upd b (size 3) (u64 4294967294)
  |P384 -> 
    upd b (size 0) (u64 18446744069414584321);
    upd b (size 1) (u64 4294967295);
    upd b (size 2) (u64 1);
    upd b (size 3) (u64 0);
    upd b (size 4) (u64 0);
    upd b (size 5) (u64 0)


let scalar_bit #buf_type s n =
  let h0 = ST.get () in
  mod_mask_lemma ((Lib.Sequence.index (as_seq h0 s) (v n / 8)) >>. (n %. 8ul)) 1ul;
  assert_norm (1 = pow2 1 - 1);
  assert (v (mod_mask #U8 #SEC 1ul) == v (u8 1));
  to_u64 ((s.(n /. 8ul) >>. (n %. 8ul)) &. u8 1)
