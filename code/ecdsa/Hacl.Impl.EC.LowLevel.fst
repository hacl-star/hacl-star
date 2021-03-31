module Hacl.Impl.EC.LowLevel

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.EC.Definition
open Hacl.Lemmas.P256

open Spec.ECC
open Spec.ECC.Curves

open FStar.Math
open FStar.Math.Lemmas
open FStar.Mul

open FStar.Tactics
open FStar.Tactics.Canon

open Hacl.Impl.P256.LowLevel
open Hacl.Impl.P384.LowLevel
open Hacl.Impl.EC.Masking

open Lib.IntTypes.Intrinsics
open Hacl.Impl.EC.LowLevel.Lemmas


open Lib.Loops

open Hacl.Bignum


#set-options "--fuel 0 --ifuel 0 --z3rlimit 200"

let uploadZeroImpl #c f =
  let h0 = ST.get() in 
  let len = getCoordinateLenU64 c in 
  let inv h (i: nat {i <= uint_v (getCoordinateLenU64 c)}) = live h f /\ modifies (loc f) h0 h /\ 
    lseq_as_nat_ (as_seq h f) i == 0 in 

  lseq_as_nat_last (as_seq h0 f);
  for 0ul len inv (fun i -> 
      let h0_ = ST.get() in 
    upd f i (u64 0); 
      let h_ = ST.get() in 

      lseq_as_nat_definiton (as_seq h_ f) (v i + 1);
      lemma_lseq_as_seq_as_forall (as_seq h0_ f) (as_seq h_ f) (v i))


let uploadOneImpl #c f =
  upd f (size 0) (u64 1);
  let h0 = ST.get() in 
  let len = getCoordinateLenU64 c in 
  let inv h (i: nat { i <= uint_v (getCoordinateLenU64 c)}) = live h f /\ modifies (loc f) h0 h /\
    lseq_as_nat_ (as_seq h f) i == 1 in  

  lseq_as_nat_definiton (as_seq h0 f) 1;
  lseq_as_nat_last (as_seq h0 f);
  
  for 1ul len inv (fun i -> 
      let h0_ = ST.get() in 
    upd f i (u64 0);
      let h_ = ST.get() in 

      lseq_as_nat_definiton (as_seq h_ f) (v i + 1);
      lemma_lseq_as_seq_as_forall (as_seq h0_ f) (as_seq h_ f) (v i))


let uploadZeroPoint #c p =
  let len = getCoordinateLenU64 c in 
  
  let x = sub p (size 0) len in 
  let y = sub p len len in 

  let z = sub p (size 2 *! len) len in 
  
  uploadZeroImpl #c x;
  uploadZeroImpl #c y;
  uploadZeroImpl #c z


let add_bn #c x y result =
  let len = getCoordinateLenU64 c in 
  match c with
  |P256 -> add4 x y result
  |P384 -> bn_add_eq_len len x y result
  |Default -> bn_add_eq_len len x y result


let add_long_bn #c x y result = 
  let len = getCoordinateLenU64 c *. 2ul in 
  match c with
  |P256 -> add8 x y result
  |P384 -> bn_add_eq_len len x y result
  |Default -> bn_add_eq_len len x y result


val _add_dep_prime: #c: curve -> x: felem c -> t: uint64{v t == 0 \/ v t == 1} 
  -> result: felem c ->
  Stack uint64
    (requires fun h -> live h x /\ live h result /\ eq_or_disjoint x result)
    (ensures fun h0 r h1 -> modifies (loc result) h0 h1 /\ (
      if uint_v t = 1 then 
        as_nat c h1 result + uint_v r * getPower2 c == as_nat c h0 x + getPrime c
      else
       as_nat c h1 result  == as_nat c h0 x))  


let _add_dep_prime #c x t result = 
  push_frame();
    let len = getCoordinateLenU64 c in 
    let b = create len (u64 0) in 
  let carry = add_bn (const_to_ilbuffer (prime_buffer #c)) x b in 

  let mask = (u64 0) -. t in 
  copy_conditional #c result b mask;
  admit();
  pop_frame();
  carry


let add_dep_prime #c x t result =
  match c with
  |P256 -> _add_dep_prime x t result
  |P384 -> add_dep_prime_p384 x t result
  |Default -> _add_dep_prime x t result


let sub_bn #c x y result =
  let len = getCoordinateLenU64 c in 
  match c with
  |P256 -> sub4 x y result
  |P384 -> bn_sub_eq_len len x y result
  |Default -> bn_sub_eq_len len x y result
  

let sub_bn_gl #c x y result =
  let y_ = const_to_ilbuffer y in 
  match c with
  |P256 -> sub4_il x y result
  |P384 -> sub_bn x y_ result
  |Default ->  sub_bn x y_ result


val _shortened_mul: #c: curve -> a: glbuffer uint64 (getCoordinateLenU64 c) -> b: uint64 -> result: widefelem c -> Stack unit
  (requires fun h -> live h a /\ live h result /\ wide_as_nat c h result = 0)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1(* /\ 
    as_nat_il c h0 a * uint_v b = wide_as_nat P384 h1 result /\ 
    wide_as_nat P384 h1 result < pow2 384 * pow2 64 *) )


let _shortened_mul #c a b result = 
  push_frame();
    let len = getCoordinateLenU64 c in 
    let bBuffer = create (size 1) b in 
    let a_ = const_to_ilbuffer a in (
    match c with 
      |P256 ->   
	bn_mul len a_ (size 1) bBuffer result
      |P384 -> 
	bn_mul len a_ (size 1) bBuffer result
      |Default -> 
	bn_mul len a_ (size 1) bBuffer result ); 
  pop_frame()


(* I expect that I use only with prime buffer, so this function will be deleted *)
let short_mul_bn #c x y result = 
  match c with
  | P256 -> shortened_mul_p256 x y result
  | P384 -> _shortened_mul x y result
  | Default -> _shortened_mul x y result


let short_mul_prime #c b result = 
  match c with
  | P256 -> shortened_mul_prime256 b result
  | P384 -> let primeBuffer = prime_buffer #c in short_mul_bn primeBuffer b result
  | Default -> let primeBuffer = prime_buffer #c in short_mul_bn primeBuffer b result
  

let square_bn #c x result = 
  let len = getCoordinateLenU64 c in 
  match c with 
  |P256 -> square_p256 x result
  |P384 -> Hacl.Bignum.bn_sqr len x result
  |Default -> Hacl.Bignum.bn_sqr len x result



val reduction_prime_2prime_with_carry_cin: #c: curve ->
  cin: uint64 -> x: felem c -> result: felem c ->
  Stack unit
  (requires fun h -> live h x /\ live h result /\ eq_or_disjoint x result /\ (
    as_nat c h x + uint_v cin * getPower2 c) < 2 * getPrime c)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
    as_nat c h1 result = (as_nat c h0 x + uint_v cin * getPower2 c) % getPrime c
  )


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
  lemma_reduction_prime_2prime_with_carry_cin c (v cin) (as_nat c h0 x) (uint_v carry0) (as_nat c h2 result)


let reduction_prime_2prime_with_carry #c x result =
  let len = getCoordinateLenU64 c in
  
  let cin = Lib.Buffer.index x len in
  let x_ = Lib.Buffer.sub x (size 0) len in
  let x__ = Lib.Buffer.sub x len len in 

  let h0 = ST.get() in 
  lemma_less_2prime #c h0 x;
  reduction_prime_2prime_with_carry_cin cin x_ result


let reduction_prime_2prime #c x result =
  push_frame();
  let len = getCoordinateLenU64 c in
  let tempBuffer = create len (u64 0) in
  recall_contents (prime_buffer #c) (Lib.Sequence.of_list (prime_list c));

    let h0 = ST.get() in
  let r = sub_bn_gl x (prime_buffer #c) tempBuffer in
  cmovznz4 r tempBuffer x result;
    let h1 = ST.get() in
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 384);
  
  lemma_reduction1 #c (as_nat c h0 x) (as_nat c h1 result);
  pop_frame()



let felem_add #c arg1 arg2 out =
  let h0 = ST.get() in

  let t = add_bn arg1 arg2 out in
  reduction_prime_2prime_with_carry_cin t out out;

  additionInDomain #c #DH (as_nat c h0 arg1) (as_nat c h0 arg2);
  inDomain_mod_is_not_mod #c #DH (fromDomain #c (as_nat c h0 arg1) + fromDomain #c (as_nat c h0 arg2))


let felem_double #c arg1 out =
  let h0 = ST.get() in

  let t = add_bn arg1 arg1 out in
  reduction_prime_2prime_with_carry_cin t out out;

  additionInDomain #c #DH (as_nat c h0 arg1) (as_nat c h0 arg1);
  inDomain_mod_is_not_mod #c #DH (fromDomain #c (as_nat c h0 arg1) + fromDomain #c (as_nat c h0 arg1))



let felem_sub #c arg1 arg2 out =
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 384);
    let h0 = ST.get() in
  let t = sub_bn arg1 arg2 out in
  let cc = add_dep_prime #c out t out in 

  modulo_addition_lemma (as_nat c h0 arg1 - as_nat c h0 arg2) (getPrime c) 1;

  let h2 = ST.get() in
  assert(
    let prime = getPrime c in 
    if as_nat c h0 arg1 - as_nat c h0 arg2 >= 0 then
      begin
	modulo_lemma (as_nat c h0 arg1 - as_nat c h0 arg2) prime;
	as_nat c h2 out == (as_nat c h0 arg1 - as_nat c h0 arg2) % prime
      end
    else
      begin
	modulo_lemma (as_nat c h2 out) prime;
	as_nat c h2 out == (as_nat c h0 arg1 - as_nat c h0 arg2) % prime
      end);

  substractionInDomain #c #DH (as_nat c h0 arg1) (as_nat c h0 arg2); 
  inDomain_mod_is_not_mod #c #DH (fromDomain #c (as_nat c h0 arg1) - fromDomain #c (as_nat c h0 arg2))


let mul #c f r out =
  let len = getCoordinateLenU64 c in 
  match c with
  |P256 -> mul_p256 f r out
  |P384 -> bn_mul len f len r out
  |Default -> bn_mul len f len r out



let isZero_uint64_CT #c f =
  push_frame();
  let h0 = ST.get() in 
  let tmp = create (size 1) (u64 18446744073709551615) in
  
  let len = getCoordinateLenU64 c in 
  let inv h (i: nat { i <= uint_v len}) = 
    live h f /\ live h tmp /\ modifies (loc tmp) h0 h /\ (
      let tmp = uint_v (Lib.Sequence.index (as_seq h tmp) 0) in (
      forall (j: nat {j < i}). v (Lib.Sequence.index (as_seq h0 f) j) == 0) <==>
      tmp == ones_v U64) 
    /\ (
      let tmp = uint_v (Lib.Sequence.index (as_seq h tmp) 0) in 
      ~ (forall (j: nat {j < i}). v (Lib.Sequence.index (as_seq h0 f) j) == 0) <==>
      tmp == 0
    ) in
  for 0ul len inv (fun i -> 
    let h0 = ST.get() in 
    assert(let tmp = uint_v (Lib.Sequence.index (as_seq h0 tmp) 0) in tmp == (ones_v U64) <==> 
      (forall (j: nat {j < (v i)}). v (Lib.Sequence.index (as_seq h0 f) j) == 0));

    let a_i = index f i in 
    let r_i = eq_mask a_i (u64 0) in 
    let tmp0 = index tmp (size 0) in 
    assert(if v a_i = 0 then v r_i == ones_v U64 else v r_i == 0);
    upd tmp (size 0) (logand r_i tmp0);
    logand_lemma r_i tmp0;

    let h1 = ST.get() in 
    let tmp1 = index tmp (size 0) in 
    assert(let tmp = uint_v (Lib.Sequence.index (as_seq h1 tmp) 0) in 
      tmp == (ones_v U64) <==> (forall (j: nat {j < (v i + 1)}). v (Lib.Sequence.index (as_seq h0 f) j) == 0)));

  let r = index tmp (size 0) in 
  
  assert(as_nat c h0 f = 0 <==> uint_v r == pow2 64 - 1);

  pop_frame();
  r



let compare_felem #c a b =
  push_frame();
  let h0 = ST.get() in 
  let tmp = create (size 1) (u64 0) in 
  upd tmp (size 0) (u64 18446744073709551615);
    
  let len = getCoordinateLenU64 c in 
  
  let inv h (i: nat { i <= uint_v len}) = live h a /\ live h b /\ live h tmp /\  modifies (loc tmp) h0 h /\ (
    let tmp = v (Lib.Sequence.index (as_seq h tmp) 0) in (
    forall (j: nat {j < i}). v (Lib.Sequence.index (as_seq h0 a) j) == 
      v (Lib.Sequence.index (as_seq h0 b) j)) <==> tmp == ones_v U64) /\ (
    let tmp = v (Lib.Sequence.index (as_seq h tmp) 0) in ( 
      ~ (forall (j: nat {j < i}).
	v (Lib.Sequence.index (as_seq h0 a) j) == v (Lib.Sequence.index (as_seq h0 b) j)) <==> tmp == 0)) in    
  for 0ul len inv (fun i -> 
    let h0 = ST.get() in 
    assert(let tmp = v (Lib.Sequence.index (as_seq h0 tmp) 0) in 
    tmp == ones_v U64 <==> (forall (j: nat {j < v i}). 
      v (Lib.Sequence.index (as_seq h0 a) j) == v (Lib.Sequence.index (as_seq h0 b) j)));
    
    let a_i = index a i in 
    let b_i = index b i in 
    let r_i = eq_mask a_i b_i in 
    let tmp0 = index tmp (size 0) in 

    logand_lemma r_i tmp0;
    upd tmp (size 0) (logand r_i tmp0);
    
    let h1 = ST.get() in 

    assert(let tmp = v (Lib.Sequence.index (as_seq h1 tmp) 0) in 
      tmp == ones_v U64 <==> (forall (j: nat {j < v i + 1}). 
	v (Lib.Sequence.index (as_seq h0 a) j) == v (Lib.Sequence.index (as_seq h0 b) j)))
    );

  let r = index tmp (size 0) in 

  lemma_felem_as_forall #c a b h0;
  assert(as_nat c h0 a == as_nat c h0 b <==> v r == ones_v U64);

  pop_frame(); 
  r


let shiftLeftWord #c i o =
  let len = getCoordinateLenU64 c in 
  let inv h (i: nat { i <= uint_v (getCoordinateLenU64 c)}) = True in 
  
  for len (size 2 *! len) inv (fun j -> 
    let i_i = index i (j -. len) in 
    upd o j i_i
    );

  for 0ul len inv (fun j -> upd o j (u64 0))
  

let mod64 #c a =
  let h0 = ST.get() in 
  lemma_wide_felem c h0 a;
  index a (size 0)



#push-options "--fuel 2"

let shift1_with_carry #c t out carry = 
  let h0 = ST.get() in 
  let len = getCoordinateLenU64 c *! 2ul -! 1ul in 
  let inv h (i: nat { i <= uint_v len}) = 
    live h t /\ live h out /\ modifies (loc out) h0 h /\  (
    lseq_as_nat_ #(v len + 1) (as_seq h0 t) (i + 1) / pow2 64 == lseq_as_nat_ #(v len + 1) (as_seq h out) i) 
  in 

  lseq_as_nat_first (as_seq h0 t);
  lseq_as_nat_last #(v len + 1) (as_seq h0 out);

  for 0ul len inv 
  (fun i -> 

    let h0_ = ST.get() in 
    let elem = index t (size 1 +! i) in 
    upd out i elem;
    let h1_ = ST.get() in 

    lemma_lseq_as_seq_as_forall (as_seq h0_ out) (as_seq h1_ out) (v i);

    lseq_as_nat_definiton #(v len + 1) (as_seq h1_ out) (v i + 1);
    lseq_as_nat_definiton #(v len + 1) (as_seq h1_ t) (v i + 2);

    pow2_plus (64 * (v i)) 64;
    
    let open FStar.Tactics in 
    let open FStar.Tactics.Canon in 

    assert_by_tactic (pow2 64 * pow2 (64 * (v i)) * v (Lib.Sequence.index (as_seq h1_ t) (v i + 1)) == 
    pow2 (64 * v i) * v (Lib.Sequence.index (as_seq h1_ t) (v i + 1)) * pow2 64) canon;
    
    lemma_div_plus (lseq_as_nat_ (as_seq h1_ t) (v i + 1)) (pow2 (64 * v i) * v (Lib.Sequence.index (as_seq h1_ t) (v i + 1)))
  (pow2 64));


  let h2 = ST.get() in 
  upd out len carry;  

  let h3 = ST.get() in 
  lemma_lseq_as_seq_as_forall (as_seq h2 out) (as_seq h3 out) (v len - 1);
  lseq_as_nat_definiton (as_seq h3 out) (v len + 1);
  pow2_plus (getPower c * 2 - 64) 64

#pop-options


let upload_one_montg_form #c b =
  match c with 
  |P256 -> 
    upd b (size 0) (u64 1);
    upd b (size 1) (u64 18446744069414584320);
    upd b (size 2) (u64 18446744073709551615);
    upd b (size 3) (u64 4294967294);
    lemmaToDomain #P256 #DH 1;
    assert_norm(1 + 18446744069414584320 * pow2 64 + 18446744073709551615 * pow2 64 * pow2 64 + 4294967294 * pow2 64 * pow2 64 * pow2 64 == pow2 (getPower P256) % getPrime P256)
  |P384 -> 
    upd b (size 0) (u64 18446744069414584321);
    upd b (size 1) (u64 4294967295);
    upd b (size 2) (u64 1);
    upd b (size 3) (u64 0);
    upd b (size 4) (u64 0);
    upd b (size 5) (u64 0);
    lemmaToDomain #P384 #DH 1;
    assert_norm(18446744069414584321 + 4294967295 * pow2 64 + 1 * pow2 64 * pow2 64 == pow2 (getPower P384) % getPrime P384)
  |Default -> 
    reduction_prime_2prime_with_carry_cin #c (u64 1) b b


let scalar_bit #c #buf_type s n =
  let h0 = ST.get () in
  mod_mask_lemma ((Lib.Sequence.index (as_seq h0 s) (v n / 8)) >>. (n %. 8ul)) 1ul;
  assert_norm (1 = pow2 1 - 1); 
  assert (v (mod_mask #U8 #SEC 1ul) == v (u8 1));
  to_u64 ((s.(n /. 8ul) >>. (n %. 8ul)) &. u8 1)


let mul_atomic x y result temp = 
  let res = mul64_wide x y in 
  let l0, h0 = to_u64 res, to_u64 (res >>. 64ul) in 
  upd result (size 0) l0;
  upd temp (size 0) h0
