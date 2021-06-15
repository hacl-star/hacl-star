module Hacl.Impl.EC.LowLevel

open Hacl.Bignum

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.EC.Definition
(* open Hacl.EC.Lemmas *)

open Spec.ECC
open Spec.ECC.Curves

open FStar.Math
open FStar.Math.Lemmas
open FStar.Mul

open FStar.Tactics
open FStar.Tactics.Canon
(* 
open Hacl.Impl.P256.LowLevel
open Hacl.Impl.P384.LowLevel
open Hacl.Impl.EC.Masking
 *)
open Lib.IntTypes.Intrinsics
(* open Hacl.Impl.EC.LowLevel.Lemmas *)


open Lib.Loops


#set-options "--fuel 0 --ifuel 0 --z3rlimit 200"
(* 
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
    let h0 = ST.get() in   
  Hacl.Spec.Bignum.bn_add_lemma (as_seq h0 x) (as_seq h0 y);
  let len = getCoordinateLenU64 c in 
  bn_add_eq_len len x y result


let add_long_bn #c x y result = 
    let h0 = ST.get() in 
  let len = getCoordinateLenU64 c *. 2ul in 
  Hacl.Spec.Bignum.bn_add_lemma (as_seq h0 x) (as_seq h0 y);
  bn_add_eq_len len x y result


inline_for_extraction noextract
val _add_dep_prime: #c: curve 
  -> x: felem c 
  -> p: felem c
  -> t: uint64{v t == 0 \/ v t == 1} 
  -> result: felem c ->
  Stack uint64
  (requires fun h -> live h x /\ live h result /\ live h p /\ 
    eq_or_disjoint x p /\ eq_or_disjoint p result /\ eq_or_disjoint x result)
  (ensures fun h0 r h1 -> modifies (loc result) h0 h1 /\ (
    if uint_v t = 1 then 
      as_nat c h1 result + v r * pow2 (getPower c) == as_nat c h0 x + as_nat c h0 p
    else
      as_nat c h1 result  == as_nat c h0 x))


let _add_dep_prime #c x p t result = 
  push_frame();
    let h0 = ST.get() in 
  let len = getCoordinateLenU64 c in 
  let b = create len (u64 0) in 
  let carry = add_bn p x b in 
  let mask = lognot ((u64 0) -. t) in 
    lognot_lemma (u64 0 -. t);
  cmovznz4 #c mask b x result;
  pop_frame();
  carry


assume val lemma_lseq_as_list: l: size_nat -> a: list uint64 {List.Tot.Base.length a == l} -> 
  Lemma (lseq_as_nat #l (Seq.seq_of_list a) == lst_as_nat a)


inline_for_extraction noextract
val add_dep_prime: #c: curve -> x: felem c -> t: uint64 {uint_v t == 0 \/ uint_v t == 1}
  -> result: felem c ->
  Stack uint64
  (requires fun h -> live h x /\ live h result /\ eq_or_disjoint x result)
  (ensures fun h0 r h1 -> modifies (loc result) h0 h1  /\ (
    if uint_v t = 1 then 
      as_nat c h1 result + v r * pow2 (getPower c) == as_nat c h0 x + getPrime c
    else
      as_nat c h1 result  == as_nat c h0 x))


let add_dep_prime #c x t result =
  match c with
  |P256 -> begin add_dep_prime_p256 x t result end 
  |P384 -> begin add_dep_prime_p384 x t result end
  |_ -> begin 
    push_frame();
    assume (getPrime c == prime256);
    let p = createL p256_prime_list in 
      lemma_lseq_as_list (v (getCoordinateLenU64 c)) (p256_prime_list);
    let r = _add_dep_prime x p t result in 
      pop_frame(); r end


let sub_bn #c x y result =
  let h0 = ST.get() in 
  let len = getCoordinateLenU64 c in 
  Hacl.Spec.Bignum.bn_sub_lemma (as_seq h0 x) (as_seq h0 y);
  bn_sub_eq_len len x y result
  

let sub_bn_order #c x result =
  let h0 = ST.get() in 
  match c with 
  |P256 -> push_frame();
    let p = createL p256_order_list in 
      lemma_lseq_as_list (v (getCoordinateLenU64 c)) (p256_order_list);
    let r = sub_bn x p result in 
      let h1 = ST.get() in 
    lseq_upperbound (as_seq h0 x);
    lseq_upperbound (as_seq h1 result);
      pop_frame(); r
  |P384 -> push_frame();
    let p = createL p384_order_list in 
      lemma_lseq_as_list (v (getCoordinateLenU64 c)) (p384_order_list);
    let r = sub_bn x p result in 
      let h1 = ST.get() in 
    lseq_upperbound (as_seq h0 x);
    lseq_upperbound (as_seq h1 result);
      pop_frame(); r
  |_ -> admit(); u64 0


let sub_bn_prime #c x result =
  let h0 = ST.get() in 
  match c with 
  |P256 -> push_frame();
    let p = createL p256_prime_list in 
      lemma_lseq_as_list (v (getCoordinateLenU64 c)) (p256_prime_list);
    let r = sub_bn x p result in 
      let h1 = ST.get() in 
    lseq_upperbound (as_seq h0 x);
    lseq_upperbound (as_seq h1 result);
      pop_frame(); r
  |P384 -> push_frame();
    let p = createL p384_prime_list in 
      lemma_lseq_as_list (v (getCoordinateLenU64 c)) (p384_prime_list);
    let r = sub_bn x p result in 
      let h1 = ST.get() in 
    lseq_upperbound (as_seq h0 x);
    lseq_upperbound (as_seq h1 result);
      pop_frame(); r
  |_ -> admit(); u64 0


val lemma_zero_lseq: #l0: size_nat -> #l1: size_nat -> a: Lib.Sequence.lseq uint64 l0 -> b: Lib.Sequence.lseq uint64 l1 
  ->  c: pos -> 
  Lemma ((lseq_as_nat a + c * lseq_as_nat b)  == 0 ==> lseq_as_nat b == 0)

let lemma_zero_lseq a b c = ()


#set-options "--fuel 0 --ifuel 0 --z3rlimit 300"

inline_for_extraction noextract
val _shortened_mul: #c: curve -> a: felem c -> b: uint64 -> result: widefelem c -> Stack unit
  (requires fun h -> live h a /\ live h result /\ eq_or_disjoint a result /\ wide_as_nat c h result = 0)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat c h0 a * uint_v b = wide_as_nat c h1 result /\ 
    wide_as_nat c h1 result < pow2 (getPower c) * pow2 64)

let _shortened_mul #c a b result = 
  push_frame();
    let len = getCoordinateLenU64 c in 
    let bBuffer = create (size 1) b in 
    let partResult = sub result (size 0) (len +! size 1) in 
    let partClean = sub result (len +! size 1) (len -! size 1) in 
        let h0 = ST.get() in 
    bn_mul len (size 1) a bBuffer partResult; 
    Hacl.Spec.Bignum.bn_mul_lemma (as_seq h0 a) (as_seq h0 bBuffer);
        let h1 = ST.get() in 
	  admit();
    lseq_as_nat_first (as_seq h0 bBuffer);
    lseq_upperbound (as_seq h0 a);
    
    lemma_mult_le_right (v b) (lseq_as_nat (as_seq h0 a)) (pow2 (getPower c) - 1);
    lemma_test (as_seq h0 result) (v len + 1);

    lemma_zero_lseq (as_seq h0 partResult) (as_seq h0 partClean) (pow2 (64 * (v len - 1)));
    lemma_test (as_seq h1 result) (v len + 1);
    
    assert(wide_as_nat c h1 result == lseq_as_nat (as_seq h0 a) * v b);
    assert(wide_as_nat c h1 result < pow2 (getPower c) * pow2 64);

  pop_frame()

let short_mul_prime #c b result = 
  match c with
  | P256 -> shortened_mul_prime256 b result
  | P384 -> 
    push_frame();
    let p = createL p384_prime_list in 
    lemma_lseq_as_list (v (getCoordinateLenU64 c)) (p384_prime_list);
    _shortened_mul p b result;
    pop_frame()
  | _ -> admit();
    push_frame();
    let p = createL p256_prime_list in 
    lemma_lseq_as_list (v (getCoordinateLenU64 c)) (p256_prime_list);
    _shortened_mul p b result;
    pop_frame()


let short_mul_order #c b result = 
  match c with
  | P256 ->     
	 push_frame();
    let p = createL p256_order_list in 
    lemma_lseq_as_list (v (getCoordinateLenU64 c)) (p256_order_list);
    _shortened_mul p b result;
      pop_frame()
  | P384 -> 
	 push_frame();
    let p = createL p384_order_list in 
    lemma_lseq_as_list (v (getCoordinateLenU64 c)) (p384_order_list);
    _shortened_mul p b result;
      pop_frame()
  | _ -> admit();
      push_frame();
    let p = createL p256_order_list in 
    lemma_lseq_as_list (v (getCoordinateLenU64 c)) (p256_order_list);
    _shortened_mul p b result;
      pop_frame()


let square_bn #c x result = 
    let h0 = ST.get() in 
  let len = getCoordinateLenU64 c in 
  Hacl.Bignum.bn_sqr len x result;
  Hacl.Spec.Bignum.bn_sqr_lemma (as_seq h0 x)

inline_for_extraction noextract
let reduction_prime_2prime_with_carry_cin #c cin x result =
  push_frame();

  let h0 = ST.get() in 

  let len = getCoordinateLenU64 c in

  let tempBuffer = create len (u64 0) in
  let tempBufferForSubborrow = create (size 1) (u64 0) in
 
  let carry0 = sub_bn_prime x tempBuffer in
  let carry = sub_borrow_u64 carry0 cin (u64 0) tempBufferForSubborrow in
  cmovznz4 carry tempBuffer x result;
  pop_frame();
  
  let h2 = ST.get() in 
  lseq_upperbound #(v (getCoordinateLenU64 c)) (as_seq h0 x);
  lemma_reduction_prime_2prime_with_carry_cin c (v cin) (as_nat c h0 x) (uint_v carry0) (as_nat c h2 result)


inline_for_extraction noextract
let reduction_prime_2prime_with_carry #c x result =
  let len = getCoordinateLenU64 c in
  
  let cin = Lib.Buffer.index x len in
  let x_ = Lib.Buffer.sub x (size 0) len in
  let x__ = Lib.Buffer.sub x len len in 

  let h0 = ST.get() in 
  FStar.Math.Lemmas.pow2_plus 64 (v (getCoordinateLenU64 c) * 64);
  lseq_upperbound1 (as_seq h0 x) (v (getCoordinateLenU64 c) + 1) (2 * v (getCoordinateLenU64 c) - v (getCoordinateLenU64 c) - 1);
  lseq_as_nat_definiton (as_seq h0 x) (v (getCoordinateLenU64 c) + 1);

  lemma_lseq_as_seq_extension (as_seq h0 (gsub x (size 0) (getCoordinateLenU64 c))) (as_seq h0 x) (v (getCoordinateLenU64 c));
  reduction_prime_2prime_with_carry_cin cin x_ result


let reduction_prime_2prime #c x result =
  push_frame();
  let len = getCoordinateLenU64 c in
  let tempBuffer = create len (u64 0) in
  let h0 = ST.get() in
  let r = sub_bn_prime x tempBuffer in
  cmovznz4 r tempBuffer x result;
  lseq_upperbound #(v (getCoordinateLenU64 c)) (as_seq h0 x);
  pop_frame()

(** Field Addition **)
inline_for_extraction
val felem_add_: #c: curve -> a: felem c -> b: felem c -> out: felem c ->
  Stack unit
    (requires (fun h0 ->
      live h0 a /\ live h0 b /\ live h0 out /\ eq_or_disjoint a out /\ eq_or_disjoint b out /\ eq_or_disjoint a b /\
      as_nat c h0 a < getPrime c /\ as_nat c h0 b < getPrime c))
    (ensures (fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      as_nat c h1 out == (as_nat c h0 a + as_nat c h0 b) % getPrime c /\
      as_nat c h1 out == toDomain #c ((fromDomain #c (as_nat c h0 a) + fromDomain #c (as_nat c h0 b)) % getPrime c)))

let felem_add_ #c arg1 arg2 out =
  let h0 = ST.get() in
  let t = add_bn arg1 arg2 out in
  reduction_prime_2prime_with_carry_cin t out out;
  additionInDomain #c #DH (as_nat c h0 arg1) (as_nat c h0 arg2);
  inDomain_mod_is_not_mod #c #DH (fromDomain #c (as_nat c h0 arg1) + fromDomain #c (as_nat c h0 arg2))

[@CInline]
val felem_add_p256: a: felem P256 -> b: felem P256 -> out: felem P256 ->
  Stack unit
    (requires (fun h0 ->
      live h0 a /\ live h0 b /\ live h0 out /\ eq_or_disjoint a out /\ eq_or_disjoint b out /\ eq_or_disjoint a b /\
      as_nat P256 h0 a < getPrime P256 /\ as_nat P256 h0 b < getPrime P256))
    (ensures (fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      as_nat P256 h1 out == (as_nat P256 h0 a + as_nat P256 h0 b) % getPrime P256 /\
      as_nat P256 h1 out == toDomain #P256 ((fromDomain #P256 (as_nat P256 h0 a) + fromDomain #P256 (as_nat P256 h0 b)) % getPrime P256)))


let felem_add_p256 a b out = felem_add_ #P256 a b out

[@CInline]
val felem_add_p384: a: felem P384 -> b: felem P384 -> out: felem P384 ->
  Stack unit
    (requires (fun h0 ->
      live h0 a /\ live h0 b /\ live h0 out /\ eq_or_disjoint a out /\ eq_or_disjoint b out /\ eq_or_disjoint a b /\
      as_nat P384 h0 a < getPrime P384 /\ as_nat P384 h0 b < getPrime P384))
    (ensures (fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      as_nat P384 h1 out == (as_nat P384 h0 a + as_nat P384 h0 b) % getPrime P384 /\
      as_nat P384 h1 out == toDomain #P384 ((fromDomain #P384 (as_nat P384 h0 a) + fromDomain #P384 (as_nat P384 h0 b)) % getPrime P384)))


let felem_add_p384 a b out = felem_add_ #P384 a b out

[@CInline]
val felem_add_generic: a: felem Default -> b: felem Default -> out: felem Default ->
  Stack unit
    (requires (fun h0 ->
      live h0 a /\ live h0 b /\ live h0 out /\ eq_or_disjoint a out /\ eq_or_disjoint b out /\ eq_or_disjoint a b /\
      as_nat Default h0 a < getPrime Default /\ as_nat Default h0 b < getPrime Default))
    (ensures (fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      as_nat Default h1 out == (as_nat Default h0 a + as_nat Default h0 b) % getPrime Default /\
      as_nat Default h1 out == toDomain #Default ((fromDomain #Default (as_nat Default h0 a) + fromDomain #Default (as_nat Default h0 b)) % getPrime Default)))


let felem_add_generic a b out = felem_add_ #Default a b out


let felem_add #c a b out = 
   match c with
    | P256 -> felem_add_p256 a b out
    | P384 -> felem_add_p384 a b out
    | Default -> felem_add_generic a b out


inline_for_extraction noextract
val felem_double_: #c: curve -> a: felem c -> out: felem c ->
  Stack unit
    (requires (fun h0 ->
      live h0 a /\ live h0 out /\ eq_or_disjoint a out /\ as_nat c h0 a < getPrime c))
    (ensures (fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      as_nat c h1 out == (2 * as_nat c h0 a) % getPrime c /\
      as_nat c h1 out == toDomain #c (2 * fromDomain #c (as_nat c h0 a) % getPrime c)))

let felem_double_ #c arg1 out =
  let h0 = ST.get() in

  let t = add_bn arg1 arg1 out in
  reduction_prime_2prime_with_carry_cin t out out;

  additionInDomain #c #DH (as_nat c h0 arg1) (as_nat c h0 arg1);
  inDomain_mod_is_not_mod #c #DH (fromDomain #c (as_nat c h0 arg1) + fromDomain #c (as_nat c h0 arg1))

[@CInline]
val felem_double_p256: a: felem P256 -> out: felem P256 ->
  Stack unit
    (requires (fun h0 ->
      live h0 a /\ live h0 out /\ eq_or_disjoint a out /\ as_nat P256 h0 a < getPrime P256))
    (ensures (fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      as_nat P256 h1 out == (2 * as_nat P256 h0 a) % getPrime P256 /\
      as_nat P256 h1 out == toDomain #P256 (2 * fromDomain #P256 (as_nat P256 h0 a) % getPrime P256)))

let felem_double_p256 arg1 out = felem_double_ #P256 arg1 out

[@CInline]
val felem_double_p384: a: felem P384 -> out: felem P384 ->
  Stack unit
    (requires (fun h0 ->
      live h0 a /\ live h0 out /\ eq_or_disjoint a out /\ as_nat P384 h0 a < getPrime P384))
    (ensures (fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      as_nat P384 h1 out == (2 * as_nat P384 h0 a) % getPrime P384 /\
      as_nat P384 h1 out == toDomain #P384 (2 * fromDomain #P384 (as_nat P384 h0 a) % getPrime P384)))

let felem_double_p384 arg1 out = felem_double_ #P384 arg1 out

[@CInline]
val felem_double_generic: a: felem Default -> out: felem Default ->
  Stack unit
    (requires (fun h0 ->
      live h0 a /\ live h0 out /\ eq_or_disjoint a out /\ as_nat Default h0 a < getPrime Default))
    (ensures (fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      as_nat Default h1 out == (2 * as_nat Default h0 a) % getPrime Default /\
      as_nat Default h1 out == toDomain #Default (2 * fromDomain #Default (as_nat Default h0 a) % getPrime Default)))

let felem_double_generic arg1 out = felem_double_ #Default arg1 out


let felem_double #c arg1 out = 
  match c with 
  |P256 -> felem_double_p256 arg1 out
  |P384 -> felem_double_p384 arg1 out
  |Default -> felem_double_generic arg1 out


#set-options "--fuel 1 --ifuel 1 --z3rlimit 200"


inline_for_extraction noextract
val felem_sub_: #c: curve -> a: felem c -> b: felem c -> out: felem c ->
  Stack unit
  (requires (fun h0 ->
    live h0 out /\ live h0 a /\ live h0 b /\ eq_or_disjoint a out /\ eq_or_disjoint b out /\ eq_or_disjoint a b /\
    as_nat c h0 a < getPrime c /\ as_nat c h0 b < getPrime c))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat c h1 out == (as_nat c h0 a - as_nat c h0 b) % getPrime c /\
    as_nat c h1 out == toDomain #c ((fromDomain #c (as_nat c h0 a) - fromDomain #c (as_nat c h0 b)) % getPrime c)))

let felem_sub_ #c arg1 arg2 out =
    let h0 = ST.get() in
  let t = sub_bn arg1 arg2 out in
    let h1 = ST.get() in 
    lseq_upperbound (as_seq h0 arg1);
    lseq_upperbound (as_seq h0 arg2);
    lseq_upperbound (as_seq h1 out);

  let r = add_dep_prime #c out t out in 
    let h2 = ST.get() in

  modulo_addition_lemma (as_nat c h0 arg1 - as_nat c h0 arg2) (getPrime c) 1;
  
  assert(
    let prime = getPrime c in 
    if as_nat c h0 arg1 - as_nat c h0 arg2 >= 0 then
      begin
	modulo_lemma (as_nat c h0 arg1 - as_nat c h0 arg2) prime;
	as_nat c h2 out == (as_nat c h0 arg1 - as_nat c h0 arg2) % prime
      end
    else
      begin
	lseq_upperbound (as_seq h2 out);
	lemma_mod_plus (as_nat c h2 out) (v r) (pow2 (getPower c));
	lemma_mod_plus (as_nat c h0 arg1 - as_nat c h0 arg2 + prime) 1 (pow2 (getPower c));
	modulo_lemma (as_nat c h2 out) (pow2 (getPower c));
	modulo_lemma (as_nat c h0 arg1 - as_nat c h0 arg2 + prime) (pow2 (getPower c));
	modulo_lemma (as_nat c h2 out) prime;
	as_nat c h2 out == (as_nat c h0 arg1 - as_nat c h0 arg2) % prime
      end);

  substractionInDomain #c #DH (as_nat c h0 arg1) (as_nat c h0 arg2); 
  inDomain_mod_is_not_mod #c #DH (fromDomain #c (as_nat c h0 arg1) - fromDomain #c (as_nat c h0 arg2))

[@CInline]
val felem_sub_p256: a: felem P256 -> b: felem P256 -> out: felem P256 ->
  Stack unit
  (requires (fun h0 ->
    live h0 out /\ live h0 a /\ live h0 b /\ eq_or_disjoint a out /\ eq_or_disjoint b out /\ eq_or_disjoint a b /\
    as_nat P256 h0 a < getPrime P256 /\ as_nat P256 h0 b < getPrime P256))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat P256 h1 out == (as_nat P256 h0 a - as_nat P256 h0 b) % getPrime P256 /\
    as_nat P256 h1 out == toDomain #P256 ((fromDomain #P256 (as_nat P256 h0 a) - fromDomain #P256 (as_nat P256 h0 b)) % getPrime P256)))

let felem_sub_p256 a b out = felem_sub_ #P256 a b out

[@CInline]
val felem_sub_p384: a: felem P384 -> b: felem P384 -> out: felem P384 ->
  Stack unit
  (requires (fun h0 ->
    live h0 out /\ live h0 a /\ live h0 b /\ eq_or_disjoint a out /\ eq_or_disjoint b out /\ eq_or_disjoint a b /\
    as_nat P384 h0 a < getPrime P384 /\ as_nat P384 h0 b < getPrime P384))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat P384 h1 out == (as_nat P384 h0 a - as_nat P384 h0 b) % getPrime P384 /\
    as_nat P384 h1 out == toDomain #P384 ((fromDomain #P384 (as_nat P384 h0 a) - fromDomain #P384 (as_nat P384 h0 b)) % getPrime P384)))

let felem_sub_p384 a b out = felem_sub_ #P384 a b out

[@CInline]
val felem_sub_generic: a: felem Default -> b: felem Default -> out: felem Default ->
  Stack unit
  (requires (fun h0 ->
    live h0 out /\ live h0 a /\ live h0 b /\ eq_or_disjoint a out /\ eq_or_disjoint b out /\ eq_or_disjoint a b /\
    as_nat Default h0 a < getPrime Default /\ as_nat Default h0 b < getPrime Default))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat Default h1 out == (as_nat Default h0 a - as_nat Default h0 b) % getPrime Default /\
    as_nat Default h1 out == toDomain #Default ((fromDomain #Default (as_nat Default h0 a) - fromDomain #Default (as_nat Default h0 b)) % getPrime Default)))

let felem_sub_generic a b out = felem_sub_ #Default a b out


let felem_sub #c a b out = 
  match c with 
  |P256 -> felem_sub_p256 a b out
  |P384 -> felem_sub_p384 a b out
  |Default -> felem_sub_generic a b out


 *)
let mul #c f r out =
  let h0 = ST.get() in 
  let len = getCoordinateLenU64 c in 
  bn_mul len len f r out;
  Hacl.Spec.Bignum.bn_mul_lemma (as_seq h0 f) (as_seq h0 r)
