module Hacl.Impl.P256.Exponent

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Hacl.Impl.P256.Math 

open Lib.IntTypes
open Lib.Buffer

open FStar.Math.Lemmas
open FStar.Mul

open Hacl.Spec.EC.Definition
open Hacl.Lemmas.P256
open Hacl.Impl.P256.LowLevel 
open Spec.ECC
open Spec.ECC.Curves
open Lib.Loops

open Hacl.Impl.P256.MM.Lemmas

open Hacl.Impl.EC.MontgomeryMultiplication


open Hacl.Spec.MontgomeryMultiplication

#set-options "--z3rlimit 100 --ifuel 0 --fuel 0"


(* Changing argument order *)
inline_for_extraction noextract
val montgomery_multiplication_buffer_: result: felem P256 -> a: felem P256 -> b: felem P256 -> Stack unit
  (requires (fun h -> live h a /\  as_nat P256 h a < prime256 /\ live h b /\ live h result /\ as_nat P256 h b < prime256)) 
  (ensures (fun h0 _ h1 -> modifies (loc result) h0 h1) (*/\  
    as_nat h1 result < prime256 /\
    as_nat h1 result = (as_nat h0 a * as_nat h0 b * modp_inv2_prime (pow2 256) prime256) % prime256 /\
    as_nat h1 result = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 b) % prime256) /\
    as_nat h1 result = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 b))) *)
  )


let montgomery_multiplication_buffer_ result a b = 
  montgomery_multiplication_buffer a b result





inline_for_extraction noextract
val montgomery_square_buffer_: result: felem P256 -> a: felem P256 -> Stack unit
  (requires (fun h -> live h a /\ as_nat P256 h a < prime256 /\ live h result)) 
  (ensures (fun h0 _ h1 -> modifies (loc result) h0 h1 (* /\  
    as_nat h1 result < prime256 /\ 
    as_nat h1 result = (as_nat h0 a * as_nat h0 a * modp_inv2_prime (pow2 256) prime256) % prime256 /\
    as_nat h1 result = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a) % prime256) /\
    as_nat h1 result = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a))*) )
  )


let montgomery_square_buffer_ result a = montgomery_square_buffer #P256 a result

inline_for_extraction noextract
val exponent_0: t: felem P256 -> t0: felem P256 -> t1: felem P256 -> t2: felem P256 -> t6: felem P256 -> t7: felem P256 -> 
  Stack unit 
  (requires fun h -> live h t /\ live h t0 /\ live h t1 /\ live h t2 /\ live h t6 /\ live h t7 /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc t; loc t0; loc t1; loc t2; loc t6; loc t7] /\
    as_nat P256 h t < prime256)
  (ensures fun h0 _ h1 -> modifies (loc t0 |+| loc t1 |+| loc t2 |+| loc t6 |+| loc t7) h0 h1 (* /\ (
    let tD = fromDomain_ (as_nat h0 t) in 
    as_nat h1 t2 = toDomain_ (pow tD 3 % prime256) /\ as_nat h1 t1 = toDomain_ (pow tD 1023 % prime256) /\ 
    as_nat h1 t0 = toDomain_ (pow tD 2046 % prime256)) /\
    as_nat h1 t0 < prime256 /\ as_nat h1 t1 < prime256 /\ as_nat h1 t2 < prime256 *)
  )


let exponent_0 t t0 t1 t2 t6 t7 = 
    let h0 = ST.get() in 
  montgomery_square_buffer_ t0 t; 
  montgomery_multiplication_buffer_ t2 t0 t; 
  montgomery_square_buffer_ t0 t2; 
  montgomery_square_buffer_ t0 t0;
  montgomery_multiplication_buffer_ t6 t0 t2;
  montgomery_square_buffer_ t0 t6;
  fsquarePowN #P256 (size 3) t0; 
  montgomery_multiplication_buffer_ t7 t0 t6;
  montgomery_square_buffer_ t0 t7;
  montgomery_square_buffer_ t0 t0;
  montgomery_multiplication_buffer_ t1 t0 t2;
  montgomery_square_buffer_ t0 t1;
    let h1 = ST.get() in 

   (* let tD = fromDomain_ (as_nat h0 t) in 
    
    calc (==) {(tD * tD % prime256 * tD % prime256) * (tD * tD % prime256 * tD % prime256) % prime256; 
      (==) {lemma_6_powers tD} pow tD 6 % prime256;};

    calc (==) {(pow tD 6 % prime256 * (pow tD 6 % prime256) % prime256) * (tD * tD % prime256 * tD % prime256) % prime256;
      (==) {lemma_15_powers tD} pow tD 15 % prime256;   };

    calc (==) {pow ((pow tD 15 % prime256 * (pow tD 15 % prime256) % prime256)) 8 % prime256;
      (==) {lemma_pow_sum tD 15 15} 
    pow ((pow tD 30 % prime256)) 8 % prime256;  
      (==) {power_distributivity (pow tD 30) 8 prime256}
    pow (pow tD 30) 8 % prime256;  
      (==) {power_mult tD 30 8}
    pow tD 240 % prime256;};

    calc (==) {pow tD 240 % prime256 * (pow tD 15 % prime256) % prime256 * (pow tD 240 % prime256 * (pow tD 15 % prime256) % prime256) % prime256;
      (==) {lemma_pow_sum tD 240 15}
    pow tD 255 % prime256 * (pow tD 255 % prime256) % prime256;
      (==) {lemma_pow_sum tD 255 255}
    pow tD 510 % prime256;};

    calc (==) {pow tD 510 % prime256 * (pow tD 510 % prime256) % prime256;
      (==) {lemma_pow_sum tD 510 510}
    pow tD 1020 % prime256;};

    calc (==) {tD * tD % prime256 * tD % prime256;
      (==) {lemma_mod_mul_distr_l (tD * tD) tD prime256}
    tD * tD * tD % prime256;
      (==) {pow_plus tD 1 1}
    pow tD 2 * tD % prime256;
      (==) {pow_plus tD 2 1}
    pow tD 3 % prime256;};

    calc (==) {pow tD 1020 % prime256 * (pow tD 3 % prime256) % prime256;
      (==) {lemma_pow_sum tD 1020 3}
    pow tD 1023 % prime256;};

    calc (==) {pow tD 1023 % prime256 * (pow tD 1023 % prime256) % prime256;
      (==) {lemma_pow_sum tD 1023 1023}
    pow tD 2046 % prime256;}*) ()

 (* assert(as_nat h5 t6 = toDomain_ (pow tD 15 % prime256)); *)
 (* assert(as_nat h8 t7 = toDomain_ (pow tD 240 % prime256 * (pow tD 15 % prime256) % prime256)); *)



inline_for_extraction noextract
val exponent_1: t: felem P256 -> t0: felem P256 -> t1: felem P256 -> t2: felem P256 -> t3: felem P256 -> t4: felem P256 -> t5: felem P256 -> Stack unit 
  (requires fun h -> live h t (*/\ live h t0 /\ live h t1 /\ live h t2 /\ live h t3 /\ live h t4 /\ live h t5 /\
    LowStar.Monotonic.Buffer.all_disjoint [loc t; loc t0; loc t1; loc t2; loc t3; loc t4; loc t5] /\
    as_nat P256 h t < prime256 /\ as_nat h t0 < prime256 /\ as_nat h t1 < prime256 /\ as_nat h t2 < prime256*) )
  (ensures fun h0 _ h1 -> modifies (loc t0 |+| loc t1 |+| loc t2 |+| loc t3 |+| loc t4 |+| loc t5) h0 h1 (*/\ (
    let t0D = fromDomain_ (as_nat h0 t0) in 
    let t1D = fromDomain_ (as_nat h0 t1) in 
    let t2D = fromDomain_ (as_nat h0 t2) in 
    let tD = fromDomain_ (as_nat h0 t) in 
    as_nat h1 t0 == toDomain_ (pow t0D (pow2 181 + pow2 21) * pow t1D (pow2 172 + pow2 162 + pow2 12 + 4) * pow t2D (pow2 160 + 1) * pow tD (pow2 128) % prime256) /\
    as_nat h1 t4 == toDomain_ (pow t0D (pow2 19) * pow t1D (pow2 10 + 1) % prime256) /\
    as_nat h1 t5 == toDomain_ (pow t0D (pow2 21) * pow t1D (pow2 12 + 4) * pow t2D 1 % prime256)) /\
    as_nat h1 t0 < prime256 /\ as_nat h1 t4 < prime256 /\ as_nat h1 t5 < prime256 *)
  )

let exponent_1 t t0 t1 t2 t3 t4 t5 = 
    let h0 = ST.get() in 
  fsquarePowN #P256 (size 9) t0;
  montgomery_multiplication_buffer_ t3 t0 t1;
  montgomery_square_buffer_ t0 t3;
  fsquarePowN #P256  (size 9) t0;
  montgomery_multiplication_buffer_ t4 t0 t1;
  montgomery_square_buffer_ t0 t4;
  montgomery_square_buffer_ t0 t0;
  montgomery_multiplication_buffer_ t5 t0 t2;
  montgomery_square_buffer_ t0 t5;
  fsquarePowN #P256  (size 31) t0;
  montgomery_multiplication_buffer_ t0 t0 t;
  fsquarePowN  #P256 (size 128) t0;
  montgomery_multiplication_buffer_ t0 t0 t5; ()
(*
  let tD = fromDomain_ (as_nat h0 t) in let t0D = fromDomain_ (as_nat h0 t0) in 
  let t1D = fromDomain_ (as_nat h0 t1) in let t2D = fromDomain_ (as_nat h0 t2) in 

  (* h3 *)
  calc (==) {pow t0D (pow2 9) % prime256 * pow t1D 1 % prime256 * (pow t0D (pow2 9) % prime256 * pow t1D 1 % prime256) % prime256;
    (==) {lemma_pow_sum2 t0D t1D (pow2 9) (pow2 9) 1 1}
  pow t0D (2 * pow2 9) * pow t1D 2 % prime256; 
    (==) {pow2_double_mult 9}
  pow t0D (pow2 10) * pow t1D 2 % prime256;};

  (* let pow2_19 = pow2 19 in let pow2_20 = pow2 20 in 
  let pow2_21 = pow2 21 in let pow2_76 = pow2 76 in let pow2_88 = pow2 88 in let pow2_152 = pow2 152 in  *)

  (*h4 *)
  lemma_exp_1_0 t0D t1D; 

  (* h5 *)
  lemma_exp_1_1 t0D t1D;
  
  (* h6 *)
  lemma_exp_1_2 t0D t1D;
  (* h7 *)
  lemma_exp_1_3 t0D t1D;
  (* h8 *)
  lemma_exp_1_4 t0D t1D t2D;
  
  (* h9 *)
  lemma_exp_1_5 t0D t1D t2D;

  (* h10 *) 
  lemma_exp_1_6 t0D t1D t2D;

  (* h11 *)
  lemma_mod_mul_distr_l (pow t0D (pow2 53) * pow t1D (pow2 44 + pow2 34) * pow t2D (pow2 32)) tD prime256;
  (* h12*) 
  lemma_exp_1_7 tD t0D t1D t2D;

  (* h13  *)
  lemma_exp_1_8 tD t0D t1D t2D (*;
  
  assert(as_nat h1 t0 =  toDomain_ (pow t0D (pow2 9) % prime256)); 
  assert(as_nat h2 t3 =  toDomain_ (pow t0D (pow2 9) % prime256 * pow t1D 1 % prime256)); 
  assert(as_nat h3 t0 =  toDomain_ (pow t0D (pow2 10) * pow t1D 2 % prime256));  
  assert(as_nat h4 t0 =  toDomain_ (pow t0D (pow2_19) * pow t1D (pow2 10) % prime256)); 
  assert(as_nat h5 t4 =  toDomain_ (pow t0D (pow2_19) * pow t1D (pow2 10 + 1) % prime256)); 
  assert(as_nat h6 t0 =  toDomain_ (pow t0D (pow2_20) * pow t1D (pow2 11 + 2) % prime256)); 
  assert(as_nat h7 t0 =  toDomain_ (pow t0D (pow2 21) * pow t1D (pow2 12 + 4) % prime256));  
  assert(as_nat h8 t5 =  toDomain_ (pow t0D (pow2 21) * pow t1D (pow2 12 + 4) * pow t2D 1 % prime256));
  assert(as_nat h9 t0 =  toDomain_ (pow t0D (pow2 22) * pow t1D (pow2 13 + 8) * pow t2D 2 % prime256)); 
  assert(as_nat h10 t0 = toDomain_ (pow t0D (pow2 53) * pow t1D (pow2 44 + pow2 34) * pow t2D (pow2 32) % prime256));
  assert(as_nat h11 t0 = toDomain_ (pow t0D (pow2 53) * pow t1D (pow2 44 + pow2 34) * pow t2D (pow2 32) * tD % prime256));
  
  assert(as_nat h12 t0 = toDomain_ (pow t0D (pow2 181) * pow t1D (pow2 172 + pow2 162) * pow t2D (pow2 160) * pow tD (pow2 128) % prime256));

  assert(as_nat h13 t0 = toDomain_ (pow t0D (pow2 181 + pow2 21) * pow t1D (pow2 172 + pow2 162 + pow2 12 + 4) * pow t2D (pow2 160 + 1) * pow tD (pow2 128) % prime256)) *) *)
  



inline_for_extraction noextract
val exponent_2: t: felem P256 -> t0: felem P256-> t4: felem P256-> t5: felem P256-> result: felem P256->
  Stack unit 
  (requires fun h -> live h t /\ live h t0 /\ live h t4 /\ live h t5 /\ live h result (*
    as_nat h t < prime256 /\ as_nat h t0 < prime256 /\ as_nat h t4 < prime256 /\ as_nat h t5 < prime256 /\
    LowStar.Monotonic.Buffer.all_disjoint [loc t; loc t0;  loc t4; loc t5]*) )
  (ensures fun h0 _ h1 -> modifies (loc t0 |+| loc t4 |+| loc t5 |+| loc result) h0 h1 (*/\ (
    let t0D = fromDomain_ (as_nat h0 t0) in 
    let t5D = fromDomain_ (as_nat h0 t5) in 
    let t4D = fromDomain_ (as_nat h0 t4) in 
    let tD = fromDomain_ (as_nat h0 t) in 
    as_nat h1 result = toDomain_ (pow t0D (pow2 64) * pow t5D (pow2 32) * pow t4D (pow2 2) * tD % prime256)) /\ 
    as_nat h1 result < prime256*)
  )

let exponent_2 t t0 t4 t5 result = 
    let h0 = ST.get() in 
  fsquarePowN #P256  (size 32) t0;
  montgomery_multiplication_buffer_ t0 t0 t5; 
  fsquarePowN #P256  (size 30) t0;
  montgomery_multiplication_buffer_ t0 t0 t4;
  fsquarePowN  #P256 (size 2) t0;
  montgomery_multiplication_buffer_ result t0 t; 
(*
  let tD =  fromDomain_ (as_nat h0 t) in 
  let t0D = fromDomain_ (as_nat h0 t0) in 
  let t5D = fromDomain_ (as_nat h0 t5) in 
  let t4D = fromDomain_ (as_nat h0 t4) in 

  let pow2_30 = pow2 30 in 
  let pow2_32 = pow2 32 in 
  let pow2_62 = pow2 62 in 
  let pow2_64 = pow2 64 in 
  
  calc (==) {pow t0D pow2_32 % prime256 * t5D % prime256;
    (==) {lemma_mod_mul_distr_l (pow t0D pow2_32) t5D prime256}
  pow t0D pow2_32 * t5D % prime256;};

  lemma_exp_2_0 t0D t5D;

  calc (==) {pow t0D pow2_62 * pow t5D pow2_30 % prime256 * t4D % prime256;
    (==) {lemma_mod_mul_distr_l (pow t0D pow2_62 * pow t5D pow2_30) t4D prime256}
  pow t0D pow2_62 * pow t5D pow2_30 * t4D % prime256;};

  lemma_exp_2_1 t0D t4D t5D;

  calc (==) {pow t0D pow2_64 * pow t5D pow2_32 * pow t4D (pow2 2) % prime256 * tD % prime256;
    (==) {lemma_mod_mul_distr_l (pow t0D pow2_64 * pow t5D pow2_32 * pow t4D (pow2 2)) tD prime256}
  pow t0D pow2_64 * pow t5D pow2_32 * pow t4D (pow2 2) * tD % prime256;} *) ()


[@ CInline]
val exponent_p256: a: felem P256->result: felem P256 -> tempBuffer: lbuffer uint64 (getCoordinateLenU P256 *. 8ul) -> Stack unit
  (requires fun h -> live h a /\ live h tempBuffer /\ live h result /\ disjoint tempBuffer result /\ 
    disjoint a tempBuffer /\ as_nat P256 h a < prime256)
  (ensures fun h0 _ h1 -> modifies2 result tempBuffer h0 h1 /\ (
    let k = fromDomain_ #P256 (as_nat P256 h0 a) in 
    as_nat P256 h1 result =  toDomain_ #P256 (pow k (prime256 - 2) % prime256)))


let exponent_p256 t result tempBuffer = 
  let h0 = ST.get () in 

  let t0 = sub tempBuffer (size 0) (size 4) in 
  let t1 = sub tempBuffer (size 4) (size 4) in 
  let t2 = sub tempBuffer (size 8) (size 4) in 
  let t3 = sub tempBuffer (size 12) (size 4) in 
  let t4 = sub tempBuffer (size 16) (size 4) in 
  let t5 = sub tempBuffer (size 20) (size 4) in 
  let t6 = sub tempBuffer (size 24) (size 4) in 
  let t7 = sub tempBuffer (size 28) (size 4) in 

  exponent_0 t t0 t1 t2 t6 t7;
    let h1 = ST.get() in 
  exponent_1 t t0 t1 t2 t3 t4 t5; 
    let h2 = ST.get() in 
  exponent_2 t t0 t4 t5 result;
    let h3 = ST.get() in 

  let tD = fromDomain_ #P256 (as_nat P256 h0 t) in 
  
  lemma_exp_1 tD; 
  lemma_exp_2 tD;
  lemma_exp_3 tD;
  lemma_exp_4 tD
