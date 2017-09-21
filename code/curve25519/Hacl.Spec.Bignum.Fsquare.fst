module Hacl.Spec.Bignum.Fsquare

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Bignum.Limb
open Hacl.Spec.Bignum
open Hacl.Spec.Bignum.Bigint
open Hacl.Spec.Bignum.Modulo
open Hacl.Spec.Bignum.Fproduct
open Hacl.Spec.EC.AddAndDouble


#set-options "--initial_fuel 0 --max_fuel 0 --z3refresh"

inline_for_extraction let p64 : p:pos{p = 0x10000000000000000} = assert_norm(pow2 64 = 0x10000000000000000); pow2 64
inline_for_extraction let p128 : p:pos{p = 0x100000000000000000000000000000000} = assert_norm(pow2 128 = 0x100000000000000000000000000000000); pow2 128

val fsquare_pre_: s:seqelem -> GTot Type0
let fsquare_pre_ s =
  let _ = () in
  let r0 = v (Seq.index s 0) in let r1 = v (Seq.index s 1) in let r2 = v (Seq.index s 2) in
  let r3 = v (Seq.index s 3) in let r4 = v (Seq.index s 4) in
  let d0 = r0 * 2 in let d1 = r1 * 2 in let d2 = r2 * 2 * 19 in let d3 = r3 * 19 in
  let d419 = r4 * 19 in let d4 = d419 * 2 in
  d0 < p64 /\ d1 < p64 /\ d2 < p64 /\ d3 < p64 /\ d419 < p64 /\ d4 < p64
  /\ r0 * r0 + d4 * r1 + d2 * r3 < p128
  /\ d0 * r1 + d4 * r2 + r3 * d3 < p128
  /\ d0 * r2 + r1 * r1 + d4 * r3 < p128
  /\ d0 * r3 + d1 * r2 + r4 * d419 < p128
  /\ d0 * r4 + d1 * r3 + r2 * r2 < p128


#set-options "--z3rlimit 100"

val seq_upd_5: s0:wide -> s1:wide -> s2:wide -> s3:wide -> s4:wide ->
  Tot (s':Seq.seq wide{Seq.length s' = len /\ Seq.index s' 0 == s0 /\ Seq.index s' 1 == s1 /\ Seq.index s' 2 == s2 /\ Seq.index s' 3 == s3 /\ Seq.index s' 4 == s4})
let seq_upd_5 s0 s1 s2 s3 s4 =
  let s  = Seq.create len wide_zero in
  let s' = Seq.upd s 0 s0 in
  let s' = Seq.upd s' 1 s1 in
  let s' = Seq.upd s' 2 s2 in
  let s' = Seq.upd s' 3 s3 in
  let s' = Seq.upd s' 4 s4 in
  s'


#set-options "--z3rlimit 10"

inline_for_extraction val computation_1:
  r0:limb -> r1:limb -> r2:limb -> r3:limb -> r4:limb -> d4:limb{v d4 = 2 * 19 * v r4} -> d2:limb{v d2 = 2 * 19 * v r2 /\ v d2 < p64 /\ v d4 < p64
  /\ v r0 * v r0 + v d4 * v r1 + v d2 * v r3 < p128}
  -> Tot (res:wide{w res = v r0 * v r0      + 2 * 19 * v r4 * v r1  + 2 * 19 * v r2 * v r3})
inline_for_extraction let computation_1 r0 r1 r2 r3 r4 d4 d2 =
  let open Hacl.Bignum.Wide in
  (( r0) *^ r0 +^ ( d4) *^ r1 +^ (( d2) *^ (r3     )))  

#set-options "--z3rlimit 10 --initial_fuel 0 --max_fuel 0"

inline_for_extraction val computation_2:
  r0:limb -> r1:limb -> r2:limb -> r3:limb -> r4:limb -> d4:limb{v d4 = 2 * 19 * v r4} -> d0:limb{v d0 = 2 * v r0 /\ v d0 < p64 /\ v d4 < p64 /\ 19 * v r3 < p64
  /\ v d0 * v r1 + v d4 * v r2 + 19 * v r3 * v r3 < p128}
  -> Tot (res:wide{w res = 2 * v r0 * v r1  + 2 * 19 * v r4 * v r2  + 19 * v r3 * v r3})
inline_for_extraction let computation_2 r0 r1 r2 r3 r4 d4 d0 =
  let open Hacl.Bignum.Wide in
  (( d0) *^ r1 +^ ( d4) *^ r2 +^ (Hacl.Bignum.Limb.(r3 *^ (uint64_to_limb 19uL)) *^ r3))

#set-options "--z3rlimit 10"

inline_for_extraction val computation_3:
  r0:limb -> r1:limb -> r2:limb -> r3:limb -> r4:limb -> d4:limb{v d4 = 2 * 19 * v r4} -> d0:limb{v d0 = 2 * v r0 /\ v d0 < p64 /\ v d4 < p64
  /\ v d0 * v r2 + v r1 * v r1 + v d4 * v r3 < p128}
  -> Tot (res:wide{w res = 2 * v r0 * v r2  + v r1 * v r1           + 2 * 19 * v r4 * v r3})
inline_for_extraction let computation_3 r0 r1 r2 r3 r4 d4 d0 =
  let open Hacl.Bignum.Wide in
  ( d0) *^ r2 +^ ( r1) *^ r1 +^ (( d4) *^ (r3     ))

#set-options "--z3rlimit 10 --initial_fuel 0 --max_fuel 0"

inline_for_extraction val computation_4:
  r0:limb -> r1:limb -> r2:limb -> r3:limb -> r4:limb -> d419:limb{v d419 = 19 * v r4} -> d0:limb{v d0 = 2 * v r0} -> d1:limb{v d1 = 2 * v r1 /\ v d0 < p64 /\ v d419 < p64 /\ v d1 < p64 /\ 19 * v r3 < p64
  /\ v d0 * v r3 + v d1 * v r2 + v r4 * v d419 < p128}
  -> Tot (res:wide{w res = 2 * v r0 * v r3  + 2 * v r1 * v r2       + 19 * v r4 * v r4})
inline_for_extraction let computation_4 r0 r1 r2 r3 r4 d419 d0 d1 =
  let open Hacl.Bignum.Wide in
  ( d0) *^ r3 +^ ( d1) *^ r2 +^ (( r4) *^ (d419   ))


inline_for_extraction val computation_5:
  r0:limb -> r1:limb -> r2:limb -> r3:limb -> r4:limb -> d0:limb{v d0 = 2 * v r0} -> d1:limb{v d1 = 2 * v r1 /\ v d0 < p64 /\ v d1 < p64 /\ 19 * v r3 < p64
  /\ v d0 * v r4 + v d1 * v r3 + v r2 * v r2 < p128}
  -> Tot (res:wide{w res = 2 * v r0 * v r4  + 2 * v r1 * v r3       + v r2 * v r2})
inline_for_extraction let computation_5 r0 r1 r2 r3 r4 d0 d1 =
  let open Hacl.Bignum.Wide in
  ( d0) *^ r4 +^ ( d1) *^ r3 +^ (( r2) *^ (r2     ))

#reset-options "--z3rlimit 71 --initial_fuel 0 --max_fuel 0"

val fsquare_spec_: s:seqelem{fsquare_pre_ s} -> Tot (s':seqelem_wide{
  let r0 = v (Seq.index s 0) in
  let r1 = v (Seq.index s 1) in
  let r2 = v (Seq.index s 2) in
  let r3 = v (Seq.index s 3) in
  let r4 = v (Seq.index s 4) in
  w (Seq.index s' 0)   = r0 * r0      + 2 * 19 * r4 * r1  + 2 * 19 * r2 * r3
  /\ w (Seq.index s' 1) = 2 * r0 * r1  + 2 * 19 * r4 * r2  + 19 * r3 * r3
  /\ w (Seq.index s' 2) = 2 * r0 * r2  + r1 * r1           + 2 * 19 * r4 * r3
  /\ w (Seq.index s' 3) = 2 * r0 * r3  + 2 * r1 * r2       + 19 * r4 * r4
  /\ w (Seq.index s' 4) = 2 * r0 * r4  + 2 * r1 * r3       + r2 * r2
})
let fsquare_spec_ s =
  let r0 = Seq.index s 0 in
  let r1 = Seq.index s 1 in
  let r2 = Seq.index s 2 in
  let r3 = Seq.index s 3 in
  let r4 = Seq.index s 4 in
  let d0 = r0 *^ (uint64_to_limb 2uL) in
  let d1 = r1 *^ (uint64_to_limb 2uL) in
  let d2 = r2 *^ (uint64_to_limb 2uL) *^ (uint64_to_limb 19uL) in
  let d419 = r4 *^ (uint64_to_limb 19uL) in
  let d4 = d419 *^ (uint64_to_limb 2uL) in
  let open Hacl.UInt128 in
  let s0 = computation_1 r0 r1 r2 r3 r4 d4 d2 in
  let s1 =  computation_2 r0 r1 r2 r3 r4 d4 d0 in
  let s2 =  computation_3 r0 r1 r2 r3 r4 d4 d0 in
  let s3 = computation_4 r0 r1 r2 r3 r4 d419 d0 d1 in
  let s4 = computation_5 r0 r1 r2 r3 r4 d0 d1 in
  let open Hacl.UInt64 in
  cut (w s0 = v r0 * v r0      + 2 * 19 * v r4 * v r1  + 2 * 19 * v r2 * v r3);
  cut (w s1 = 2 * v r0 * v r1  + 2 * 19 * v r4 * v r2  + 19 * v r3 * v r3);
  cut (w s2 = 2 * v r0 * v r2  + v r1 * v r1           + 2 * 19 * v r4 * v r3);
  cut (w s3 = 2 * v r0 * v r3  + 2 * v r1 * v r2       + 19 * v r4 * v r4);
  cut (w s4 = 2 * v r0 * v r4  + 2 * v r1 * v r3       + v r2 * v r2);
  seq_upd_5 s0 s1 s2 s3 s4

#reset-options "--z3rlimit 5 --initial_fuel 0 --max_fuel 0"

private let lemma_mul_5 a b c d e : Lemma ( (a+b+c+d+e)*(a+b+c+d+e) =
  a * a + a * b + a * c + a * d + a * e
  + b * a + b * b + b * c + b * d + b * e
  + c * a + c * b + c * c + c * d + c * e
  + d * a + d * b + d * c + d * d + d * e
  + e * a + e * b + e * c + e * d + e * e) =
    Math.Lemmas.distributivity_add_right (a+b+c+d+e) a (b+c+d+e);
    Math.Lemmas.distributivity_add_right (a+b+c+d+e) b (c+d+e);
    Math.Lemmas.distributivity_add_right (a+b+c+d+e) c (d+e);
    Math.Lemmas.distributivity_add_right (a+b+c+d+e) d (e);
    Math.Lemmas.distributivity_add_left (a) (b+c+d+e) (a);
    Math.Lemmas.distributivity_add_left (b) (c+d+e) (a);
    Math.Lemmas.distributivity_add_left (c) (d+e) (a);
    Math.Lemmas.distributivity_add_left (d) (e) (a);
    Math.Lemmas.distributivity_add_left (a) (b+c+d+e) (b);
    Math.Lemmas.distributivity_add_left (b) (c+d+e) (b);
    Math.Lemmas.distributivity_add_left (c) (d+e) (b);
    Math.Lemmas.distributivity_add_left (d) (e) (b);
    Math.Lemmas.distributivity_add_left (a) (b+c+d+e) (c);
    Math.Lemmas.distributivity_add_left (b) (c+d+e) (c);
    Math.Lemmas.distributivity_add_left (c) (d+e) (c);
    Math.Lemmas.distributivity_add_left (d) (e) (c);
    Math.Lemmas.distributivity_add_left (a) (b+c+d+e) (d);
    Math.Lemmas.distributivity_add_left (b) (c+d+e) (d);
    Math.Lemmas.distributivity_add_left (c) (d+e) (d);
    Math.Lemmas.distributivity_add_left (d) (e) (d);
    Math.Lemmas.distributivity_add_left (a) (b+c+d+e) (e);
    Math.Lemmas.distributivity_add_left (b) (c+d+e) (e);
    Math.Lemmas.distributivity_add_left (c) (d+e) (e);
    Math.Lemmas.distributivity_add_left (d) (e) (e)


#set-options "--z3rlimit 10"

val lemma_fsquare_spec_2_1: s:seqelem -> Lemma
  (let r0 = v (Seq.index s 0) in
  let r1 = v (Seq.index s 1) in
  let r2 = v (Seq.index s 2) in
  let r3 = v (Seq.index s 3) in
  let r4 = v (Seq.index s 4) in
  (seval s * seval s =
  r0 * r0 + r0 * (pow2 51 * r1) + r0 * (pow2 102 * r2) + r0 * (pow2 153 * r3) + r0 * (pow2 204 * r4)
  + (pow2 51 * r1) * r0 + (pow2 51 * r1) * (pow2 51 * r1) + (pow2 51 * r1) * (pow2 102 * r2) + (pow2 51 * r1) * (pow2 153 * r3) + (pow2 51 * r1) * (pow2 204 * r4)
  + (pow2 102 * r2) * r0 + (pow2 102 * r2) * (pow2 51 * r1) + (pow2 102 * r2) * (pow2 102 * r2) + (pow2 102 * r2) * (pow2 153 * r3) + (pow2 102 * r2) * (pow2 204 * r4)
  + (pow2 153 * r3) * r0 + (pow2 153 * r3) * (pow2 51 * r1) + (pow2 153 * r3) * (pow2 102 * r2) + (pow2 153 * r3) * (pow2 153 * r3) + (pow2 153 * r3) * (pow2 204 * r4)
  + (pow2 204 * r4) * r0 + (pow2 204 * r4) * (pow2 51 * r1) + (pow2 204 * r4) * (pow2 102 * r2) + (pow2 204 * r4) * (pow2 153 * r3) + (pow2 204 * r4) * (pow2 204 * r4)))
let lemma_fsquare_spec_2_1 s =
  lemma_seval_5 s;
  let r0 = v (Seq.index s 0) in
  let r1 = v (Seq.index s 1) in
  let r2 = v (Seq.index s 2) in
  let r3 = v (Seq.index s 3) in
  let r4 = v (Seq.index s 4) in
  lemma_mul_5 r0 (pow2 51 * r1) (pow2 102 * r2) (pow2 153 * r3) (pow2 204 * r4)


private let lemma_aux_1 a b c : Lemma ( a * b * c = b * (a * c) ) = ()
private let lemma_aux_2 a b c d : Lemma ( (b * d) * a * c = (b * a) * (d * c) ) = ()
private let lemma_aux_3 a b c : Lemma ( a * b * c = (a * b) * c ) = ()


#reset-options "--z3rlimit 200 --max_fuel 00"

val lemma_fsquare_spec_2_2_0: r0:nat -> r1:nat -> r2:nat -> r3:nat -> r4:nat -> Lemma
  ( r0 * r0 + r0 * (pow2 51 * r1) + r0 * (pow2 102 * r2) + r0 * (pow2 153 * r3) + r0 * (pow2 204 * r4)
    =
    r0 * r0 + pow2 51 * r0 * r1 + pow2 102 * r0 * r2 + pow2 153 * r0 * r3 + pow2 204 * r0 * r4)
let lemma_fsquare_spec_2_2_0 r0 r1 r2 r3 r4 =
  lemma_aux_1 r0 (pow2 51)  r1;
  lemma_aux_1 r0 (pow2 102) r2;
  lemma_aux_1 r0 (pow2 153) r3;
  lemma_aux_1 r0 (pow2 204) r4


#reset-options "--z3rlimit 10"

val lemma_fsquare_spec_2_2_1: r0:nat -> r1:nat -> r2:nat -> r3:nat -> r4:nat -> Lemma
  ( (pow2 51 * r1) * r0 + (pow2 51 * r1) * (pow2 51 * r1) + (pow2 51 * r1) * (pow2 102 * r2) + (pow2 51 * r1) * (pow2 153 * r3) + (pow2 51 * r1) * (pow2 204 * r4)
    =
  pow2 51 * r1 * r0 + pow2 102 * r1 * r1 + pow2 153 * r1 * r2 + pow2 204 * r1 * r3 + pow2 255 * r1 * r4)
let lemma_fsquare_spec_2_2_1 r0 r1 r2 r3 r4 =
  lemma_aux_3 (pow2 51) r1 r0;
  lemma_aux_2 r1 (pow2 51) r1 (pow2 51);
  lemma_aux_2 r1 (pow2 51) r2 (pow2 102);
  lemma_aux_2 r1 (pow2 51) r3 (pow2 153);
  lemma_aux_2 r1 (pow2 51) r4 (pow2 204);
  Math.Lemmas.pow2_plus 51 51;
  Math.Lemmas.pow2_plus 102 51;
  Math.Lemmas.pow2_plus 153 51;
  Math.Lemmas.pow2_plus 204 51


val lemma_fsquare_spec_2_2_2: r0:nat -> r1:nat -> r2:nat -> r3:nat -> r4:nat -> Lemma
  ( (pow2 102 * r2) * r0 + (pow2 102 * r2) * (pow2 51 * r1) + (pow2 102 * r2) * (pow2 102 * r2) + (pow2 102 * r2) * (pow2 153 * r3) + (pow2 102 * r2) * (pow2 204 * r4)
    =
   pow2 102 * r2 * r0 + pow2 153 * r2 * r1 + pow2 204 * r2 * r2 + pow2 255 * r2 * r3 + pow2 306 * r2 * r4)
let lemma_fsquare_spec_2_2_2 r0 r1 r2 r3 r4 =
  lemma_aux_3 (pow2 102) r2 r0;
  lemma_aux_2 r2 (pow2 102) r1 (pow2 51);
  lemma_aux_2 r2 (pow2 102) r2 (pow2 102);
  lemma_aux_2 r2 (pow2 102) r3 (pow2 153);
  lemma_aux_2 r2 (pow2 102) r4 (pow2 204);
  Math.Lemmas.pow2_plus 102 51;
  Math.Lemmas.pow2_plus 102 102;
  Math.Lemmas.pow2_plus 102 153;
  Math.Lemmas.pow2_plus 102 204

val lemma_fsquare_spec_2_2_3: r0:nat -> r1:nat -> r2:nat -> r3:nat -> r4:nat -> Lemma
  ( (pow2 153 * r3) * r0 + (pow2 153 * r3) * (pow2 51 * r1) + (pow2 153 * r3) * (pow2 102 * r2) + (pow2 153 * r3) * (pow2 153 * r3) + (pow2 153 * r3) * (pow2 204 * r4)
  = pow2 153 * r3 * r0 + pow2 204 * r3 * r1 + pow2 255 * r3 * r2 + pow2 306 * r3 * r3 + pow2 357 * r3 * r4)
let lemma_fsquare_spec_2_2_3 r0 r1 r2 r3 r4 =
  lemma_aux_3 (pow2 153) r3 r0;
  lemma_aux_2 r3 (pow2 153) r1 (pow2 51);
  lemma_aux_2 r3 (pow2 153) r2 (pow2 102);
  lemma_aux_2 r3 (pow2 153) r3 (pow2 153);
  lemma_aux_2 r3 (pow2 153) r4 (pow2 204);
  Math.Lemmas.pow2_plus 153 51;
  Math.Lemmas.pow2_plus 153 102;
  Math.Lemmas.pow2_plus 153 153;
  Math.Lemmas.pow2_plus 153 204

val lemma_fsquare_spec_2_2_4: r0:nat -> r1:nat -> r2:nat -> r3:nat -> r4:nat -> Lemma
  ((pow2 204 * r4) * r0 + (pow2 204 * r4) * (pow2 51 * r1) + (pow2 204 * r4) * (pow2 102 * r2) + (pow2 204 * r4) * (pow2 153 * r3) + (pow2 204 * r4) * (pow2 204 * r4)  = pow2 204 * r4 * r0 + pow2 255 * r4 * r1 + pow2 306 * r4 * r2 + pow2 357 * r4 * r3 + pow2 408 * r4 * r4)
let lemma_fsquare_spec_2_2_4 r0 r1 r2 r3 r4 =
  lemma_aux_3 (pow2 204) r4 r0;
  lemma_aux_2 r4 (pow2 204) r1 (pow2 51);
  lemma_aux_2 r4 (pow2 204) r2 (pow2 102);
  lemma_aux_2 r4 (pow2 204) r3 (pow2 153);
  lemma_aux_2 r4 (pow2 204) r4 (pow2 204);
  Math.Lemmas.pow2_plus 204 51;
  Math.Lemmas.pow2_plus 204 102;
  Math.Lemmas.pow2_plus 204 153;
  Math.Lemmas.pow2_plus 204 204


val lemma_fsquare_spec_2_2: r0:nat -> r1:nat -> r2:nat -> r3:nat -> r4:nat -> Lemma
  (  r0 * r0 + r0 * (pow2 51 * r1) + r0 * (pow2 102 * r2) + r0 * (pow2 153 * r3) + r0 * (pow2 204 * r4)
  + (pow2 51 * r1) * r0 + (pow2 51 * r1) * (pow2 51 * r1) + (pow2 51 * r1) * (pow2 102 * r2) + (pow2 51 * r1) * (pow2 153 * r3) + (pow2 51 * r1) * (pow2 204 * r4)
  + (pow2 102 * r2) * r0 + (pow2 102 * r2) * (pow2 51 * r1) + (pow2 102 * r2) * (pow2 102 * r2) + (pow2 102 * r2) * (pow2 153 * r3) + (pow2 102 * r2) * (pow2 204 * r4)
  + (pow2 153 * r3) * r0 + (pow2 153 * r3) * (pow2 51 * r1) + (pow2 153 * r3) * (pow2 102 * r2) + (pow2 153 * r3) * (pow2 153 * r3) + (pow2 153 * r3) * (pow2 204 * r4)
  + (pow2 204 * r4) * r0 + (pow2 204 * r4) * (pow2 51 * r1) + (pow2 204 * r4) * (pow2 102 * r2) + (pow2 204 * r4) * (pow2 153 * r3) + (pow2 204 * r4) * (pow2 204 * r4)
    =
    r0 * r0 + pow2 51 * r0 * r1 + pow2 102 * r0 * r2 + pow2 153 * r0 * r3 + pow2 204 * r0 * r4
  + pow2 51 * r1 * r0 + pow2 102 * r1 * r1 + pow2 153 * r1 * r2 + pow2 204 * r1 * r3 + pow2 255 * r1 * r4
  + pow2 102 * r2 * r0 + pow2 153 * r2 * r1 + pow2 204 * r2 * r2 + pow2 255 * r2 * r3 + pow2 306 * r2 * r4
  + pow2 153 * r3 * r0 + pow2 204 * r3 * r1 + pow2 255 * r3 * r2 + pow2 306 * r3 * r3 + pow2 357 * r3 * r4
  + pow2 204 * r4 * r0 + pow2 255 * r4 * r1 + pow2 306 * r4 * r2 + pow2 357 * r4 * r3 + pow2 408 * r4 * r4)
let lemma_fsquare_spec_2_2 r0 r1 r2 r3 r4 =
  lemma_fsquare_spec_2_2_0 r0 r1 r2 r3 r4;
  lemma_fsquare_spec_2_2_1 r0 r1 r2 r3 r4;
  lemma_fsquare_spec_2_2_2 r0 r1 r2 r3 r4;
  lemma_fsquare_spec_2_2_3 r0 r1 r2 r3 r4;
  lemma_fsquare_spec_2_2_4 r0 r1 r2 r3 r4


#set-options "--z3rlimit 10"

val lemma_fsquare_spec_2: s:seqelem -> Lemma
  (let r0 = v (Seq.index s 0) in
  let r1 = v (Seq.index s 1) in
  let r2 = v (Seq.index s 2) in
  let r3 = v (Seq.index s 3) in
  let r4 = v (Seq.index s 4) in
  (seval s * seval s = r0 * r0 + pow2 51 * r0 * r1 + pow2 102 * r0 * r2 + pow2 153 * r0 * r3 + pow2 204 * r0 * r4
  + pow2 51 * r1 * r0 + pow2 102 * r1 * r1 + pow2 153 * r1 * r2 + pow2 204 * r1 * r3 + pow2 255 * r1 * r4
  + pow2 102 * r2 * r0 + pow2 153 * r2 * r1 + pow2 204 * r2 * r2 + pow2 255 * r2 * r3 + pow2 306 * r2 * r4
  + pow2 153 * r3 * r0 + pow2 204 * r3 * r1 + pow2 255 * r3 * r2 + pow2 306 * r3 * r3 + pow2 357 * r3 * r4
  + pow2 204 * r4 * r0 + pow2 255 * r4 * r1 + pow2 306 * r4 * r2 + pow2 357 * r4 * r3 + pow2 408 * r4 * r4))
let lemma_fsquare_spec_2 s =
  lemma_seval_5 s;
  let r0 = v (Seq.index s 0) in
  let r1 = v (Seq.index s 1) in
  let r2 = v (Seq.index s 2) in
  let r3 = v (Seq.index s 3) in
  let r4 = v (Seq.index s 4) in
  lemma_mul_5 r0 (pow2 51 * r1) (pow2 102 * r2) (pow2 153 * r3) (pow2 204 * r4);
  lemma_fsquare_spec_2_2 r0 r1 r2 r3 r4


private let lemma_distr_2 x a b : Lemma ( x * (a + b) = x * a + x * b) = ()
private let lemma_distr_3 x a b c  : Lemma ( x * (a + b + c) = x * a + x * b + x * c) = ()
private let lemma_distr_4 x a b c d : Lemma ( x * (a + b + c + d) = x * a + x * b + x * c + x * d) = ()
private let lemma_distr_5 x a b c d e : Lemma ( x * (a + b + c + d + e) = x * a + x * b + x * c + x * d + x * e) = ()

private let lemma_mul_paren a b c : Lemma ( a * b * c = a * (b * c) ) = ()


#reset-options "--z3rlimit 100 --initial_fuel 0 --initial_ifuel 0"

val lemma_fsquare_spec_3_1: r0:nat -> r1:nat -> r2:nat -> r3:nat -> r4:nat -> Lemma
  (r0 * r0 + pow2 51 * r0 * r1 + pow2 102 * r0 * r2 + pow2 153 * r0 * r3 + pow2 204 * r0 * r4
  + pow2 51 * r1 * r0 + pow2 102 * r1 * r1 + pow2 153 * r1 * r2 + pow2 204 * r1 * r3 + pow2 255 * r1 * r4
  + pow2 102 * r2 * r0 + pow2 153 * r2 * r1 + pow2 204 * r2 * r2 + pow2 255 * r2 * r3 + pow2 306 * r2 * r4
  + pow2 153 * r3 * r0 + pow2 204 * r3 * r1 + pow2 255 * r3 * r2 + pow2 306 * r3 * r3 + pow2 357 * r3 * r4
  + pow2 204 * r4 * r0 + pow2 255 * r4 * r1 + pow2 306 * r4 * r2 + pow2 357 * r4 * r3 + pow2 408 * r4 * r4
  = r0 * r0 + pow2 51 * (r0 * r1 + r1 * r0) + pow2 102 * (r0 * r2 + r1 * r1 + r2 * r0) + pow2 153 * (r0 * r3 + r1 * r2 + r2 * r1 + r3 * r0) + pow2 204 * (r0 * r4 + r1 * r3 + r2 * r2 + r3 * r1 + r4 * r0) + pow2 255 * (r1 * r4 + r2 * r3 + r3 * r2 + r4 * r1) + pow2 306 * (r2 * r4 + r3 * r3 + r4 * r2) + pow2 357 * (r3 * r4 + r4 * r3) + pow2 408 * r4 * r4)
let lemma_fsquare_spec_3_1 r0 r1 r2 r3 r4 =
  lemma_mul_paren (pow2 51) r0 r1;
  lemma_mul_paren (pow2 51) r1 r0;
  lemma_mul_paren (pow2 102) r0 r2;
  lemma_mul_paren (pow2 102) r1 r1;
  lemma_mul_paren (pow2 102) r2 r0;
  lemma_mul_paren (pow2 153) r0 r3;
  lemma_mul_paren (pow2 153) r1 r2;
  lemma_mul_paren (pow2 153) r2 r1;
  lemma_mul_paren (pow2 153) r3 r0;
  lemma_mul_paren (pow2 204) r0 r4;
  lemma_mul_paren (pow2 204) r1 r3;
  lemma_mul_paren (pow2 204) r2 r2;
  lemma_mul_paren (pow2 204) r3 r1;
  lemma_mul_paren (pow2 204) r4 r0;
  lemma_mul_paren (pow2 255) r1 r4;
  lemma_mul_paren (pow2 255) r2 r3;
  lemma_mul_paren (pow2 255) r3 r2;
  lemma_mul_paren (pow2 255) r4 r1;
  lemma_mul_paren (pow2 306) r2 r4;
  lemma_mul_paren (pow2 306) r3 r3;
  lemma_mul_paren (pow2 306) r4 r2;
  lemma_mul_paren (pow2 357) r3 r4;
  lemma_mul_paren (pow2 357) r4 r3;
  lemma_mul_paren (pow2 408) r4 r4;
  lemma_distr_2 (pow2 51)  (r0 * r1) (r1 * r0);
  lemma_distr_2 (pow2 357) (r3 * r4) (r4 * r3);
  lemma_distr_3 (pow2 102) (r0 * r2) (r1 * r1) (r2 * r0);
  lemma_distr_3 (pow2 306) (r2 * r4) (r3 * r3) (r4 * r2);
  lemma_distr_4 (pow2 153) (r0 * r3) (r1 * r2) (r2 * r1) (r3 * r0);
  lemma_distr_4 (pow2 255) (r1 * r4) (r2 * r3) (r3 * r2) (r4 * r1);
  lemma_distr_5 (pow2 204) (r0 * r4) (r1 * r3) (r2 * r2) (r3 * r1) (r4 * r0)


#set-options "--z3rlimit 10 --initial_fuel 0 --max_fuel 0"

val lemma_fsquare_spec_3: s:seqelem -> Lemma
  (let r0 = v (Seq.index s 0) in
  let r1 = v (Seq.index s 1) in
  let r2 = v (Seq.index s 2) in
  let r3 = v (Seq.index s 3) in
  let r4 = v (Seq.index s 4) in
  (r0 * r0 + pow2 51 * r0 * r1 + pow2 102 * r0 * r2 + pow2 153 * r0 * r3 + pow2 204 * r0 * r4
  + pow2 51 * r1 * r0 + pow2 102 * r1 * r1 + pow2 153 * r1 * r2 + pow2 204 * r1 * r3 + pow2 255 * r1 * r4
  + pow2 102 * r2 * r0 + pow2 153 * r2 * r1 + pow2 204 * r2 * r2 + pow2 255 * r2 * r3 + pow2 306 * r2 * r4
  + pow2 153 * r3 * r0 + pow2 204 * r3 * r1 + pow2 255 * r3 * r2 + pow2 306 * r3 * r3 + pow2 357 * r3 * r4
  + pow2 204 * r4 * r0 + pow2 255 * r4 * r1 + pow2 306 * r4 * r2 + pow2 357 * r4 * r3 + pow2 408 * r4 * r4
  = r0 * r0 + pow2 51 * (r0 * r1 + r1 * r0) + pow2 102 * (r0 * r2 + r1 * r1 + r2 * r0) + pow2 153 * (r0 * r3 + r1 * r2 + r2 * r1 + r3 * r0) + pow2 204 * (r0 * r4 + r1 * r3 + r2 * r2 + r3 * r1 + r4 * r0) + pow2 255 * (r1 * r4 + r2 * r3 + r3 * r2 + r4 * r1) + pow2 306 * (r2 * r4 + r3 * r3 + r4 * r2) + pow2 357 * (r3 * r4 + r4 * r3) + pow2 408 * r4 * r4))
let lemma_fsquare_spec_3 s =
  let r0 = v (Seq.index s 0) in
  let r1 = v (Seq.index s 1) in
  let r2 = v (Seq.index s 2) in
  let r3 = v (Seq.index s 3) in
  let r4 = v (Seq.index s 4) in
  lemma_fsquare_spec_3_1 r0 r1 r2 r3 r4


let lemma_mul_symm a b : Lemma (a * b + b * a = 2 * a * b) = ()


#reset-options "--z3rlimit 689 --initial_fuel 0 --max_fuel 0 --smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr wrapped"

val lemma_fsquare_spec_4: s:seqelem -> Lemma
  (let r0 = v (Seq.index s 0) in
  let r1 = v (Seq.index s 1) in
  let r2 = v (Seq.index s 2) in
  let r3 = v (Seq.index s 3) in
  let r4 = v (Seq.index s 4) in
  (r0 * r0 
   + pow2 51 * (r0 * r1 + r1 * r0) 
   + pow2 102 * (r0 * r2 + r1 * r1 + r2 * r0) 
   + pow2 153 * (r0 * r3 + r1 * r2 + r2 * r1 + r3 * r0) 
   + pow2 204 * (r0 * r4 + r1 * r3 + r2 * r2 + r3 * r1 + r4 * r0) 
   + pow2 255 * (r1 * r4 + r2 * r3 + r3 * r2 + r4 * r1) 
   + pow2 306 * (r2 * r4 + r3 * r3 + r4 * r2) 
   + pow2 357 * (r3 * r4 + r4 * r3) 
   + pow2 408 * r4 * r4
  = r0 * r0 
    + pow2 51 * 2 * r0 * r1 
    + pow2 102 * (2 * r0 * r2 + r1 * r1) 
    + pow2 153 * (2 * r0 * r3 + 2 * r1 * r2) 
    + pow2 204 * (2 * r0 * r4 + 2 * r1 * r3 + r2 * r2)
    + pow2 255 * (2 * r1 * r4 + 2 * r2 * r3) 
    + pow2 306 * (2 * r2 * r4 + r3 * r3) 
    + pow2 357 * 2 * r3 * r4 
    + pow2 408 * r4 * r4))
let lemma_fsquare_spec_4 s = ()

#reset-options "--z3rlimit 10"

val lemma_sum_mod_0: a:nat -> b:nat -> c:nat -> Lemma ( (a + b * c) % prime = (a + ((b % prime) * c)) % prime)
let lemma_sum_mod_0 a b c =
  Math.Lemmas.lemma_mod_plus_distr_l (b * c) a prime;
  Math.Lemmas.lemma_mod_mul_distr_l b c prime;
  Math.Lemmas.lemma_mod_plus_distr_l ((b % prime) * c) a prime


#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val lemma_sum_mod: a:nat -> b:nat -> c:nat -> d:nat -> e:nat -> Lemma
  ((a + pow2 255 * b + pow2 306 * c + pow2 357 * d + pow2 408 * e) % prime
    = (a + 19 * b + pow2 51 * 19 * c + pow2 102 * 19 * d + pow2 153 * 19 * e) % prime)
let lemma_sum_mod a b c d e =
  let z = (a + pow2 255 * b + pow2 306 * c + pow2 357 * d + pow2 408 * e) % prime in
  assert_norm (pow2 408 % (pow2 255 - 19) = 19 * pow2 153);
  assert_norm (pow2 357 % (pow2 255 - 19) = 19 * pow2 102);
  assert_norm (pow2 306 % (pow2 255 - 19) = 19 * pow2 51);
  assert_norm (pow2 255 % (pow2 255 - 19) = 19);
  Math.Lemmas.nat_times_nat_is_nat 19 (pow2 51);
  Math.Lemmas.nat_times_nat_is_nat 19 (pow2 102);
  Math.Lemmas.nat_times_nat_is_nat 19 (pow2 153);
  Math.Lemmas.nat_times_nat_is_nat (19*pow2 153) e;
  Math.Lemmas.nat_times_nat_is_nat (19*pow2 102) d;
  Math.Lemmas.nat_times_nat_is_nat (19*pow2 51) c;
  Math.Lemmas.nat_times_nat_is_nat (19) b;
  lemma_sum_mod_0 (a + pow2 255 * b + pow2 306 * c + pow2 357 * d) (pow2 408) e;
  lemma_sum_mod_0 (a + pow2 255 * b + pow2 306 * c + (19 * pow2 153) * e) (pow2 357) d;
  lemma_sum_mod_0 (a + pow2 255 * b + (19 * pow2 102) * d + (19 * pow2 153) * e) (pow2 306) c;
  lemma_sum_mod_0 (a + (19 * pow2 51) * c + (19 * pow2 102) * d + (19 * pow2 153) * e) (pow2 255) b


#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0"

val lemma_fsquare_spec_5_1: r0:nat -> r1:nat -> r2:nat -> r3:nat -> r4:nat -> Lemma
  ((r0 * r0
    + pow2 51 * (2 * r0 * r1)
    + pow2 102 * (2 * r0 * r2 + r1 * r1)
    + pow2 153 * (2 * r0 * r3 + 2 * r1 * r2)
    + pow2 204 * (2 * r0 * r4 + 2 * r1 * r3 + r2 * r2)
    + pow2 255 * (2 * r1 * r4 + 2 * r2 * r3)
    + pow2 306 * (2 * r2 * r4 + r3 * r3)
    + pow2 357 * (2 * r3 * r4)
    + pow2 408 * (r4 * r4)) % prime
   = (r0 * r0
    + pow2 51 * 2 * r0 * r1
    + pow2 102 * (2 * r0 * r2 + r1 * r1)
    + pow2 153 * (2 * r0 * r3 + 2 * r1 * r2)
    + pow2 204 * (2 * r0 * r4 + 2 * r1 * r3 + r2 * r2)
    + 19 * (2 * r1 * r4 + 2 * r2 * r3)
    + pow2 51 * 19 * (2 * r2 * r4 + r3 * r3)
    + pow2 102 * 19 * (2 * r3 * r4)
    + pow2 153 * 19 * (r4 * r4)) % prime)
let lemma_fsquare_spec_5_1 r0 r1 r2 r3 r4 =
  Math.Lemmas.nat_times_nat_is_nat r0 r0;  Math.Lemmas.nat_times_nat_is_nat r0 r1;
  Math.Lemmas.nat_times_nat_is_nat r0 r2;  Math.Lemmas.nat_times_nat_is_nat r0 r3;
  Math.Lemmas.nat_times_nat_is_nat r0 r4;  Math.Lemmas.nat_times_nat_is_nat r1 r1;
  Math.Lemmas.nat_times_nat_is_nat r1 r2;  Math.Lemmas.nat_times_nat_is_nat r1 r3;
  Math.Lemmas.nat_times_nat_is_nat r1 r4;  Math.Lemmas.nat_times_nat_is_nat r2 r2;
  Math.Lemmas.nat_times_nat_is_nat r2 r3;  Math.Lemmas.nat_times_nat_is_nat r2 r4;
  Math.Lemmas.nat_times_nat_is_nat r3 r3;  Math.Lemmas.nat_times_nat_is_nat r3 r4;
  Math.Lemmas.nat_times_nat_is_nat r4 r4;
  Math.Lemmas.nat_times_nat_is_nat (pow2 51) (2 * r0 * r1);
  Math.Lemmas.nat_times_nat_is_nat (pow2 102) (2 * r0 * r2 + r1 * r1);
  Math.Lemmas.nat_times_nat_is_nat (pow2 153) (2 * r0 * r3 + 2 * r1 * r2);
  Math.Lemmas.nat_times_nat_is_nat (pow2 204) (2 * r0 * r4 + 2 * r1 * r3 + r2 * r2);
  let a = (r0 * r0 + pow2 51 * 2 * r0 * r1 + pow2 102 * (2 * r0 * r2 + r1 * r1) + pow2 153 * (2 * r0 * r3 + 2 * r1 * r2) + pow2 204 * (2 * r0 * r4 + 2 * r1 * r3 + r2 * r2)) in
  let b = (2 * r1 * r4 + 2 * r2 * r3) in
  let c = (2 * r2 * r4 + r3 * r3) in
  let d = (2 * r3 * r4) in 
  let e = (r4 * r4) in
  lemma_sum_mod a b c d e


let lemma_mul_paren2 a b c d : Lemma (a * b * (c * d) = a * (b * c * d)) = ()
let lemma_mul_paren3 a b c d e : Lemma (a * b * (c * d * e) = a * (b * c * d * e)) = ()
let lemma_mul_paren4 a b c : Lemma (a * b * c = a * (b * c)) = ()


#reset-options "--z3rlimit 10 --initial_fuel 0 --max_fuel 0"

val lemma_fsquare_spec_5_2_1: r0:nat -> r1:nat -> r2:nat -> r3:nat -> r4:nat -> Lemma
  (r0 * r0 + 19 * 2 * r4 * r1  + 19 * 2 * r2 * r3
   = (r0 * r0
    + 19 * (2 * r1 * r4 + 2 * r2 * r3)))
let lemma_fsquare_spec_5_2_1 r0 r1 r2 r3 r4 =
  Math.Lemmas.distributivity_add_right 19 (2 * r1 * r4) (2 * r2 * r3)


val lemma_fsquare_spec_5_2_2: r0:nat -> r1:nat -> r2:nat -> r3:nat -> r4:nat -> Lemma
  (pow2 51 * (2 * r0 * r1  + 19 * 2 * r4 * r2  + 19 * r3 * r3)
   = (pow2 51 * 2 * r0 * r1 + pow2 51 * 19 * (2 * r2 * r4 + r3 * r3)))
let lemma_fsquare_spec_5_2_2 r0 r1 r2 r3 r4 =
  Math.Lemmas.distributivity_add_right (pow2 51) (2 * r2 * r4) (r3 * r3)

val lemma_fsquare_spec_5_2_3: r0:nat -> r1:nat -> r2:nat -> r3:nat -> r4:nat -> Lemma
  (pow2 102 * (2 * r0 * r2  + r1 * r1           + 19 * 2 * r4 * r3)
   =  pow2 102 * (2 * r0 * r2 + r1 * r1) + pow2 102 * 19 * (2 * r3 * r4))
let lemma_fsquare_spec_5_2_3 r0 r1 r2 r3 r4 = ()

val lemma_fsquare_spec_5_2_4: r0:nat -> r1:nat -> r2:nat -> r3:nat -> r4:nat -> Lemma
  (pow2 153 * (2 * r0 * r3  + 2 * r1 * r2       + 19 * r4 * r4)
   = pow2 153 * (2 * r0 * r3 + 2 * r1 * r2) + pow2 153 * 19 * (r4 * r4))
let lemma_fsquare_spec_5_2_4 r0 r1 r2 r3 r4 = ()

val lemma_fsquare_spec_5_2: r0:nat -> r1:nat -> r2:nat -> r3:nat -> r4:nat -> Lemma
  ((r0 * r0 + 19 * 2 * r4 * r1  + 19 * 2 * r2 * r3
     + pow2 51 * (2 * r0 * r1  + 19 * 2 * r4 * r2  + 19 * r3 * r3)
     + pow2 102 * (2 * r0 * r2  + r1 * r1           + 19 * 2 * r4 * r3)
     + pow2 153 * (2 * r0 * r3  + 2 * r1 * r2       + 19 * r4 * r4)
     + pow2 204 * (2 * r0 * r4  + 2 * r1 * r3       + r2 * r2))
   = (r0 * r0
    + pow2 51 * 2 * r0 * r1
    + pow2 102 * (2 * r0 * r2 + r1 * r1)
    + pow2 153 * (2 * r0 * r3 + 2 * r1 * r2)
    + pow2 204 * (2 * r0 * r4 + 2 * r1 * r3 + r2 * r2)
    + 19 * (2 * r1 * r4 + 2 * r2 * r3)
    + pow2 51 * 19 * (2 * r2 * r4 + r3 * r3)
    + pow2 102 * 19 * (2 * r3 * r4)
    + pow2 153 * 19 * (r4 * r4)))
let lemma_fsquare_spec_5_2 r0 r1 r2 r3 r4 =
  lemma_fsquare_spec_5_2_1 r0 r1 r2 r3 r4;
  lemma_fsquare_spec_5_2_2 r0 r1 r2 r3 r4;
  lemma_fsquare_spec_5_2_3 r0 r1 r2 r3 r4;
  lemma_fsquare_spec_5_2_4 r0 r1 r2 r3 r4


#reset-options "--max_fuel 0 --z3rlimit 400"

val lemma_fsquare_spec_5_0: r0:nat -> r1:nat -> r2:nat -> r3:nat -> r4:nat -> Lemma
  ((r0 * r0
    + pow2 51 * 2 * r0 * r1
    + pow2 102 * (2 * r0 * r2 + r1 * r1)
    + pow2 153 * (2 * r0 * r3 + 2 * r1 * r2)
    + pow2 204 * (2 * r0 * r4 + 2 * r1 * r3 + r2 * r2)
    + pow2 255 * (2 * r1 * r4 + 2 * r2 * r3)
    + pow2 306 * (2 * r2 * r4 + r3 * r3)
    + pow2 357 * 2 * r3 * r4
    + pow2 408 * r4 * r4) % prime
   = (r0 * r0      + 2 * 19 * r4 * r1  + 2 * 19 * r2 * r3
    + pow2 51 * (2 * r0 * r1  + 2 * 19 * r4 * r2  + 19 * r3 * r3)
    + pow2 102 * (2 * r0 * r2  + r1 * r1           + 2 * 19 * r4 * r3)
    + pow2 153 * (2 * r0 * r3  + 2 * r1 * r2       + 19 * r4 * r4)
    + pow2 204 * (2 * r0 * r4  + 2 * r1 * r3       + r2 * r2)) % prime)
let lemma_fsquare_spec_5_0 r0 r1 r2 r3 r4 =
  lemma_fsquare_spec_5_1 r0 r1 r2 r3 r4;
  lemma_fsquare_spec_5_2 r0 r1 r2 r3 r4


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 1000"

val lemma_fsquare_spec_1: s:seqelem -> Lemma
  (let r0 = v (Seq.index s 0) in
  let r1 = v (Seq.index s 1) in
  let r2 = v (Seq.index s 2) in
  let r3 = v (Seq.index s 3) in
  let r4 = v (Seq.index s 4) in
  (seval s * seval s) % prime = (r0 * r0      + 2 * 19 * r4 * r1  + 2 * 19 * r2 * r3
  + pow2 51 * (2 * r0 * r1  + 2 * 19 * r4 * r2  + 19 * r3 * r3)
  + pow2 102 * (2 * r0 * r2  + r1 * r1           + 2 * 19 * r4 * r3)
  + pow2 153 * (2 * r0 * r3  + 2 * r1 * r2       + 19 * r4 * r4)
  + pow2 204 * (2 * r0 * r4  + 2 * r1 * r3       + r2 * r2)) % prime)  
let lemma_fsquare_spec_1 s =
  let r0 = v (Seq.index s 0) in
  let r1 = v (Seq.index s 1) in
  let r2 = v (Seq.index s 2) in
  let r3 = v (Seq.index s 3) in
  let r4 = v (Seq.index s 4) in
  lemma_fsquare_spec_2 s;
  lemma_fsquare_spec_3 s;
  lemma_fsquare_spec_4 s;
  lemma_fsquare_spec_5_0 r0 r1 r2 r3 r4


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

val lemma_fsquare_spec_: s:seqelem{fsquare_pre_ s} -> Lemma (
  let s' = fsquare_spec_ s in
  seval_wide (fsquare_spec_ s) % prime = (seval s * seval s) % prime)
let lemma_fsquare_spec_ s =
  lemma_seval_5 s;
  let s' = fsquare_spec_ s in
  lemma_seval_wide_5 s';
  lemma_fsquare_spec_1 s;
  ()


#set-options "--z3rlimit 10 --initial_fuel 0 --max_fuel 0"

val fsquare_pre: s:seqelem -> GTot Type0
let fsquare_pre s =
  let _ = () in
  fsquare_pre_ s
  /\ carry_wide_pre (fsquare_spec_ s) 0
  /\ carry_top_wide_pre (carry_wide_spec (fsquare_spec_ s))
  /\ copy_from_wide_pre (carry_top_wide_spec (carry_wide_spec (fsquare_spec_ s)))
  /\ carry_0_to_1_pre (copy_from_wide_spec (carry_top_wide_spec (carry_wide_spec (fsquare_spec_ s))))

val fsquare_spec: s:seqelem{fsquare_pre s} ->
  Tot (s':seqelem{selem s' = selem s *@ selem s})
let fsquare_spec s =
  lemma_fsquare_spec_ s;
  let output1 = fsquare_spec_ s in
  cut (seval_wide output1 % prime = (seval s * seval s) % prime);
  let output2 = carry_wide_spec output1 in
  lemma_carry_top_wide_spec output2;
  let output3 = carry_top_wide_spec output2 in
  lemma_copy_from_wide output3;
  let output4 = copy_from_wide_spec output3 in
  let output5 = carry_0_to_1_spec output4 in
  Math.Lemmas.lemma_mod_mul_distr_l (seval s) (seval s) prime;
  Math.Lemmas.lemma_mod_mul_distr_l (seval s) (selem s) prime;
  output5


#set-options "--z3rlimit 5 --initial_fuel 0 --max_fuel 0"

inline_for_extraction let p104 : p:pos{p = 0x100000000000000000000000000} = assert_norm (pow2 104 = 0x100000000000000000000000000); pow2 104

let lemma_mul_ineq (a:nat) (b:nat) (c:nat{a < c}) (d:nat{b < d}) : Lemma (a * b < c * d) = ()
let lemma_mul_ineq1 (a:pos) (c:nat) (d:nat{c < d}) : Lemma (a * c < a * d) = ()


#reset-options "--z3rlimit 1000 --max_fuel 0 --initial_ifuel 2 --max_ifuel 2"

val lemma_52_to_fsquare_is_fine: s:seqelem{red_52 s} ->
 Lemma (fsquare_pre_ s /\ bounds' (fsquare_spec_ s) (77 * p104) (59 * p104) (41 * p104) (23 * p104) (5 * p104))
let lemma_52_to_fsquare_is_fine s =
  let r0 = v (Seq.index s 0) in let r1 = v (Seq.index s 1) in let r2 = v (Seq.index s 2) in
  let r3 = v (Seq.index s 3) in let r4 = v (Seq.index s 4) in
  let d0 = r0 * 2 in let d1 = r1 * 2 in let d2 = r2 * 2 * 19 in let d3 = r3 * 19 in
  let d419 = r4 * 19 in let d4 = d419 * 2 in
  Math.Lemmas.nat_times_nat_is_nat r0 r0;
  Math.Lemmas.nat_times_nat_is_nat d4 r1;
  Math.Lemmas.nat_times_nat_is_nat r2 r3;
  lemma_mul_ineq r0 r0 p52 p52;
  lemma_mul_ineq d4 r1 (2 * 19 * p52) p52;
  lemma_mul_ineq d2 r3 (2 * 19 * p52) (p52);
  lemma_mul_ineq d0 r1 (2 * p52) p52;
  lemma_mul_ineq d0 r2 (2 * p52) p52;
  lemma_mul_ineq d0 r3 (2 * p52) p52;
  lemma_mul_ineq d0 r4 (2 * p52) p52;
  lemma_mul_ineq d4 r2 (2 * 19 * p52) p52;
  lemma_mul_ineq r3 d3 (p52) (19 * p52);
  lemma_mul_ineq r1 r1 (p52) (p52);
  lemma_mul_ineq d4 r3 (2 * 19 * p52) (p52);
  lemma_mul_ineq d1 r2 (2*p52) (p52);
  lemma_mul_ineq r4 d419 (p52) (19*p52);
  lemma_mul_ineq d1 r3 (2*p52) (p52);
  lemma_mul_ineq r2 r2 (p52) (p52)


#set-options "--z3rlimit 5 --initial_fuel 0 --max_fuel 0"

val lemma_104_smaller_than_108: s:seqelem_wide{bounds' s (77 * p104) (59 * p104) (41 * p104) (23 * p104) (5 * p104)} -> Lemma (bounds' s (77 * p108) (59 * p108) (41 * p108) (23 * p108) (5 * p108))
let lemma_104_smaller_than_108 s = ()


#reset-options "--z3rlimit 1000 --max_fuel 0"

inline_for_extraction let p106 : p:pos{p = 0x400000000000000000000000000} =
  assert_norm(pow2 106 = 0x400000000000000000000000000); pow2 106

val lemma_53_to_fsquare_is_fine: s:seqelem{red_53 s} ->
 Lemma (fsquare_pre_ s /\ bounds' (fsquare_spec_ s) (77 * p106) (59 * p106) (41 * p106) (23 * p106) (5 * p106))
let lemma_53_to_fsquare_is_fine s =
  let r0 = v (Seq.index s 0) in let r1 = v (Seq.index s 1) in let r2 = v (Seq.index s 2) in
  let r3 = v (Seq.index s 3) in let r4 = v (Seq.index s 4) in
  let d0 = r0 * 2 in let d1 = r1 * 2 in let d2 = r2 * 2 * 19 in let d3 = r3 * 19 in
  let d419 = r4 * 19 in let d4 = d419 * 2 in
  Math.Lemmas.nat_times_nat_is_nat r0 r0;
  Math.Lemmas.nat_times_nat_is_nat d4 r1;
  Math.Lemmas.nat_times_nat_is_nat r2 r3;
  lemma_mul_ineq r0 r0 p53 p53;
  lemma_mul_ineq d4 r1 (2 * 19 * p53) p53;
  lemma_mul_ineq d2 r3 (2 * 19 * p53) (p53);
  lemma_mul_ineq d0 r1 (2 * p53) p53;
  lemma_mul_ineq d0 r2 (2 * p53) p53;
  lemma_mul_ineq d0 r3 (2 * p53) p53;
  lemma_mul_ineq d0 r4 (2 * p53) p53;
  lemma_mul_ineq d4 r2 (2 * 19 * p53) p53;
  lemma_mul_ineq r3 d3 (p53) (19 * p53);
  lemma_mul_ineq r1 r1 (p53) (p53);
  lemma_mul_ineq d4 r3 (2 * 19 * p53) (p53);
  lemma_mul_ineq d1 r2 (2*p53) (p53);
  lemma_mul_ineq r4 d419 (p53) (19*p53);
  lemma_mul_ineq d1 r3 (2*p53) (p53);
  lemma_mul_ineq r2 r2 (p53) (p53);
  ()

#set-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val lemma_106_smaller_than_108: s:seqelem_wide{bounds' s (77 * p106) (59 * p106) (41 * p106) (23 * p106) (5 * p106)} -> Lemma (bounds' s (77 * p108) (59 * p108) (41 * p108) (23 * p108) (5 * p108))
let lemma_106_smaller_than_108 s = ()


val fsquare_53_is_fine:
  s1:seqelem{red_53 s1} ->
  Lemma (fsquare_pre s1 /\ red_513 (fsquare_spec s1))
let fsquare_53_is_fine s1 =
  lemma_53_to_fsquare_is_fine s1;
  let o = fsquare_spec_ s1 in
  lemma_106_smaller_than_108 o;
  lemma_53_55_is_fine_to_carry o;
  let o' = carry_wide_spec o in
  lemma_53_55_is_fine_to_carry_top o';
  let o'' = carry_top_wide_spec o' in
  lemma_53_55_is_fine_to_copy o'';
  let o''' = copy_from_wide_spec o'' in
  lemma_53_55_is_fine_to_carry_last o''';
  let o'''' = carry_0_to_1_spec o''' in
  assert_norm(pow2 52 = 0x10000000000000);
  cut (bounds o'''' (p51) (p51+p13) p51 p51 p51);
  cut (o'''' == fsquare_spec s1)


#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 10"


let lemma_52_fits_53 (s:seqelem{red_52 s}) : Lemma (red_53 s) = ()


inline_for_extraction let pmax : p:pos{p = 410718794474278367478258677579776} =
  assert_norm(p5413 * p5413 = 410718794474278367478258677579776); p5413 * p5413

#reset-options "--z3rlimit 1000 --initial_fuel 0 --max_fuel 0"

val lemma_5413_to_fsquare_is_fine: s:seqelem{red_5413 s} ->
 Lemma (fsquare_pre_ s /\ bounds' (fsquare_spec_ s) (77 * pmax) (59 * pmax) (41 * pmax) (23 * pmax) (5 * pmax))
let lemma_5413_to_fsquare_is_fine s =
  let r0 = v (Seq.index s 0) in let r1 = v (Seq.index s 1) in let r2 = v (Seq.index s 2) in
  let r3 = v (Seq.index s 3) in let r4 = v (Seq.index s 4) in
  let d0 = r0 * 2 in let d1 = r1 * 2 in let d2 = r2 * 2 * 19 in let d3 = r3 * 19 in
  let d419 = r4 * 19 in let d4 = d419 * 2 in
  Math.Lemmas.nat_times_nat_is_nat r0 r0;
  Math.Lemmas.nat_times_nat_is_nat d4 r1;
  Math.Lemmas.nat_times_nat_is_nat r2 r3;
  lemma_mul_ineq r0 r0 p5413 p5413;
  lemma_mul_ineq d4 r1 (2 * 19 * p5413) p5413;
  lemma_mul_ineq d2 r3 (2 * 19 * p5413) (p5413);
  lemma_mul_ineq d0 r1 (2 * p5413) p5413;
  lemma_mul_ineq d0 r2 (2 * p5413) p5413;
  lemma_mul_ineq d0 r3 (2 * p5413) p5413;
  lemma_mul_ineq d0 r4 (2 * p5413) p5413;
  lemma_mul_ineq d4 r2 (2 * 19 * p5413) p5413;
  lemma_mul_ineq r3 d3 (p5413) (19 * p5413);
  lemma_mul_ineq r1 r1 (p5413) (p5413);
  lemma_mul_ineq d4 r3 (2 * 19 * p5413) (p5413);
  lemma_mul_ineq d1 r2 (2*p5413) (p5413);
  lemma_mul_ineq r4 d419 (p5413) (19*p5413);
  lemma_mul_ineq d1 r3 (2*p5413) (p5413);
  lemma_mul_ineq r2 r2 (p5413) (p5413);
  ()


#set-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val lemma_5413_is_fine_to_carry:
  s:seqelem_wide{bounds' (s) (77 * pmax) (59 * pmax) (41 * pmax) (23 * pmax) (5 * pmax)} ->
  Lemma (carry_wide_pre s 0 /\ bounds' (carry_wide_spec s) p51 p51 p51 p51 (5*pmax+p77))
let lemma_5413_is_fine_to_carry s =
  assert_norm (pow2 53 = 0x20000000000000);
  assert_norm (pow2 55 = 0x80000000000000);
  assert_norm (pow2 64 = 0x10000000000000000);
  assert_norm (pow2 wide_n = 0x100000000000000000000000000000000);
  assert_norm (pow2 (wide_n-1) = 0x80000000000000000000000000000000);
  lemma_carry_wide_spec_unrolled s


val lemma_5413_is_fine_to_carry_top:
  s:seqelem_wide{bounds' s p51 p51 p51 p51 (5*pmax+p77)} ->
  Lemma (carry_top_wide_pre s /\ bounds' (carry_top_wide_spec s) (p51+19*((5*pmax+p77)/p51)) p51 p51 p51 p51)
let lemma_5413_is_fine_to_carry_top s =
  assert_norm (pow2 64 = 0x10000000000000000);
  assert_norm (pow2 wide_n = 0x100000000000000000000000000000000);
  assert_norm (pow2 (wide_n-1) = 0x80000000000000000000000000000000);
  lemma_carry_wide_then_carry_top s;
  lemma_carry_top_wide_spec_ s


val lemma_5413_is_fine_to_copy:
  s:seqelem_wide{bounds' (s) (p51+19*((5*pmax+p77)/p51)) p51 p51 p51 p51} ->
  Lemma (copy_from_wide_pre s /\ bounds (copy_from_wide_spec s) (p51+19*((5*pmax+p77)/p51)) p51 p51 p51 p51)
let lemma_5413_is_fine_to_copy s =
  assert_norm (pow2 64 = 0x10000000000000000);
  assert_norm (pow2 wide_n = 0x100000000000000000000000000000000);
  assert_norm (pow2 (wide_n-1) = 0x80000000000000000000000000000000)


val lemma_5413_is_fine_to_carry_last:
  s:seqelem{bounds (s) (p51+19*((5*pmax+p77)/p51)) p51 p51 p51 p51} ->
  Lemma (carry_0_to_1_pre s /\ bounds (carry_0_to_1_spec s) (p51) (p51+p13) p51 p51 p51)
let lemma_5413_is_fine_to_carry_last s =
  assert_norm (pow2 64 = 0x10000000000000000);
  assert_norm (pow2 wide_n = 0x100000000000000000000000000000000);
  assert_norm (pow2 (wide_n-1) = 0x80000000000000000000000000000000)


val fsquare_5413_is_fine:
  s1:seqelem{red_5413 s1} ->
  Lemma (fsquare_pre s1 /\ red_513 (fsquare_spec s1))
let fsquare_5413_is_fine s1 =
  lemma_5413_to_fsquare_is_fine s1;
  let o = fsquare_spec_ s1 in
  lemma_5413_is_fine_to_carry o;
  let o' = carry_wide_spec o in
  lemma_5413_is_fine_to_carry_top o';
  let o'' = carry_top_wide_spec o' in
  lemma_5413_is_fine_to_copy o'';
  let o''' = copy_from_wide_spec o'' in
  lemma_5413_is_fine_to_carry_last o''';
  let o'''' = carry_0_to_1_spec o''' in
  cut (bounds o'''' (p51) (p51+p13) p51 p51 p51);
  cut (o'''' == fsquare_spec s1)


(* val exp: x:elem -> n:elem -> Tot elem *)
(* let rec exp x n = if n = 0 then 1 else x * exp x (n-1) *)


val fsquare_times_tot: s:seqelem{red_5413 s} -> n:pos ->
  Tot (s':seqelem{red_513 s'})
  (decreases n)
let rec fsquare_times_tot s n =
  if n = 1 then (fsquare_5413_is_fine s; fsquare_spec s)
  else (cut (n > 1);
    fsquare_5413_is_fine s;
    let s' = fsquare_spec s in
    cut (red_52 s');
    let s'' = fsquare_times_tot s' (n-1) in s'')
