module FastUtil_helpers

open Words_s
open Types_s
open FStar.Mul
open FStar.Tactics
open FStar.Tactics.CanonCommSemiring
open Fast_defs

let int_canon = fun _ -> canon_semiring int_cr //; dump "Final"

let sub_carry (x y:nat64) (c:bit) : nat64 & (c':bit)
  =
  if x - (y + c) < 0 then 
    (x - (y + c) + pow2_64, 1) 
  else
    (x - (y + c)), 0

val lemma_sub_carry_equiv (x y:nat64) (c:bit) : 
  Lemma (let v, c' = sub_carry x y c in
         v == (x - (y + c)) % pow2_64 /\
         c' == bool_bit (x - (y+c) < 0))

val lemma_sub_carry_equiv_forall: unit ->
  Lemma (forall x y c . {:pattern (sub_carry x y c)}
         let v, c' = sub_carry x y c in
         v == (x - (y + c)) % pow2_64 /\
         c' == bool_bit (x - (y+c) < 0))
  
val lemma_sub3
      (a:nat) (a0 a1 a2:nat64)      
      (b:nat) (b0 b1 b2:nat64)
      (s1 s2 s3:nat64) (c:bit) : Lemma
  (requires a = pow2_three a0 a1 a2 /\
            b = pow2_three b0 b1 b2 /\            
           (let s1', c1 = sub_carry a0 b0 0 in
            let s2', c2 = sub_carry a1 b1 c1 in
            let s3', c3 = sub_carry a2 b2 c2 in
            s1 == s1' /\
            s2 == s2' /\
            s3 == s3' /\
            c  == c3))
  (ensures a - b == pow2_three s1 s2 s3 - c * pow2_192)

val lemma_sub
      (a:nat) (a0 a1 a2 a3:nat64)      
      (b:nat) (b0 b1 b2 b3:nat64)
      (s1 s2 s3 s4:nat64) (c:bit) : Lemma
  (requires a = pow2_four a0 a1 a2 a3 /\
            b = pow2_four b0 b1 b2 b3 /\            
           (let s1', c1 = sub_carry a0 b0 0 in
            let s2', c2 = sub_carry a1 b1 c1 in
            let s3', c3 = sub_carry a2 b2 c2 in
            let s4', c4 = sub_carry a3 b3 c3 in
            s1 == s1' /\
            s2 == s2' /\
            s3 == s3' /\
            s4 == s4' /\
            c  == c4))
  (ensures a - b == pow2_four s1 s2 s3 s4 - c * pow2_256)

