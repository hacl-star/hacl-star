module Spec.GaloisField

open FStar.Seq
open FStar.BitVector 
//open Spec.Lib.IntSeq
//open Spec.Lib.IntTypes


(* We represent GF(2^n) with irreducible polynomial x^n + p(x), deg(p) <= n-1	
   by GF n bv where bv is the big-endian bitvector for p(x)   *)
type polynomial (degree:nat) = bv_t (degree + 1)
type field' = | GF: bits:pos -> irred: polynomial (bits - 1) -> field'
let field = field'

let numbits (f:field) = f.bits
let mk_field bits irred = GF bits (UInt.to_vec #bits irred)

type felem (f:field) = bv_t f.bits

let to_felem #f u = UInt.to_vec #f.bits u
let from_felem #f (e:felem f) = UInt.from_vec #f.bits e
let zero #f : felem f = zero_vec #f.bits
let one #f : felem f = elem_vec #f.bits 0

let fadd (#f:field) (a:felem f) (b:felem f) : felem f = logxor_vec #f.bits a b
let op_Plus_At #f e1 e2 = fadd #f e1 e2




(* Properties *)

let add_comm (#f:field) (a:felem f) (b:felem f) = lemma_eq_intro (a +@ b) (b +@ a)

let add_asso (#f:field) (a:felem f) (b:felem f) (c:felem f) = lemma_eq_intro (a +@ b +@ c) (a +@ (b +@ c))

let add_zero (#f:field) (a:felem f) = lemma_eq_intro (a +@ zero) a

let shift_reduce (#f:field) (a:felem f) = 
    if (index a (f.bits-1) = true) then
       fadd (shift_right_vec a 1) f.irred
    else (shift_right_vec a 1)

let cond_fadd (#f:field) (a:felem f) (b:felem f) (c:felem f) (n:nat{n < f.bits}) = 
    if (index b n = true) then fadd c a else c

val cond_fadd_lemma: #f:field -> a:felem f -> b:felem f -> c:felem f -> d:felem f -> n:nat{n < f.bits} -> Lemma
  (requires True)
  (ensures cond_fadd a b c n `fadd` d = c `fadd` cond_fadd a b d n)
let cond_fadd_lemma #f a b c d n = 
    if (index b n = true) then begin
       add_comm #f d a;
       add_asso #f c a d
    end else ()
    

let rec fmul_loop (#f:field) (a:felem f) (b:felem f) (n:nat{n<=f.bits}) 
    : Tot (felem f) (decreases (f.bits - n)) = 
    if n = f.bits then zero #f
    else 
       let n_1 : nat = n + 1 in
       let fmul_n_1 = fmul_loop (shift_reduce #f a) 
       	   	      		b n_1 in
       cond_fadd a b fmul_n_1 n
      
let fmul (#f:field) (a:felem f) (b:felem f) = fmul_loop a b 0
let op_Star_At #f e1 e2 = fmul #f e1 e2

val degree_: #f:field -> a:felem f -> i:nat{i < f.bits} -> Tot nat (decreases i)
let rec degree_ (#f:field) (a:felem f) (i:nat{i < f.bits}) = 
  if i = 0 then 0
  else if index a (f.bits - i - 1) then i
  else degree_ #f a (i-1)

let degree #f a = degree_ #f a (f.bits - 1)

val finv_: #f:field -> s:felem f -> r:felem f -> v:felem f -> u:felem f -> Tot (felem f) (decreases (degree r + degree s))
let rec finv_ (#f:field) (s:felem f) (r:felem f) (v:felem f) (u:felem f) =
  let dr = degree r in
  let ds = degree s in
  if dr = 0 then u else 
  if ds >= dr then
    let s' : felem f = fadd s (shift_left_vec r (ds - dr)) in
    let v' : felem f = fadd v (shift_left_vec u (ds - dr)) in
    finv_ #f s' r  v' u
  else 
    let r' = s in
    let s' = r in
    let v' = u in
    let u' = v in
    let s' = fadd s' (shift_left_vec r' (dr - ds)) in
    let v' = fadd v' (shift_left_vec u' (dr - ds)) in
    finv_ #f s' r' v' u'

let finv (#f:field) (irr: felem f) (a:felem f) =
  if from_felem #f a = 0 then zero else
  let r = a in
  let s = irr in
  let dr = degree r in
  let ds = f.bits in
  let v = zero in
  let u = to_felem #f 1 in
  if dr = 0 then u else 
    let s' = fadd s (shift_left_vec r (ds - dr)) in
    let v' = fadd v (shift_left_vec u (ds - dr)) in
    finv_ #f s' r  v' u

val fexp: #f:field -> a:felem f -> n:nat{n >= 1} -> Tot (felem f) (decreases n)
let rec fexp #f a x = 
  if x = 1 then a else  
  if x = 2 then fmul #f a a else
  let r = fexp #f a (x / 2) in
  let r' = fmul #f r r in
  if (x % 2) = 0  then r' 
  else fmul #f a r'
