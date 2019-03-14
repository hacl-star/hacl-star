module Spec.GaloisField

module ST = FStar.HyperStack.ST

module UInt = FStar.UInt
open FStar.Old.Endianness
open FStar.BitVector 
open FStar.Seq

(* We represent GF(2^n) with irreducible polynomial x^n + p(x), deg(p) <= n-1	
   by GF n bv where bv is the big-endian bitvector for p(x)   *)
type polynomial (degree:nat) = bv_t (degree + 1)
type field = 
     | GF: bits:pos -> irred: polynomial (bits - 1) -> field
let mk_field bits irred = GF bits irred

type felem (f:field) = bv_t f.bits

let to_felem #f (u:UInt.uint_t f.bits) = UInt.to_vec #f.bits u
let from_felem #f (e:felem f) = UInt.from_vec #f.bits e
let zero #f : felem f = zero_vec #f.bits
let one #f : felem f = elem_vec #f.bits 0

let fadd (#f:field) (a:felem f) (b:felem f) : felem f = logxor_vec #f.bits a b
let op_Plus_At #f = fadd #f

val add_comm: #f:field -> a:felem f -> b:felem f -> Lemma (a +@ b == b +@ a)
let add_comm #f a b = lemma_eq_intro (a +@ b) (b +@ a)

val add_asso: #f:field -> a:felem f -> b:felem f -> c:felem f -> Lemma (a +@ b +@ c == a +@ (b +@ c))
let add_asso #f a b c = lemma_eq_intro (a +@ b +@ c) (a +@ (b +@ c))

val add_zero: #f:field -> a:felem f -> b:felem f{b = zero #f} -> Lemma (a +@ b == a)
let add_zero #f a b = lemma_eq_intro (a +@ b) a

let shift_reduce (#f:field) (a:felem f) = 
    if (index a (f.bits - 1) = true) then
       fadd (shift_right_vec a 1) f.irred
    else (shift_right_vec a 1)

let cond_fadd (#f:field) (a:felem f) (b:felem f) (c:felem f) (n:nat{n < f.bits}) = 
    if (index b n = true) then fadd c a else c

val cond_fadd_lemma: #f:field -> a:felem f -> b:felem f -> c:felem f -> d:felem f -> n:nat{n < f.bits} -> Lemma
  (requires True)
  (ensures cond_fadd a b c n +@ d = c +@ cond_fadd a b d n)
let cond_fadd_lemma #f a b c d n =
    if (index b n = true) then begin
       add_comm d a;
       add_asso c a d
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
let op_Star_At #f = fmul #f

(* Test GF8: Wikipedia *)

let irr : polynomial 7 = UInt.to_vec #8 0xd8
let gf8 = mk_field 8 irr

let a = to_felem #gf8 0x53
let b = to_felem #gf8 0xca

let a_plus_b = to_felem #gf8 0x99
let a_times_b = one #gf8

let test() = 
    fadd a b = a_plus_b 
    && fmul a b = a_times_b

