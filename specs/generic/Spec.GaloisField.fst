module Spec.GaloisField

module UInt = FStar.UInt
open FStar.Endianness
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
let zero #f : felem f = to_felem #f 0
let one #f : felem f = to_felem #f 1

let fadd (#f:field) (a:felem f) (b:felem f) : felem f = logxor_vec #f.bits a b
let op_Plus_At e1 e2 = fadd e1 e2

let shift_reduce (#f:field) (a:felem f) = 
    if (index a 0 = true) then
       fadd (shift_left_vec a 1) f.irred
    else (shift_left_vec a 1)

let rec fmul_loop (#f:field) (a:felem f) (b:felem f) (n:nat{n<=f.bits}) 
    : Tot (felem f) (decreases n) = 
    if n = 0 then zero #f
    else 
       let n_1 : nat = n - 1 in
       let fmul_n_1 = fmul_loop (shift_reduce #f a) 
       	   	      		b n_1 in
       if (index b n_1 = true) then 
          fadd a fmul_n_1
       else fmul_n_1
      
let fmul (#f:field) (a:felem f) (b:felem f) = fmul_loop a b f.bits
let op_Star_At e1 e2 = fmul e1 e2

val add_comm: #f:field -> a:felem f -> b:felem f -> Lemma (a +@ b == b +@ a)
let add_comm #f a b = UInt.logxor_commutative (from_felem a) (from_felem b)


(* Test GF8: Wikipedia *)

let irr : polynomial 7 = UInt.to_vec #8 0x1b
let gf8 = mk_field 8 irr

let a = to_felem #gf8 0x53
let b = to_felem #gf8 0xCA

let a_plus_b = to_felem #gf8 0x99
let a_times_b = one #gf8

let test() = 
    fadd a b = a_plus_b 
    && fmul a b = a_times_b

