module Hacl.Impl.K256.Exponent

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Hacl.Impl.P256.Math 

open Lib.IntTypes
open Lib.Buffer

open FStar.Math.Lemmas
open FStar.Mul

open Hacl.Spec.P256.Definition
open Hacl.Lemmas.P256
open Hacl.Impl.P256.LowLevel 
open Spec.ECC
open Lib.Loops

open Hacl.Impl.P256.MM.Lemmas

open Hacl.Impl.EC.MontgomeryMultiplication
open Hacl.Spec.MontgomeryMultiplication


#set-options "--z3rlimit 100 --ifuel 0 --fuel 0"


[@ CInline]
val exponent_k256: a: felem P256 -> result: felem P256 -> tempBuffer: lbuffer uint64 (getCoordinateLenU P256 *. 8ul) -> Stack unit
  (requires fun h -> live h a /\ live h tempBuffer /\ live h result)
  (ensures fun h0 _ h1 -> modifies2 result tempBuffer h0 h1)


let exponent_k256 t result tempBuffer = 
  let h0 = ST.get () in 

  let t0 = sub tempBuffer (size 0) (size 4) in 

  let t1 = sub tempBuffer (size 9) (size 4) in 
  let t2 = sub tempBuffer (size 18) (size 4) in 
  let t3 = sub tempBuffer (size 27) (size 4) in 
  let t4 = sub tempBuffer (size 36) (size 4) in 
  let t5 = sub tempBuffer (size 45) (size 4) in 
  let t6 = sub tempBuffer (size 54) (size 4) in 
  let t7 = sub tempBuffer (size 63) (size 4) in  

(* _10(t0)       = sq(t) *)
	montgomery_square_buffer t t0;
 
  (* _100 (t1)   = sq(_10) *)
  montgomery_square_buffer #P256 t0 t1;

(* _101    = m(t, _100) *)
  montgomery_multiplication_buffer t1 t t1;

(* _111    = m(_10, _101) *)
  montgomery_multiplication_buffer #P256 t1 t0 t0;

(* _1110   = sq(_111) *)
  montgomery_square_buffer #P256 t0 t2;

(* _111000 = n_sq(_1110, 2) *)
  montgomery_square_buffer #P256 t2 t3;
  montgomery_square_buffer #P256 t3 t3;

(* _111111 = m(_111, _111000) *)
  montgomery_multiplication_buffer #P256 t3 t0 t3;

(* i13     = m(n_sq(_111111, 4),  _1110) *)
  fsquarePowN #P256 (size 4) t3;
  montgomery_multiplication_buffer #P256 t3 t2 t2;

(*  t3 is free*)
  (* x12     = m(n_sq(i13, 2), _111) *)
  montgomery_square_buffer #P256 t2 t3;
  montgomery_square_buffer #P256 t3 t3;
  montgomery_multiplication_buffer #P256 t3 t0 t3;

(* x22     = m(m(n_sq(x12, 10), i13), t) *)
  fsquarePowN #P256 (size 10) t3;
  montgomery_multiplication_buffer #P256 t3 t2 t3;
  montgomery_multiplication_buffer #P256 t3 t t3;

(* t2 is free
 i29     = sq(x22) *)
  montgomery_square_buffer #P256 t3 t2;

(* i31     = n_sq(i29, 2) *)
  montgomery_square_buffer #P256 t2 t4;
  montgomery_square_buffer #P256 t4 t4;

(* i54     = m(n_sq(i31, 22), i31) *)
  montgomery_square_buffer #P256 t4 t5;
  fsquarePowN #P256 (size 21) t5;
  montgomery_multiplication_buffer #P256 t5 t4 t4;

(* i0 = m(n_sq(i54, 20), i29) *)
  montgomery_square_buffer #P256 t4 t5;
  fsquarePowN #P256 (size 19) t5;
  montgomery_multiplication_buffer #P256 t5 t2 t2;

(* i122    = m(n_sq(i0, 46), i54) *)
  fsquarePowN #P256 (size 46) t2;
  montgomery_multiplication_buffer #P256 t2 t4 t2;

  (* t4 is free*)
(* x223    = m(m(n_sq(i122, 110), i122), _111) *)
  montgomery_square_buffer #P256 t2 t4;
  fsquarePowN #P256 (size 109) t4;
  montgomery_multiplication_buffer #P256 t4 t2 t4;
  montgomery_multiplication_buffer #P256 t4 t0 t4;

(* i1 = m(n_sq(x223, 23),x22) *)
  fsquarePowN #P256 (size 23) t4;
  montgomery_multiplication_buffer #P256 t4 t3 t4;

(* i269    = n_sq(m(n_sq(i1, 7), _101), 3) *)
  fsquarePowN #P256 (size 7) t4;
  montgomery_multiplication_buffer #P256 t4 t1 t4;
  fsquarePowN #P256 (size 3) t4;

  montgomery_multiplication_buffer t1 t4 result



(* 

prime = 2^256 - 2^32 - 2^9 - 2^8 - 2^7 - 2^6 - 2^4 - 1

def m(x, y):
    return x * y % prime

def sq(x):
    return (power_mod(x, 2, prime))

def n_sq(x, n):
    k = x
    for i in range(n):
        k = sq(k)
    return k

t = getrandbits(520)

_10 (t0)     = sq(t)
_100 (t1)   = sq(_10)
_101 (t1)   = m(t, _100)
_111 (t0)   = m(_10, _101)
_1110 (t2)  = sq(_111)
_111000 (t3) = n_sq(_1110, 2)
_111111 (t3) = m(_111, _111000)
i13 (t2)    = m(n_sq(_111111, 4),  _1110)
x12 (t3)    = m(n_sq(i13, 2), _111)
x22 (t3)    = m(m(n_sq(x12, 10), i13), t)
i29 (t2)    = sq(x22)
i31 (t4)    = n_sq(i29, 2)
i54 (t4)    = m(n_sq(i31, 22), i31)
i0 (t2) = m(n_sq(i54, 20), i29)
i122 (t2)   = m(n_sq(i0, 46), i54)
x223 (t4)   = m(m(n_sq(i122, 110), i122), _111)
i1 (t4) = m(n_sq(x223, 23),x22)
i269 (t4)   = n_sq(m(n_sq(i1, 7), _101), 3)
r = m(   _101, i269)

print(hex(r))
print(hex (power_mod (t, prime - 2, prime)))



addchain: expr: "2^256 - 2^32 - 2^9 - 2^8 - 2^7 - 2^6 - 2^4 - 3"
addchain: hex: fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2d
addchain: dec: 115792089237316195423570985008687907853269984665640564039457584007908834671661
addchain: best: opt(dictionary(hybrid(3,0),continued_fractions(dichotomic)))
_10     = 2*1
_100    = 2*_10
_101    = 1 + _100
_111    = _10 + _101
_1110   = 2*_111
_111000 = _1110 << 2
_111111 = _111 + _111000
i13     = _111111 << 4 + _1110
x12     = i13 << 2 + _111
x22     = x12 << 10 + i13 + 1
i29     = 2*x22
i31     = i29 << 2
i54     = i31 << 22 + i31
i122    = (i54 << 20 + i29) << 46 + i54
x223    = i122 << 110 + i122 + _111
i269    = ((x223 << 23 + x22) << 7 + _101) << 3
return    _101 + i269





 *)
