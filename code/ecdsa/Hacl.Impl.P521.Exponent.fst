module Hacl.Impl.P521.Exponent

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Hacl.Impl.EC.Math 

open Lib.IntTypes
open Lib.Buffer

open FStar.Math.Lemmas
open FStar.Mul

open Hacl.Spec.EC.Definition
open Hacl.Lemmas.P256
open Hacl.Impl.P256.LowLevel 
open Spec.ECC
open Lib.Loops

open Hacl.Impl.P256.MM.Lemmas

open Hacl.Impl.EC.MontgomeryMultiplication
open Hacl.Spec.MontgomeryMultiplication


#set-options "--z3rlimit 100 --ifuel 0 --fuel 0"

let felem_521 = lbuffer uint64 (size 9)


assume val montgomery_multiplication_buffer: (*#c: curve -> *) a: lbuffer uint64 (size 9) -> b: lbuffer uint64 (size 9) -> result: lbuffer uint64 (size 9) ->  
  Stack unit
    (requires (fun h ->
      live h a /\ live h b /\ live h result (* /\ felem_eval c h a  /\ felem_eval c h b *))) 
    (ensures (fun h0 _ h1 -> True (* 
      modifies (loc result) h0 h1 /\  
      felem_eval c h1 result /\
      as_nat c h1 result = (as_nat c h0 a * as_nat c h0 b * modp_inv2_prime (pow2 (getPower c)) (getPrime c)) % getPrime c /\
      as_nat c h1 result = toDomain_ #c (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 b) % getPrime c) /\
      as_nat c h1 result = toDomain_ #c (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 b))) *)))


assume val montgomery_square_buffer: a: lbuffer uint64 (size 9) -> result: lbuffer uint64 (size 9) ->  
  Stack unit
    (requires (fun h -> live h a)) 
    (ensures (fun h0 _ h1 -> True (*)
      (
  let prime = getPrime c in 
  modifies (loc result) h0 h1 /\  
  felem_eval c h1 result /\ 
  as_nat c h1 result = (as_nat c h0 a * as_nat c h0 a * modp_inv2_prime (getPower c) prime) % prime /\
  as_nat c h1 result = toDomain_ #c (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 a) % prime) /\
  as_nat c h1 result = toDomain_ #c (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 a)))) *) ))



assume val fsquarePowN: n: size_t -> a: felem_521 -> Stack unit 
  (requires (fun h -> live h a)) 
  (ensures (fun h0 _ h1 -> (*
    let k = fromDomain_ #P256 (as_nat P256 h0 a) in
    modifies (loc a) h0 h1 /\ as_nat P256 h1 a < prime256 /\ 
    as_nat P256 h1 a = toDomain_ #P256 (pow k (pow2 (v n)))*) True))



(* Check is needed *)

(* [@ CInline] *)
val exponent_p521: a: felem_521 -> result: felem_521 -> 
  tempBuffer: lbuffer uint64 (9ul *. 8ul) -> Stack unit
  (requires fun h -> live h a /\ live h tempBuffer /\ live h result /\ disjoint tempBuffer result)
  (ensures fun h0 _ h1 -> True)


let exponent_p521 t result tempBuffer = 
  let h0 = ST.get () in 

  let t0 = sub tempBuffer (size 0) (size 9) in 

  let t1 = sub tempBuffer (size 9) (size 9) in 
  let t2 = sub tempBuffer (size 18) (size 9) in 
  let t3 = sub tempBuffer (size 27) (size 9) in 
  let t4 = sub tempBuffer (size 36) (size 9) in 
  let t5 = sub tempBuffer (size 45) (size 9) in 
  let t6 = sub tempBuffer (size 54) (size 9) in 
  let t7 = sub tempBuffer (size 63) (size 9) in  

(* _10(t0)       = sq(t) *)
	montgomery_square_buffer t t0;

(* _11       = m(t, _10) *)
	montgomery_multiplication_buffer t t0 t0;

(* _1100     = n_sq(_11, 2) *)
	montgomery_square_buffer t0 t1;
	montgomery_square_buffer t1 t1;

(* _1111     = m(_11, _1100) *)
	montgomery_multiplication_buffer t0 t1 t1;

(* _11110000 = n_sq(_1111 , 4) *)
	montgomery_square_buffer t1 t2;
	fsquarePowN (size 3) t2;

(* _11111111 = m(_1111, _11110000) *)
	montgomery_multiplication_buffer t1 t2 t2;

(* x16       = m(n_sq(_11111111, 8), _11111111) *)
	montgomery_square_buffer t2 t3;
	fsquarePowN (size 7) t3;
	montgomery_multiplication_buffer t3 t2 t2;

(* x32       = m(n_sq(x16, 16), x16) *)
	montgomery_square_buffer t2 t3;
	fsquarePowN (size 15) t3;
	montgomery_multiplication_buffer t3 t2 t3;

(* x64       = m(n_sq(x32, 32) , x32) *)
	montgomery_square_buffer t2 t3;
	fsquarePowN (size 31) t3;
	montgomery_multiplication_buffer t3 t2 t3;

(* x65       = m(sq(x64), t) *)
	montgomery_square_buffer t2 t3;
	montgomery_multiplication_buffer t3 t t3;

(* x129      = m(n_sq(x65, 64) , x64) *)
	fsquarePowN (size 64) t3;
	montgomery_multiplication_buffer t3 t2 t2;

(* x130      = m( sq( x129) , t)  *)
	montgomery_square_buffer t2 t3;
	montgomery_multiplication_buffer t t3 t3;

(* x259      = m(n_sq(x130, 129), x129) *)
	fsquarePowN (size 129) t3;
	montgomery_multiplication_buffer t3 t2 t2;

(* x260      = m(sq(x259), t) *)
	montgomery_square_buffer t2 t3;
	montgomery_multiplication_buffer t t3 t3;

(* x519      = m(n_sq(x260, 259) , x259) *)
	fsquarePowN (size 259) t3;
	montgomery_multiplication_buffer t3 t2 t3;

(* m(n_sq(x519, 2), t) *)
	fsquarePowN (size 2) t3;
	montgomery_multiplication_buffer t3 t result


(* 


prime = 2^521 - 1

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

_10 (t0)       = sq(t)
_11 (t0)       = m(t, _10)
_1100 (t1)     = n_sq(_11, 2)
_1111 (t1)     = m(_11, _1100)
_11110000 (t2) = n_sq(_1111 , 4)
_11111111 (t2) = m(_1111, _11110000)

x16 (t2)      = m(n_sq(_11111111, 8), _11111111)
x32 (t2)      = m(n_sq(x16, 16), x16)
x64 (t2)     = m(n_sq(x32, 32) , x32)
x65 (t3)      = m(sq(x64), t)
x129 (t2)     = m(n_sq(x65, 64) , x64)
x130 (t3)     = m(sq(x129) , t) 
x259 (t2)    = m(n_sq(x130, 129), x129)
x260 (t3)     = m(sq(x259), t)
x519 (t3)     = m(n_sq(x260, 259) , x259)
r =       m(n_sq(x519, 2), t)

print(hex(r))
print(hex (power_mod (t, prime - 2, prime)))


addchain search '2^521 - 3'
addchain: expr: "2^521 - 3"
addchain: hex: 1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd
addchain: dec: 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057149
addchain: best: opt(dictionary(run_length(0),continued_fractions(dichotomic)))
_10       = 2*1
_11       = 1 + _10
_1100     = _11 << 2
_1111     = _11 + _1100
_11110000 = _1111 << 4
_11111111 = _1111 + _11110000
x16       = _11111111 << 8 + _11111111
x32       = x16 << 16 + x16
x64       = x32 << 32 + x32
x65       = 2*x64 + 1
x129      = x65 << 64 + x64
x130      = 2*x129 + 1
x259      = x130 << 129 + x129
x260      = 2*x259 + 1
x519      = x260 << 259 + x259
return      x519 << 2 + 1





 *)