module MPFR.BinaryFP

open FStar.Mul
open MPFR.Maths

#set-options "--z3refresh --z3rlimit 5 --max_fuel 1 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 0"

(* Arbitrary precision floating point number: significand * 2 ^ exponent 
 * this allows multiple representations for one value. *)
noeq type binary_fp = {significand:int; exponent:int}

let mk_fp m x = {significand = m; exponent = x}
    
(* Constants *)
let zero_fp = mk_fp 0 0

let unit_fp x = mk_fp 1 x

(* Evaluation to integer after adding a sufficient large exponent 
 * Maybe evaluate to a real number when F* have one. *)
let eval_i fp (elb:int{fp.exponent - elb >= 0}) = fp.significand * pow2 (fp.exponent - elb)

(* Comparison *)
let eq (a:binary_fp) (b:binary_fp) = let elb = min a.exponent b.exponent in eval_i a elb = eval_i b elb
let gt (a:binary_fp) (b:binary_fp) = let elb = min a.exponent b.exponent in eval_i a elb > eval_i b elb
let ge (a:binary_fp) (b:binary_fp) = let elb = min a.exponent b.exponent in eval_i a elb >= eval_i b elb
let lt (a:binary_fp) (b:binary_fp) = let elb = min a.exponent b.exponent in eval_i a elb < eval_i b elb
let le (a:binary_fp) (b:binary_fp) = let elb = min a.exponent b.exponent in eval_i a elb <= eval_i b elb

(* Negation post-condition:
 * r.mant * 2 ^ (r.exp - elb) = - a.mant * 2 ^ (a.exp - elb)
 * is equivalent to
 * r.mant * 2 ^ r.exp = - a.mant * 2 ^ a.exp *)
val neg: a:binary_fp -> Tot (r:binary_fp{
    let elb = a.exponent in
    r.exponent >= elb /\
    eval_i r elb = - eval_i a elb})
let neg a = mk_fp (- a.significand) a.exponent

(* Addition post-condition:
 * a.mant * 2 ^ (a.exp - elb) + b.mant * 2 ^ (b.exp - elb) = r.mant * 2 ^ (r.exp - elb)
 * is equivalent to
 * a.mant * 2 ^ a.exp + b.mant * 2 ^ b.exp = r.mant * 2 ^ r.exp *)
val add: a:binary_fp -> b:binary_fp -> Tot (r:binary_fp{
    let elb = min a.exponent b.exponent in
    r.exponent >= elb /\
    eval_i a elb + eval_i b elb = eval_i r elb})
let add a b =
    let elb = min a.exponent b.exponent in
    mk_fp (a.significand * pow2 (a.exponent - elb) + b.significand * pow2 (b.exponent - elb)) elb
    
(* Subtraction post-condition
 * a.mant * 2 ^ (a.exp - elb) - b.mant * 2 ^ (b.exp - elb) = r.mant * 2 ^ (r.exp - elb)
 * is equivalent to
 * a.mant * 2 ^ a.exp - b.mant * 2 ^ b.exp = r.mant * 2 ^ r.exp *)
val sub: a:binary_fp -> b:binary_fp -> Tot (r:binary_fp{
    let elb = min a.exponent b.exponent in
    r.exponent >= elb /\
    eval_i a elb - eval_i b elb = eval_i r elb})
let sub a b = add a (neg b)

(* Multiplication post-condition
 * a.mant * 2 ^ (a.exp - elb) * b.mant * 2 ^ (b.exp - elb) = r.mant * 2 ^ (r.exp - 2 * elb)
 * is equivalent to
 * a.mant * 2 ^ a.exp * b.mant * 2 ^ b.exp = r.mant * 2 ^ r.exp *)
val mul: a:binary_fp -> b:binary_fp -> Tot (r:binary_fp{
    let elb = min a.exponent b.exponent in
    r.exponent >= 2 * elb /\
    eval_i a elb * eval_i b elb = eval_i r (2 * elb)})
let mul a b =
    mk_fp (a.significand * b.significand) (a.exponent + b.exponent)

(* Infix notations *)
unfold let op_Equals_Dot  = eq
unfold let op_Greater_Dot  = gt
unfold let op_Greater_Equals_Dot = ge
unfold let op_Less_Dot  = lt
unfold let op_Less_Equals_Dot = le
unfold let op_Plus_Dot  = add
unfold let op_Subtraction_Dot  = sub
unfold let op_Star_Dot  = mul
