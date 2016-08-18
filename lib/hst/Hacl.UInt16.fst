module Hacl.UInt16
(* This module generated automatically using [mk_int.sh] *)

open FStar.UInt16
module U = FStar.UInt16
open FStar.Mul

(* NOTE: anything that you fix/update here should be reflected in [Hacl.IntN.fstp], which is mostly
 * a copy-paste of this module. *)

let n = U.n

private type t' = | Mk: v:U.t -> t'
type t = t'

let v (x:t) : GTot (FStar.UInt.uint_t n) = U.v x.v

val add: a:t -> b:t -> Pure t
  (requires (UInt.size (v a + v b) n))
  (ensures (fun c -> v a + v b = v c))
let add a b =
  Mk (add (a.v) (b.v))

val add_underspec: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun c ->
    UInt.size (v a + v b) n ==> v a + v b = v c))
let add_underspec a b =
  Mk (add_underspec (a.v) (b.v))

val add_mod: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun c -> (v a + v b) % pow2 n = v c))
let add_mod a b =
  Mk (add_mod (a.v) (b.v))

(* Subtraction primitives *)
val sub: a:t -> b:t -> Pure t
  (requires (UInt.size (v a - v b) n))
  (ensures (fun c -> v a - v b = v c))
let sub a b =
  Mk (sub (a.v) (b.v))

val sub_underspec: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun c ->
    UInt.size (v a - v b) n ==> v a - v b = v c))
let sub_underspec a b =
  Mk (sub_underspec (a.v) (b.v))

val sub_mod: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun c -> (v a - v b) % pow2 n = v c))
let sub_mod a b =
  Mk (sub_mod (a.v) (b.v))

(* Multiplication primitives *)
val mul: a:t -> b:t -> Pure t
  (requires (UInt.size (v a * v b) n))
  (ensures (fun c -> v a * v b = v c))
let mul a b =
  Mk (mul (a.v) (b.v))

val mul_underspec: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun c ->
    UInt.size (v a * v b) n ==> v a * v b = v c))
let mul_underspec a b =
  Mk (mul_underspec (a.v) (b.v))

val mul_mod: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun c -> (v a * v b) % pow2 n = v c))
let mul_mod a b =
  Mk (mul_mod (a.v) (b.v))

(* Division primitives *)
val div: a:t -> b:t{v b <> 0} -> Pure t
  (requires (UInt.size (v a / v b) n))
  (ensures (fun c -> v b <> 0 ==> v a / v b = v c))
let div a b =
  Mk (div (a.v) (b.v))

val div_underspec: a:t -> b:t{v b <> 0} -> Pure t
  (requires True)
  (ensures (fun c ->
    (v b <> 0 /\ UInt.size (v a / v b) n) ==> v a / v b = v c))
let div_underspec a b =
  Mk (div_underspec (a.v) (b.v))

(* Modulo primitives *)
val rem: a:t -> b:t{v b <> 0} -> Pure t
  (requires True)
  (ensures (fun c ->
    v a - ((v a / v b) * v b) = v c))
let rem a b = Mk (rem (a.v) (b.v))

(* Bitwise operators *)
val logand: t -> t -> Tot t
let logand a b = Mk (logand (a.v) (b.v))
val logxor: t -> t -> Tot t
let logxor a b = Mk (logxor (a.v) (b.v))
val logor: t -> t -> Tot t
let logor a b = Mk (logor (a.v) (b.v))
val lognot: t -> Tot t
let lognot a = Mk (lognot (a.v))

val uint_to_t: x:(UInt.uint_t n) -> Pure t
  (requires True)
  (ensures (fun y -> v y = x))
let uint_to_t x = Mk (uint_to_t x)

(* Shift operators *)
val shift_right: a:t -> s:FStar.UInt32.t -> Pure t
  (requires True)
  (ensures (fun c -> FStar.UInt32.v s < n ==> v c = (v a / (pow2 (FStar.UInt32.v s)))))
let shift_right a s = Mk (shift_right (a.v) s)

val shift_left: a:t -> s:FStar.UInt32.t -> Pure t
  (requires True)
  (ensures (fun c -> FStar.UInt32.v s < n ==> v c = ((v a * pow2 (FStar.UInt32.v s)) % pow2 n)))
let shift_left a s = Mk (shift_left (a.v) s)

assume val eq_mask: a:t -> b:t -> Tot (c:t{(v a = v b ==> v c = pow2 n - 1) /\ (v a <> v b ==> v c = 0)})
assume val gte_mask: a:t -> b:t -> Tot (c:t{(v a >= v b ==> v c = pow2 n - 1) /\ (v a < v b ==> v c = 0)})
assume val lt_mask: a:t -> b:t -> Tot (c:t{(v a < v b ==> v c = pow2 n - 1) /\ (v a >= v b ==> v c = 0)})

(* Infix notations *)
let op_Plus_Hat = add
let op_Plus_Question_Hat = add_underspec
let op_Plus_Percent_Hat = add_mod
let op_Subtraction_Hat = sub
let op_Subtraction_Question_Hat = sub_underspec
let op_Subtraction_Percent_Hat = sub_mod
let op_Star_Hat = mul
let op_Star_Question_Hat = mul_underspec
let op_Star_Percent_Hat = mul_mod
let op_Slash_Hat = div
let op_Percent_Hat = rem
let op_Hat_Hat = logxor
let op_Amp_Hat = logand
let op_Bar_Hat = logor
let op_Less_Less_Hat = shift_left
let op_Greater_Greater_Hat = shift_right

(* To input / output constants *)
assume val of_string: string -> Tot t
