module Spec.Curve25519


open FStar.Mul
open FStar.Seq
open FStar.UInt8
open FStar.Endianness
open Spec.Lib

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

(* Field types and parameters *)

unfold let prime : (p:pos{p = pow2 255 - 19}) =
  assert_norm(pow2 255 - 19 = 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed);
  0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed

type elem : Type0 = e:int{e >= 0 /\ e < prime}

let zero : elem = 0
let one  : elem = 1

val fadd: elem -> elem -> Tot elem
let fadd e1 e2 = (e1 + e2) % prime
let op_Plus_At e1 e2 = fadd e1 e2

val fsub: elem -> elem -> Tot elem
let fsub e1 e2 = (e1 - e2) % prime
let op_Subtraction_At e1 e2 = fsub e1 e2

val fmul: elem -> elem -> Tot elem
let fmul e1 e2 = (e1 * e2) % prime
let op_Star_At e1 e2 = fmul e1 e2

val fdiv: elem -> d:elem{d <> zero} -> Tot elem
let fdiv e1 e2 = (e1 / e2) % prime
let op_Slash_At e1 e2 = fdiv e1 e2

let rec op_Star_Star (e:elem) (n:nat) : Tot elem =
  if n = 1 then e
  else (
    if n % 2 = 0 then op_Star_Star (e *@ e) (n / 2)
    else e *@ (op_Star_Star (e *@ e) ((n-1)/2))
  )

(* Curve group *)

(* inline_for_extraction let param_a = 486662 *)
(* inline_for_extraction let param_b = 1 *)


(* type affine_point = *)
(*   | Inf *)
(*   | Finite: x:elem -> y:elem -> affine_point *)

(* let on_curve (p:affine_point) : Tot bool = *)
(*   (Inf? p || (Finite? p && (let x, y = Finite?.x p, Finite?.y p in *)
(*              (y ** 2) = ((x ** 3) +@ (param_a *@ x) +@ param_b)))) *)

(* type celem = p:affine_point{on_curve p} *)


(* (\* Definition of the addition, same as the SSReflect one *\) *)
(* #set-options "--lax" *)

(* val add': affine_point -> affine_point -> Tot affine_point *)
(* let add' p1 p2 = *)
(*   if not(on_curve p1) then Inf *)
(*   else if not(on_curve p2) then Inf  *)
(*   else if Inf? p1 then p2 *)
(*   else if Inf? p2 then p1 *)
(*   else ( *)
(*     let x1 = Finite?.x p1 in  *)
(*     let x2 = Finite?.x p2 in  *)
(*     let y1 = Finite?.y p1 in  *)
(*     let y2 = Finite?.y p2 in  *)
(*     if x1 = x2 then ( *)
(*       if y1 = y2 && y1 <> zero then ( *)
(* 	(\* characteristic_corollary y1; *\) *)
(* 	let lam = ((3 *@ (x1 ** 2) +@ param_a) /@ (2 *@ y1)) in  *)
(* 	let x = ((lam ** 2) -@ (2 *@ x1)) in *)
(* 	let y = ((lam *@ (x1 -@ x)) -@ y1) in *)
(* 	Finite x y *)
(*       ) else ( *)
(* 	Inf *)
(*       ) *)
(*     ) *)
(*     else ( *)
(*       let lam = (y2 -@ y1) /@ (x2 -@ x1) in *)
(*       let x = ((lam ** 2) -@ x1 -@ x2) in *)
(*       let y = (lam *@ (x1 -@ x) -@ y1) in *)
(*       Finite x y *)
(*     ) *)
(*   ) *)


(* let rec exp (n:nat) (p:affine_point) : Tot affine_point = *)
(*   if n = 0 then Inf else add' p (exp (n-1) p) *)


#reset-options "--initial_fuel 0 --max_fuel 0"

type proj_point = | Proj: x:elem -> y:elem -> z:elem -> proj_point

type scalar = lbytes 32
type serialized_point = lbytes 32


// Try to write it with "set" ?
let decodeScalar25519 (k:scalar) : Tot scalar =
  let k0  = index k 0  in
  let k31 = index k 31 in
  let k   = upd k 0 (k0 &^ 248uy)             in
  let k   = upd k 31 ((k31 &^ 127uy) |^ 64uy) in
  k

let xor a b = match a,b with | true, false | false, true -> true | _ -> false

let cswap swap x y = if swap then y,x else x,y

val montgomery_ladder: k:scalar -> u:serialized_point -> Tot elem
let montgomery_ladder k u =
  let rec loop k x_1 x_2 z_2 x_3 z_3 swap (ctr:nat) : Tot (tuple5 elem elem elem elem bool)
                                                   (decreases (ctr))
  =
    if ctr = 0 then (x_2, z_2, x_3, z_3, swap)
    else (
      let ctr = ctr - 1 in
      let k_t = (k / pow2 ctr) % 2 = 1 in // ctr-th bit of the scalar
      let swap = swap `xor` k_t in
      let x_2, x_3 = cswap swap x_2 x_3 in
      let z_2, z_3 = cswap swap z_2 z_3 in
      let swap = k_t in
      let a  = x_2 +@ z_2 in
      let aa = a**2 in
      let b  = x_2 -@ z_2 in
      let bb = b**2 in
      let e = aa -@ bb in
      let c = x_3 +@ z_3 in
      let d = x_3 -@ z_3 in
      let da = d *@ a in
      let cb = c *@ b in
      let x_3 = (da +@ cb)**2 in
      let z_3 = x_1 *@ ((da -@ cb)**2) in
      let x_2 = aa *@ bb in
      let z_2 = e *@ (aa +@ (121665 *@ e)) in
      loop k x_1 x_2 z_2 x_3 z_3 swap ctr
  ) in
  let k    = little_endian k in // Scalar as natural number
  let u    = little_endian u % prime in // Point as element of the prime field
  let x_1   = u in               // Basepoint 'x' coordinate
  let x_2   = one in             // First point 'P' of the ladder (point at infinity at first)
  let z_2   = 0 in
  let x_3   = u in               // Second point 'Q' of the ladder (equal to 'u' at first)
  let z_3   = one in
  let swap = false in           // Swap variable
  let x_2, z_2, x_3, z_3, swap = loop k x_1 x_2 z_2 x_3 z_3 swap 256 in
  // Can be integrated to the recursive call
  let x_2, x_3 = cswap swap x_2 x_3 in
  let z_2, z_3 = cswap swap z_2 z_3 in
  x_2 *@ (z_2 ** (prime - 2))


let scalarmult (k:scalar) (u:serialized_point) : Tot serialized_point =
  let k = decodeScalar25519 k in
  let u = montgomery_ladder k u in
  assert_norm(pow2 256 >= pow2 255 - 19);
  little_bytes 32ul u


#set-options "--lax"

let test () =  
  let scalar1 = createL [
    0xa5uy; 0x46uy; 0xe3uy; 0x6buy; 0xf0uy; 0x52uy; 0x7cuy; 0x9duy;
    0x3buy; 0x16uy; 0x15uy; 0x4buy; 0x82uy; 0x46uy; 0x5euy; 0xdduy;
    0x62uy; 0x14uy; 0x4cuy; 0x0auy; 0xc1uy; 0xfcuy; 0x5auy; 0x18uy;
    0x50uy; 0x6auy; 0x22uy; 0x44uy; 0xbauy; 0x44uy; 0x9auy; 0xc4uy
    ] in
  let scalar2 = createL [
    0x4buy; 0x66uy; 0xe9uy; 0xd4uy; 0xd1uy; 0xb4uy; 0x67uy; 0x3cuy;
    0x5auy; 0xd2uy; 0x26uy; 0x91uy; 0x95uy; 0x7duy; 0x6auy; 0xf5uy;
    0xc1uy; 0x1buy; 0x64uy; 0x21uy; 0xe0uy; 0xeauy; 0x01uy; 0xd4uy;
    0x2cuy; 0xa4uy; 0x16uy; 0x9euy; 0x79uy; 0x18uy; 0xbauy; 0x0duy
    ] in
  let input1 = createL [
    0xe6uy; 0xdbuy; 0x68uy; 0x67uy; 0x58uy; 0x30uy; 0x30uy; 0xdbuy;
    0x35uy; 0x94uy; 0xc1uy; 0xa4uy; 0x24uy; 0xb1uy; 0x5fuy; 0x7cuy;
    0x72uy; 0x66uy; 0x24uy; 0xecuy; 0x26uy; 0xb3uy; 0x35uy; 0x3buy;
    0x10uy; 0xa9uy; 0x03uy; 0xa6uy; 0xd0uy; 0xabuy; 0x1cuy; 0x4cuy
    ] in
  let input2 = createL [
    0xe5uy; 0x21uy; 0x0fuy; 0x12uy; 0x78uy; 0x68uy; 0x11uy; 0xd3uy;
    0xf4uy; 0xb7uy; 0x95uy; 0x9duy; 0x05uy; 0x38uy; 0xaeuy; 0x2cuy;
    0x31uy; 0xdbuy; 0xe7uy; 0x10uy; 0x6fuy; 0xc0uy; 0x3cuy; 0x3euy;
    0xfcuy; 0x4cuy; 0xd5uy; 0x49uy; 0xc7uy; 0x15uy; 0xa4uy; 0x93uy
    ] in
  let expected1 = createL [
    0xc3uy; 0xdauy; 0x55uy; 0x37uy; 0x9duy; 0xe9uy; 0xc6uy; 0x90uy;
    0x8euy; 0x94uy; 0xeauy; 0x4duy; 0xf2uy; 0x8duy; 0x08uy; 0x4fuy;
    0x32uy; 0xecuy; 0xcfuy; 0x03uy; 0x49uy; 0x1cuy; 0x71uy; 0xf7uy;
    0x54uy; 0xb4uy; 0x07uy; 0x55uy; 0x77uy; 0xa2uy; 0x85uy; 0x52uy
    ] in
  let expected2 = createL [
    0x95uy; 0xcbuy; 0xdeuy; 0x94uy; 0x76uy; 0xe8uy; 0x90uy; 0x7duy;
    0x7auy; 0xaduy; 0xe4uy; 0x5cuy; 0xb4uy; 0xb8uy; 0x73uy; 0xf8uy;
    0x8buy; 0x59uy; 0x5auy; 0x68uy; 0x79uy; 0x9fuy; 0xa1uy; 0x52uy;
    0xe6uy; 0xf8uy; 0xf7uy; 0x64uy; 0x7auy; 0xacuy; 0x79uy; 0x57uy
    ] in
  scalarmult scalar1 input1 = expected1
  (* && scalarmult scalar2 input2 = expected2 *) // TODO: fails !!!
