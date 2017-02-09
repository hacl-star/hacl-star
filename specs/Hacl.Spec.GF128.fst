module Hacl.Spec.GF128

open FStar.Mul
open FStar.Seq
(* Field types and parameters *)

type elem = UInt128.t

let zero: elem = FStar.Int.Cast.uint64_to_uint128(0uL)
let one: elem  = FStar.Int.Cast.uint64_to_uint128(1uL)

val fadd: elem -> elem -> Tot elem
let fadd e1 e2 = (e1 ^^ e2)
let op_Plus_At e1 e2 = fadd e1 e2


noextract val ith_bit_mask: num:elem -> i:nat{i < 128} -> Tot (r:elem{
    nth (v num) i = true ==> r = ones_128 /\
    nth (v num) i = false ==> r = zero_128})
let ith_bit_mask num i = if (nth (v num) i) then ones_128 else zero_128

val shift_right: elem -> Tot elem
let shift_right a = a >>^ 1ul

private let r_mul = uint64_to_uint128(225uL) <<^ 120ul


val mask_add: a:elem -> b:elem -> r:elem -> dep:nat{dep < 128} -> Tot (s:elem{
    nth (v b) dep = true ==> s = r +@ a /\
    nth (v b) dep = false ==> s = r}) (decreases (128 - dep))
let mask_add a b r dep =
  let msk = ith_bit_mask b dep in
  let m = a &^ msk in
  r +@ m

val shift_right_modulo: a:elem -> Tot (r:elem{
    nth (v a) 127 = true ==> r = (shift_right a) +@ r_mul /\
    nth (v a) 127 = false ==> r = shift_right a})
let shift_right_modulo a =
  let msk = ith_bit_mask a 127 in
  let m = r_mul &^ msk in
  shift_right a +@ m

val mul_loop: a:elem -> b:elem -> r:elem -> dep:nat{dep <= 128} -> Tot elem
  (decreases (128 - dep))
let rec mul_loop a b r dep =
  if dep = 128 then r else
  begin
    let nr = mask_add a b r dep in 
    let na = shift_right_modulo a in
    mul_loop na b nr (dep + 1)
  end

val fmul: elem -> elem -> Tot elem
let fmul e1 e2 = (e1 * e2) % prime


let op_Star_At e1 e2 = fmul e1 e2

(* Types from Low-level crypto *)
type byte = FStar.UInt8.t
type bytes = seq byte
type word = w:bytes{length w <= 16}
type word_16 = w:bytes{length w = 16}
type tag = word_16
type text = seq word

(* Assumed for simplicity sake for now (see low-level/crypto *)
let rec big_endian (b:bytes) : Tot (n:nat) (decreases (Seq.length b)) = 
  if Seq.length b = 0 then 0 
  else
    UInt8.v (last b) + pow2 8 * big_endian (Seq.slice b 0 (Seq.length b - 1))

let encode (w:word) : Tot elem = uint_to_t (big_endian b)

val poly: vs:text -> r:elem -> Tot (a:elem) (decreases (Seq.length vs))
let rec poly vs r =
  if Seq.length vs = 0 then 0
  else 
    let v = SeqProperties.head vs in
    (encode v +@ poly (SeqProperties.tail vs) r) *@ r

let finish a s = decode (a +@ (encode s))

let mac vs r s = finish (poly vs r) s
