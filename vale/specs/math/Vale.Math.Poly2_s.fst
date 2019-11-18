module Vale.Math.Poly2_s
open FStar.Mul
open FStar.Seq

let poly = D.poly
let degree p = D.degree p
let zero = D.zero
let one = D.one
let monomial n = D.monomial n
let shift p n = D.shift p n
let reverse p n = D.reverse p n
let poly_index p n = D.poly_index p n
let to_seq s n = D.to_seq s n
let of_seq s = D.of_seq s
let of_fun len f = D.of_fun len f
let add a b = D.add a b
let mul a b = D.mul a b

assume val undefined_div_by_zero (a:poly) : poly
assume val undefined_mod_by_zero (a:poly) : poly

let div a b = if degree b >= 0 then D.div a b else undefined_div_by_zero a
let mod a b = if degree b >= 0 then D.mod a b else undefined_mod_by_zero a

let reveal_defs () = ()
