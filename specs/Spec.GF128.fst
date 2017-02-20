module Spec.GF128

open FStar.Mul
open FStar.Seq
open FStar.UInt8
open FStar.Endianness
open Spec.GaloisField

(* Field types and parameters *)

#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

let irr : polynomial 127 = UInt.to_vec #128 0x87
let gf128 = mk_field 128 irr
let elem = felem gf128

type word = w:bytes{length w <= 16}
type tag =  lbytes 16
type text = seq word

val encode: lbytes 16 -> Tot elem
let encode b = to_felem (big_endian b)
val decode: elem -> Tot (lbytes 16)
let decode e = big_bytes 16ul (from_felem e)

let seq_head (vs:seq 'a {Seq.length vs > 0}) = Seq.slice vs 0 (Seq.length vs - 1)

val poly: vs:text -> r:elem -> Tot (a:elem) (decreases (Seq.length vs))
let rec poly vs r =
  if Seq.length vs = 0 then zero
  else
    let v = Seq.head vs in 
    (encode v +@ poly (Seq.tail vs) r ) *@ r

let finish a s = decode (a +@ (encode s))

let mac vs r s = finish (poly vs r) s

val poly_cons: x:lbytes 16 -> xs:text -> r:elem ->
  Lemma (poly (Seq.cons x xs) r == (encode x +@ poly xs r) *@ r)
let poly_cons x xs r =
  let xxs = Seq.cons x xs in
  Seq.lemma_len_append (Seq.create 1 x) xs;
  Seq.lemma_eq_intro (Seq.tail xxs) xs

val poly_empty: t:text{Seq.length t == 0} -> r:elem ->
  Lemma (poly t r == zero #gf128)
let poly_empty t r = ()

(* Test *)

let test() = Spec.GaloisField.test()