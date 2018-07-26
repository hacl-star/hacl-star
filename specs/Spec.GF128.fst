module Spec.GF128

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Spec.GaloisField

(* Field types and parameters *)

let gf128 = mk_field 128 0xe1000000000000000000000000000000
let elem = felem gf128
let zero = zero #gf128

(* GCM types and specs *)
inline_for_extraction
let size_block : size_nat = 16
inline_for_extraction
let size_key   : size_nat = 16

type block = lbytes size_block
type tag   = lbytes size_block
type key   = lbytes size_key

let encode (len:size_nat{len <= size_block}) (w:lbytes len) : Tot elem =
  let b = create size_block (u8 0) in
  let b = update_slice b 0 len w  in
  to_felem (nat_from_bytes_be b)

let decode (e:elem) : Tot block = nat_to_bytes_be size_block (from_felem e)

let update (r:elem ) (len:size_nat{len <= size_block}) (w:lbytes len) (acc:elem) : Tot elem =
    (encode len w `fadd` acc) `fmul` r

val poly: len:size_nat -> text:lbytes len -> r:elem ->  Tot (a:elem)  (decreases len)
let poly len text r =
  let blocks = len / size_block in
  let rem = len % size_block in
  let init  : elem = zero in
  let acc   : elem =
    repeati blocks
      (fun i acc  ->
	let b = slice text (i * size_block) ((i+1)*size_block) in
	update r size_block b acc)
      init in
  let acc = if rem = 0 then acc else
    update r rem (slice text (len-rem) len) acc in
  acc
let finish (a:elem) (s:tag) : Tot tag = decode (a `fadd` (encode size_block s))

let gmul (len:size_nat) (text:lbytes len) (h:lbytes size_block) : Tot tag  =
    let r = encode size_block h in
    decode (poly len text r)

val gmac:
  len:size_nat ->
  text:lbytes len ->
  h:lbytes size_block ->
  k:key ->
  Tot tag
let gmac len text h k =
  let r = encode size_block h in
  finish (poly len text r) k
