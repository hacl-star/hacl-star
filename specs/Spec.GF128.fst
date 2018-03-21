module Spec.GF128

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.GaloisField

(* Field types and parameters *)

let gf128 = mk_field 128 0xe1000000000000000000000000000000
let elem = felem gf128
let zero = zero #gf128

(* GCM types and specs *)
let blocksize : size_nat = 16
let keysize   : size_nat = 16
type block = lbytes blocksize
type tag   = lbytes blocksize
type key   = lbytes keysize

let encode (len:size_nat{len <= blocksize}) (w:lbytes len) : Tot elem =
  let b = create blocksize (u8 0) in
  let b = update_slice b 0 len w  in
  to_felem (nat_from_bytes_be b)

let decode (e:elem) : Tot block = nat_to_bytes_be blocksize (from_felem e)

let update (r:elem) (len:size_nat{len <= blocksize}) (w:lbytes len) (acc:elem) : Tot elem =
    (encode len w `fadd` acc) `fmul` r

val poly: len:size_nat -> text:lbytes len -> r:elem ->  Tot (a:elem)  (decreases len)
let poly len text r =
  let blocks = len / blocksize in
  let rem = len % blocksize in
  let init  : elem = zero in
  let acc   : elem =
    repeati blocks
      (fun i acc ->
      	let b = slice text (i * blocksize) ((i+1)*blocksize) in
      	update r blocksize b acc)
      init in
  let acc = if rem = 0 then acc else
    update r rem (slice text (len-rem) len) acc in
  acc
let finish (a:elem) (s:tag) : Tot tag = decode (a `fadd` (encode blocksize s))

let gmac (len:size_nat) (text:lbytes len) (k:key) : Tot tag  =
  let s = create blocksize (u8 0) in
  let r = encode blocksize k in
  finish (poly len text r) s
