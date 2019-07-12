module Spec.GF128

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Spec.GaloisField
open Lib.LoopCombinators


(* GF128 Field: note that bits are loaded in little-endian order *)
let irred = u128 0x87
let gf128 = gf U128 irred
let elem = felem gf128
let load_elem (b:lbytes 16) : elem = load_felem_le #gf128 b
let store_elem (e:elem) : lbytes 16 = store_felem_le #gf128 e

(* GCM types and specs *)
let blocksize : size_nat = 16
let keysize   : size_nat = 16
type block = lbytes blocksize
type tag   = lbytes blocksize
type key   = lbytes keysize


let encode (len:size_nat{len <= blocksize}) (w:lbytes len) : Tot elem =
  let b = create blocksize (u8 0) in
  let b = update_slice b 0 len w  in
  load_elem b

let decode (e:elem) : Tot block = store_elem e

noeq type state = {
  r:elem;
  acc:elem
}

let init (h:lbytes blocksize) : state = {
  r =  encode blocksize h;
  acc = zero
}

let set_acc (st:state) (acc:elem) = {st with acc = acc}

let update (len:size_nat{len <= blocksize}) (w:lbytes len) (st:state) : state =
  let acc = (encode len w `fadd` st.acc) `fmul` st.r in
  set_acc st acc

let poly (text:seq uint8) (st:state) : state =
  repeat_blocks #uint8 #state blocksize text
    (fun b st -> update blocksize b st)
    (fun rem b st -> if rem = 0 then st else update rem b st)
  st

let finish (st:state) (s:tag) : Tot tag =
  decode (st.acc `fadd` (encode blocksize s))

let gmul (text:bytes) (h:lbytes blocksize) : Tot tag  =
  let st = init h in
  let st = poly text st in
  decode st.acc

val gmac:
    text: bytes
  -> h: lbytes blocksize
  -> k: key ->
  Tot tag

let gmac text h k =
  let st = init h in
  let st = poly text st in
  finish st k
