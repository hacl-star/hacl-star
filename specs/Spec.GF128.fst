module Spec.GF128

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Spec.GaloisField
open Lib.LoopCombinators

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

noeq type state = {
    r:elem;
    acc:elem
  }
  
let init (h:lbytes blocksize) : state = 
  {r =  encode blocksize h;
   acc = zero}

let set_acc (st:state) (acc:elem) =
  {st with acc = acc}

let update (len:size_nat{len <= blocksize}) (w:lbytes len) (st:state) : state =
    let acc = (encode len w `fadd` st.acc) `fmul` st.r in
    set_acc st acc


let poly (text:seq uint8) (st:state) : state =
  repeat_blocks #uint8 #state blocksize text
    (fun i b st -> update blocksize b st)
    (fun i rem b st -> if rem = 0 then st else update rem b st)
  st

let finish (st:state) (s:tag) : Tot tag = 
  decode (st.acc `fadd` (encode blocksize s))

let gmul (text:bytes) (h:lbytes blocksize) : Tot tag  =
    let st = init h in
    let st = poly text st in
    decode st.acc

val gmac:
  text:bytes ->
  h:lbytes blocksize ->
  k:key ->
  Tot tag
let gmac text h k =
  let st = init h in
  let st = poly text st in
  finish st k
