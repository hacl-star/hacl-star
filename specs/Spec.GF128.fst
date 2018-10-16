module Spec.GF128

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Spec.GaloisField
open Lib.LoopCombinators

(* Field types and parameters *)

//let gf128 = mk_field 128 0xe1
//let elem = felem gf128
//let zero = zero #gf128
// let reverse (u:uint128) : uint128 = 
//   repeati 64 
//     (fun i u -> 
//       let ui = u &. (u128 1 <<. size i) in
//       let u128_i = u &. ((u128 1) <<. size (127 - i)) in
//       (u &. (u128 0 <<. size i) &. ((u128 0) <<. size (127 - i))) |.
//       (ui <<. size (127 - i - i)) |. (u128_i >>. size (127 - i - i))
//     ) u
//let irred = u128 0x87
// let fmul (a:uint128) (b:uint128) : uint128 =
//   let (p,a,b) =
//     repeati 127 (fun i (p,a,b) ->
// 	   let b0 = eq_mask #U128 (b &. u128 1) (u128 1) in
// 	   let p = p ^. (b0 &. a) in
//   	   let carry_mask = eq_mask #U128 (a >>. 127) (u128 1) in
// 	   let a = a <<. size 1 in
// 	   let a = a ^. (carry_mask &. irred) in
// 	   let b = b >>. size 1 in
// 	   (p,a,b)) (u128 0,a,b) in
//   let b0 = eq_mask #U128 (b &. u128 1) (u128 1) in
//   let p = p ^. (b0 &. a) in
//   p


  
let elem = uint128
let to_elem x = x
let from_elem x = x
let zero = u128 0
let irred = u128 0xE1000000000000000000000000000000

let fadd (a:uint128) (b:uint128) : uint128 = a ^. b 

let fmul (a:uint128) (b:uint128) : uint128 =
  let (p,a,b) =
    repeati 127 (fun i (p,a,b) ->
	   let b0 = eq_mask #U128 (b >>. 127) (u128 1) in
	   let p = p ^. (b0 &. a) in
  	   let carry_mask = eq_mask #U128 (a &. u128 1) (u128 1) in
	   let a = a >>. size 1 in
	   let a = a ^. (carry_mask &. irred) in
	   let b = b <<. size 1 in
	   (p,a,b)) (u128 0,a,b) in
  let b0 = eq_mask #U128 (b >>. 127) (u128 1) in
  let p = p ^. (b0 &. a) in
  p

(* GCM types and specs *)
let blocksize : size_nat = 16
let keysize   : size_nat = 16
type block = lbytes blocksize
type tag   = lbytes blocksize
type key   = lbytes keysize

let encode (len:size_nat{len <= blocksize}) (w:lbytes len) : Tot elem =
  let b = create blocksize (u8 0) in
  let b = update_slice b 0 len w  in
  to_elem (uint_from_bytes_be #U128 b)

let decode (e:elem) : Tot block = uint_to_bytes_be (from_elem e)

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
  text:bytes ->
  h:lbytes blocksize ->
  k:key ->
  Tot tag
let gmac text h k =
  let st = init h in
  let st = poly text st in
  finish st k
