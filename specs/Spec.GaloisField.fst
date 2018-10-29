module Spec.GaloisField
open Lib.IntTypes
open Lib.Sequence
open Lib.LoopCombinators
open Lib.ByteSequence
(* We represent GF(2^n) by uint_t along  with some  irreducible polynomial also of type uint_t *)
(* Consequently this module is specialized for GF(8/16/32/64/128) but can be generalized to other sizes if needed *)

noeq type field = 
  | GF: t:inttype{t <> U1} -> irred: uint_t t SEC -> field

let gf t irred = GF t irred 
type felem (f:field) = uint_t f.t SEC
let to_felem (#f:field) (n:nat{n <= maxint f.t}) : felem f = uint #f.t #SEC n 
let from_felem (#f:field) (e:felem f) : n:nat{n <= maxint f.t} = uint_v #f.t #SEC e 

let zero (#f:field) : felem f = to_felem 0
let one (#f:field) : felem f = to_felem 1

let load_felem_be (#f:field) (b:lbytes (numbytes f.t)) : felem f = uint_from_bytes_be #f.t #SEC b
let store_felem_be (#f:field) (e:felem f): lbytes (numbytes f.t) = uint_to_bytes_be #f.t #SEC e

let reverse (#t:inttype) (a:uint_t t SEC) : uint_t t SEC = 
  repeati (bits t) (fun i u ->
    u |. (((a >>. size i) &. uint #t #SEC 1) <<. (size (bits t - 1 - i)))) (uint #t #SEC 0)

let load_felem_le (#f:field) (b:lbytes (numbytes f.t)) : felem f = reverse #f.t (load_felem_be #f b)
let store_felem_le (#f:field) (e:felem f) : lbytes (numbytes f.t) = store_felem_be #f (reverse #f.t e)

let fadd (#f:field) (a:felem f) (b:felem f) : felem f = a ^. b
let op_Plus_At #f e1 e2 = fadd #f e1 e2

let fmul (#f:field) (a:felem f) (b:felem f) : felem f =
  let one = one #f in
  let zero = zero #f in
  let (p,a,b) =
    repeati (bits f.t - 1) (fun i (p,a,b) ->
	   let b0 = eq_mask #f.t (b &. one) one in
	   let p = p ^. (b0 &. a) in
  	   let carry_mask = eq_mask #f.t (a >>. size (bits f.t - 1)) one  in
	   let a = a <<. size 1 in
	   let a = a ^. (carry_mask &. f.irred) in
	   let b = b >>. size 1 in
	   (p,a,b)) (zero,a,b) in
  let b0 = eq_mask #f.t (b &. one) one in
  let p = p ^. (b0 &. a) in
  p
let op_Star_At #f e1 e2 = fmul #f e1 e2

val fexp: #f:field -> a:felem f -> n:nat{n >= 1} -> Tot (felem f) (decreases n)
let rec fexp #f a x =
  if x = 1 then a else
  if x = 2 then fmul #f a a else
  let r = fexp #f a (x / 2) in
  let r' = fmul #f r r in
  if (x % 2) = 0  then r'
  else fmul #f a r'
let op_Star_Star_At #f e1 e2 = fexp #f e1 e2

let finv (#f:field) (a:felem f) : felem f = 
  fexp #f a (maxint f.t - 1)
