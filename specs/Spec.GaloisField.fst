module Spec.GaloisField
open Lib.IntTypes
open Lib.Sequence
open Lib.LoopCombinators
open Lib.ByteSequence

(* We represent GF(2^n) by uint_t along  with some  irreducible polynomial also of type uint_t *)
(* Consequently this module is specialized for GF(8/16/32/64/128) but can be generalized to other sizes if needed *)

#set-options "--z3rlimit 30 --max_fuel 0 --max_ifuel 0"

noeq type field =
  | GF: t:inttype{unsigned t /\ t <> U1} -> irred: uint_t t SEC -> field

let gf t irred = GF t irred
type felem (f:field) = uint_t f.t SEC
let to_felem (#f:field) (n:nat{n <= maxint f.t}) : felem f = uint #f.t #SEC n
let from_felem (#f:field) (e:felem f) : n:nat{n <= maxint f.t} = uint_v #f.t #SEC e

let zero (#f:field) : felem f = to_felem 0
let one (#f:field) : felem f = to_felem 1

let load_felem_be (#f:field) (b:lbytes (numbytes f.t)) : felem f = uint_from_bytes_be #f.t #SEC b
let store_felem_be (#f:field) (e:felem f): lbytes (numbytes f.t) = uint_to_bytes_be #f.t #SEC e

let reverse (#t:inttype{unsigned t}) (a:uint_t t SEC) : uint_t t SEC =
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

val get_ith_bit: #f:field -> x:felem f -> i:nat{i < bits f.t} ->
  Tot (r:felem f{v r == v x / pow2 (bits f.t - 1 - i) % 2})
let get_ith_bit #f x i =
  logand_mask (x >>. size (bits f.t - 1 - i)) one 1;
  (x >>. size (bits f.t - 1 - i)) &. one

val mask_add: #f:field -> x:felem f -> y:felem f -> res:felem f -> i:nat{i < bits f.t} ->
  Tot (r:felem f{r == (if v (get_ith_bit x i) = 1 then res `fadd` y else res)})
let mask_add #f x y res i =
  logxor_lemma res zero;
  res `fadd` (y &. eq_mask #f.t (get_ith_bit x i) one)

val mask_shift_right_mod: #f:field -> y:felem f ->
  Tot (r:felem f{r == (if v (get_ith_bit y (bits f.t - 1)) = 1 then (y >>. 1ul) `fadd` f.irred else (y >>. 1ul))})
let mask_shift_right_mod #f y =
  logxor_lemma (y >>. 1ul) zero;
  (y >>. 1ul) `fadd` (f.irred &. eq_mask #f.t (get_ith_bit y (bits f.t - 1)) one)


val fmul_be_f: #f:field -> x:felem f -> i:nat{i < bits f.t} -> res_y:tuple2 (felem f) (felem f) -> felem f & felem f
let fmul_be_f #f x i (res, y) =
  let res = mask_add x y res i in
  let y = mask_shift_right_mod y in
  (res, y)


let fmul_be (#f:field) (x:felem f) (y:felem f) : felem f =
  let (res, y) = repeati (bits f.t) (fmul_be_f x) (zero, y) in
  res

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
