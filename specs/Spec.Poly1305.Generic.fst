module Spec.Poly1305.Generic

#reset-options "--z3rlimit 60 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.RawIntTypes
open Spec.Lib.IntSeq
open Spec.Poly1305.Lemmas

noeq type finite_field (bits:size_nat) = 
  | MkFF: elem:Type0 -> 
	  to_elem: (n:nat{n < pow2 bits} -> e:elem) ->
	  from_elem: (e:elem -> n:nat{n < pow2 bits}) ->
//	  bytes_to_elem: (b:bytes{8 * length b < pow2 bits} -> e:elem) ->
//	  bytes_from_elem: (e:elem -> b:bytes{8 * length b < pow2 bits}) ->
	  zero:elem ->
	  add: (e1:elem -> e2:elem -> e3:elem) ->
	  mul: (e1:elem -> e2:elem -> e3:elem) ->
	  finite_field bits

(* Poly1305 parameters *)
let blocksize : size_nat = 16
let keysize   : size_nat = 32
type block = lbytes blocksize
type tag   = lbytes blocksize
type key   = lbytes keysize


noeq type state (ff:finite_field 130) = {
  r:ff.elem;
  s:uint128;
  acc:ff.elem
}

let set_acc #ff (st:state ff) (acc:ff.elem) =
  {st with acc = acc}

(* Poly1305 specification *)
let update1 #ff (len:size_nat{len <= blocksize}) (b:lbytes len) (st:state ff) : state ff =
  Math.Lemmas.pow2_le_compat 128 (8 * len);
  assert (pow2 (8 * len) <= pow2 128);
  Math.Lemmas.pow2_lt_compat 130 (8 * len);
  assert (pow2 (8 * len) < pow2 130);
  let n = ff.add (ff.to_elem (pow2 (8 * len))) (ff.to_elem (nat_from_bytes_le b)) in
  let acc = ff.mul (ff.add n st.acc) st.r in
  set_acc st acc
  

let update_blocks #ff (n:size_nat{n * blocksize <= max_size_t}) (text:lbytes (n * blocksize)) (st:state ff) : state ff =
  reduce_blocks blocksize n (fun i -> update1 16) text st

let poly #ff (len:size_nat) (text:lbytes len) (st:state ff) : state ff =
  let n = len / blocksize in
  let rem = len % blocksize in
  let blocks = slice text 0 (n * blocksize) in
  let st = update_blocks n blocks st in
  if rem = 0 then st
  else
    let last = slice text (n * blocksize) len in
    update1 rem last st

let finish #ff (st:state ff) : tag =
  let n = u128(ff.from_elem st.acc) +. st.s in
  uint_to_bytes_le n

let encode_r (#ff:finite_field 130) (rb:block) : ff.elem =
  let (&.) = logand #U8 in
  let rb = rb.[3] <- rb.[3] &. u8 15 in
  let rb = rb.[7] <- rb.[7] &. u8 15 in
  let rb = rb.[11] <- rb.[11] &. u8 15 in
  let rb = rb.[15] <- rb.[15] &. u8 15 in
  let rb = rb.[4] <- rb.[4] &. u8 252 in
  let rb : lseq uint8 16 = rb.[8] <- rb.[8] &. u8 252 in
  let rb : lseq uint8 16 = rb.[12] <- rb.[12] &. u8 252 in
  Math.Lemmas.pow2_lt_compat 130 128;
  ff.to_elem (nat_from_bytes_le rb)

let poly1305_init #ff (k:key) : state ff =
  let r = encode_r (slice k 0 16) in
  Math.Lemmas.pow2_lt_compat 130 128;
  let s = u128 (nat_from_bytes_le (slice k 16 32)) in
  {r = r; s = s; acc = ff.zero}

let poly1305_generic (#ff:finite_field 130) (len:size_nat) (msg:lbytes len) (k:key) : tag =
  let st = poly1305_init #ff k in
  let st = poly #ff len msg st in
  finish #ff st


(***** HIGH LEVEL SPEC *****)

(* Field types and parameters *)
let prime =  pow2 130 - 5
unfold type elem = nat_mod prime
let to_elem (x:nat) : elem = x `modulo` prime 
let from_elem (x:elem) : n:nat{n < pow2 130} = nat_mod_v #prime x
let zero : elem = to_elem 0

let poly1305_field : finite_field 130 = 
    MkFF elem to_elem from_elem zero (+.) ( *. )

let poly1305 (len:size_nat) (msg:lbytes len) (k:key) : tag =
    poly1305_generic #poly1305_field len msg k

(***** LOW LEVEL 64-bit SPEC *****)

type elem2 = s:lseq uint64 3
let mask44 = (((u64 1) <<. (u32 44)) -. (u64 1)) 
let mask42 = (((u64 1) <<. (u32 42)) -. (u64 1))

let zero2 : elem2 = 
  create 3 (u64 0)

let to_elem2 (n:nat{n < pow2 130}) : elem2 = 
    repeati 3 (fun i acc ->
      acc.[i] <- u64 ((n / pow2 (i * 44)) % pow2 44)) zero2

let from_elem2 (s:elem2) : (n:nat{n < pow2 130}) = 
    repeati 3 (fun i acc ->
      acc + (uint_to_nat s.[i] * pow2 (i * 44))) 0

let add2 (s1:elem2) (s2:elem2) : elem2 = 
  repeati 3 (fun i acc -> acc.[i] <- s1.[i] +. s2.[i]) zero2

[@ Substitute]
inline_for_extraction
let mul_wide44 (a:uint64) (b:uint64) : tuple2 uint64 uint64 = 
  let o = mul_wide a b in
  let l = (to_u64 o) &. mask44 in
  let h = to_u64 (o >>. (u32 44)) in
  (h,l)

let mul2 (s1:elem2) (s2:elem2) : elem2 = 
  let s4 = repeati 3 (fun i acc -> 
       repeati 3 (fun j acc ->
                   let s2j = s2.[(3 + j - i) % 3] in
		   let s2j = if i <= j then s2j else u64 20 *. s2j in
		   let (hij,lij) = mul_wide44 s1.[i] s2j in
		   let acc = acc.[j] <- acc.[j] +. lij in
		   acc.[j+1] <- acc.[j+1] +. hij) acc) (create 4 (u64 0)) in
  let s4 = s4.[0] <- s4.[0] +. (u64 20 *. s4.[3]) in
  let s4 = repeati 2 (fun i acc ->
			let acc = acc.[i+1] <- acc.[i+1] +. (acc.[i] >>. (u32 44)) in
			acc.[i] <- acc.[i] &. mask44) s4 in
  let carry2 = s4.[2] >>. (u32 42) in
  let s4 = s4.[2] <- s4.[2] &. mask42 in
  let s4 = s4.[0] <- s4.[0] +. (u64 5 *. carry2) in
  let s4 = repeati 2 (fun i acc ->
			let acc = acc.[i+1] <- acc.[i+1] +. (acc.[i] >>. (u32 44)) in
			acc.[i] <- acc.[i] &. mask44) s4 in
  slice s4 0 3
  
let poly1305_field2 : finite_field 130 = 
  MkFF elem2 to_elem2 from_elem2 zero2 add2 mul2

let poly1305_2 (len:size_nat) (msg:lbytes len) (k:key) : tag =
    poly1305_generic #poly1305_field2 len msg k

(***** LOW LEVEL 64-bit SPEC *****)

type elem3 = s:lseq uint32 5
let mask26 = (((u32 1) <<. (u32 26)) -. (u32 1)) 
let zero3 : elem3 = 
  create 5 (u32 0)

let to_elem3 (n:nat{n < pow2 130}) : elem3 = 
    repeati 5 (fun i acc ->
      acc.[i] <- u32 ((n / pow2 (i * 26)) % pow2 26)) zero3

let from_elem3 (s:elem3) : (n:nat{n < pow2 130}) = 
    repeati 5 (fun i acc ->
      acc + (uint_to_nat s.[i] * pow2 (i * 26))) 0

let add3 (s1:elem3) (s2:elem3) : elem3 = 
    repeati 5 (fun i acc -> acc.[i] <- s1.[i] +. s2.[i]) zero3

[@ Substitute]
inline_for_extraction
let mul_wide26 (a:uint32) (b:uint32) : tuple2 uint32 uint32 = 
  let o = (to_u64 a) *. (to_u64 b) in
  let l = (to_u32 o) &. mask26 in
  let h = to_u32 (o >>. (u32 26)) in
  (h,l)

let mul3 (s1:elem3) (s2:elem3) : elem3 = 
  let s6 = repeati 5 (fun i acc -> 
       repeati 5 (fun j acc ->
                   let s2j = s2.[(5 + j - i) % 5] in
		   let s2j = if i <= j then s2j else u32 5 *. s2j in
		   let (hij,lij) = mul_wide26 s1.[i] s2j in
		   let acc = acc.[j] <- acc.[j] +. lij in
		   acc.[j+1] <- acc.[j+1] +. hij) acc) (create 6 (u32 0)) in
  let s6 = s6.[0] <- s6.[0] +. (u32 5 *. s6.[5]) in
  let s6 = s6.[5] <- u32 0 in
  let s6 = repeati 5 (fun i acc ->
			let acc = acc.[i+1] <- acc.[i+1] +. (acc.[i] >>. (u32 26)) in
			acc.[i] <- acc.[i] &. mask26) s6 in
  let s6 = s6.[0] <- s6.[0] +. (u32 5 *. s6.[5]) in
  let s6 = s6.[5] <- u32 0 in

  let s6 = repeati 4 (fun i acc ->
			let acc = acc.[i+1] <- acc.[i+1] +. (acc.[i] >>. (u32 26)) in
			acc.[i] <- acc.[i] &. mask26) s6 in
  slice s6 0 5
  
let poly1305_field3 : finite_field 130 = 
  MkFF elem3 to_elem3 from_elem3 zero3 add3 mul3

let poly1305_3 (len:size_nat) (msg:lbytes len) (k:key) : tag =
    poly1305_generic #poly1305_field3 len msg k
