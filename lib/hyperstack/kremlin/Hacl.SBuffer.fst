module Hacl.SBuffer

open FStar.UInt32
open FStar.HyperHeap
open FStar.HyperStack
open FStar.ST
open FStar.Buffer

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

#set-options "--lax"

let s8  = Hacl.UInt8.t
let s32 = Hacl.UInt32.t
let s64 = Hacl.UInt64.t
let s128 = Hacl.UInt128.t

let u32 = FStar.UInt32.t

type buffer (a:Type) = buffer a

type _u8s  = buffer s8
type _u32s = buffer s32
type _u64s = buffer s64
type _u128s = buffer s128

type u8s  = _u8s
type u32s = _u32s
type u64s = _u64s
type u128s = _u128s

let contains = contains
let sel = sel
let max_length = max_length
let length = length
(* let length' = length' *)
let idx  = idx
let content = content
let as_ref = as_ref
let as_aref = as_aref
let frameOf = frameOf

(* Liveness condition, necessary for any computation on the buffer *)
let live #a (h:mem) (b:buffer a) = live #a h b

(* let getValue = getValue *)
let get = get
let as_seq = as_seq
let equal = equal

(* y is included in x / x contains y *)
let includes #a (x:buffer a) (y:buffer a) = includes #a x y

let disjoint #a #a' (x:buffer a) (y:buffer a') = disjoint #a #a' x y

(* Abstraction of buffers of any type *)
let modifies_0 h0 h1 = modifies_0 h0 h1

let modifies_1 (#a:Type) (b:buffer a) h0 h1 = modifies_1 #a b h0 h1

let modifies_2 (#a:Type) (#a':Type) (b:buffer a) (b':buffer a') h0 h1 = modifies_2 #a #a' b b' h0 h1

let modifies_region rid bufs h0 h1 = modifies_region rid bufs h0 h1

inline_for_extraction let create (* #t a len *) = create (* #t a len *)
inline_for_extraction let index (* #t b i *) = index (* #t b i *)
inline_for_extraction let upd (* #t b i v *) = upd
inline_for_extraction let sub (* #t b x y *) = sub (* #t b x y *)
inline_for_extraction let offset (* #t b i *) = offset (* #t b i *)

inline_for_extraction let blit = blit
inline_for_extraction let fill = fill

inline_for_extraction let op_Array_Assignment = op_Array_Assignment
inline_for_extraction let op_Array_Access = op_Array_Access
