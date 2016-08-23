module Hacl.SBuffer

open FStar.UInt32
open FStar.HyperHeap
open FStar.HyperStack
open FStar.HST
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
let live = live

(* let getValue = getValue *)
let get = get
let as_seq = as_seq
let equal = equal

(* y is included in x / x contains y *)
let includes = includes

let disjoint = disjoint

(* Abstraction of buffers of any type *)
let modifies_0 = modifies_0

let modifies_1 = modifies_1

let modifies_2 = modifies_2

let modifies_region = modifies_region

let create #t a len = create #t a len
let index #t b i = index #t b i
let upd #t b i v = upd #t b i v
let sub #t b x y = sub #t b x y
let offset #t b i = offset #t b i

let blit (#t:Type) (a:buffer t) aidx (b:buffer t) bidx len = blit a aidx b bidx len
let fill #a = fill #a
