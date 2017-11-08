module Spec.Lib.Stateful2
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq

type allocator 's = unit -> 's
noeq type accessor 's 'a = {
  get: 's -> 'a;
  put: 's -> 'a -> 's
}


val stateful (s:Type0) (a:Type0): Type0
val run: allocator 's -> stateful 's 'a -> 'a
val bind: stateful 's 'a -> ('a -> stateful 's 'b) -> stateful 's 'b
val loop: min:size_t -> max:size_t{min <= max} -> f:(i:size_t{i >= min /\ i < max} -> stateful 's unit) -> stateful 's unit 
val repeat: n:size_t -> f:stateful 's unit -> stateful 's unit 

val copy: k1:accessor 's 'a -> k2:accessor 's 'a -> stateful 's unit 
val import: ext:'a -> k:accessor 's 'b -> f:('a -> 'b) -> stateful 's unit
val export: k:accessor 's 'a -> (f:'a -> 'b) -> stateful 's 'b

let array_size_t = len:size_t{len > 0}

type array_accessor 's 'a (len:array_size_t) = accessor 's (lseq 'a len)
val read: #len:array_size_t -> k:array_accessor 's 'a len -> i:size_t{i < len} -> stateful 's 'a
val write: #len:array_size_t -> k:array_accessor 's 'a len -> i:size_t{i < len} -> v:'a -> stateful 's unit
val foreach: #len:array_size_t -> k:array_accessor 's 'a len -> f:(i:size_t{i < len} -> 'a -> stateful 's unit) -> stateful 's unit
val foreach_slice: #len:array_size_t -> k:array_accessor 's 'a len -> slen:array_size_t{len % slen = 0} -> f:(i:size_t{i < len/slen} -> lseq 'a slen -> stateful 's unit) -> stateful 's unit
val in_place_map2: #len:array_size_t -> k1:array_accessor 's 'a len -> k2:array_accessor 's 'b len -> f:('a -> 'b -> 'b) -> stateful 's unit
val import_slice: #len:array_size_t -> #slice_len:array_size_t -> ext:lseq 'a slice_len -> k:array_accessor 's 'b len -> min:size_t -> max:size_t{min <= max /\ max <= len} -> f:(lseq 'a slice_len -> lseq 'b (max - min)) -> stateful 's unit






