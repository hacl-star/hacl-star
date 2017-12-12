module Spec.Lib.Stateful
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq

noeq type state_def =
  | StateDef: state: Type0 ->
	      key:Type0 ->
	      value:(key->Type0) ->
	      length:(key->size_nat) ->
	      create:(unit -> state) ->
	      get:(state -> k:key -> lseq (value k) (length k)) ->
	      put:(state -> k:key -> lseq (value k) (length k) -> state) ->
	      state_def

unfold
let state_index (d:state_def) (k:d.key) = s:size_nat{s < d.length k}
unfold
let state_seq (d:state_def) (k:d.key) : Type0 = lseq (d.value k) (d.length k)
unfold
let state_slice (d:state_def) (k:d.key) (min:size_nat) (max:size_nat{min <= max}) : Type0 = lseq (d.value k) (max - min)


val stateful (d:state_def) (a:Type0) : Type0

val alloc: #a:Type0 -> #d:state_def -> f:stateful d a -> a

val read: #d:state_def -> k:d.key -> x:state_index d k -> stateful d (d.value k)
val write: #d:state_def -> k:d.key -> x:state_index d k -> v:d.value k -> stateful d unit
val return: #a:Type0 -> #d:state_def -> x:a -> stateful d a
val bind: #a:Type0 -> #b:Type0 -> #d:state_def -> f:stateful d a -> g:(a -> stateful d b) -> stateful d b

(* Convenience functions, can be implemented using read/write and repeat_range *)

val repeat_stateful: #d:state_def -> n:size_nat -> f:stateful d unit -> stateful d unit
val repeat_range_stateful: #d:state_def -> min:size_nat -> max:size_nat{min <= max} -> f:(i:size_nat{i >= min /\ i < max} -> stateful d unit) -> stateful d unit
val copy: #d:state_def -> k1:d.key -> k2:d.key{d.value k1 == d.value k2 /\ d.length k1 == d.length k2} -> stateful d unit
val in_place_map2: #d:state_def -> k1:d.key -> k2:d.key{d.value k1 == d.value k2 /\ d.length k1 == d.length k2} -> f:(d.value k1 -> d.value k2 -> d.value k2) -> stateful d unit
val import: #a:Type0 -> #len:size_nat -> #d:state_def -> lseq a len -> k:d.key -> f:(lseq a len -> state_seq d k) -> stateful d unit
val import_slice: #a:Type0 -> #len:size_nat -> #d:state_def -> lseq a len -> k:d.key -> min:size_nat -> max:size_nat{min <= max /\ max <= d.length k} -> f:(lseq a len -> state_slice d k min max) -> stateful d unit

val export: #a:Type0 -> #len:size_nat -> #d:state_def -> k:d.key -> f:(state_seq d k -> lseq a len) -> stateful d (lseq a len)
