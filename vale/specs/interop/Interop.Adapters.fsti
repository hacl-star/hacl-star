module Interop.Adapters
open Interop.Base

module B = LowStar.Buffer
module HS = FStar.HyperStack
module ME = X64.Memory
module MS = X64.Machine_s
module IM = Interop.Mem

[@reduce]
let maybe_cons_buffer (x:arg) (args:list b8) : list b8 =
    match x with
    | (|TD_Buffer _, x|) -> x :: args
    | _ -> args

[@reduce]
let args_b8 (args:list arg) : GTot (list b8) =
  BigOps.foldr_gtot args maybe_cons_buffer []

val liveness_disjointness (args:list arg) (h:mem_roots args)
  : Lemma (IM.list_disjoint_or_eq (args_b8 args) /\
           IM.list_live h (args_b8 args))

val create_valid_memtaint
  (mem:ME.mem)
  (ps:list b8{IM.list_disjoint_or_eq ps})
  (ts:b8 -> GTot MS.taint) :
  GTot ME.memtaint

val mk_mem (args:list arg) (h:mem_roots args) : ME.mem
val hs_of_mem (m:ME.mem) : HS.mem
val ptrs_of_mem (m:ME.mem) : l:list b8{IM.list_disjoint_or_eq l}
