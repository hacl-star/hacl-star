module Vale.AsLowStar.Signature

module B = LowStar.Buffer
module BV = LowStar.BufferView
module HS = FStar.HyperStack
module ME = X64.Memory
module IS = X64.Interop_s
module V = X64.Vale.Decls
module IA = Interop_assumptions
module VS = X64.Vale.State

(* This will grow as we add:
      - confidentiality tags
      - number of stack slots
      - which buffers are modified
*)
let sig = l:list IS.vale_type
let sig_arity_ok = l:sig{List.length l < IS.max_arity IA.win}
