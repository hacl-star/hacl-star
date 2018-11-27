module FastHybrid_helpers

open Words_s
open Types_s
open FStar.Mul
open FStar.Tactics
open CanonCommSemiring
open Fast_defs

let int_canon = fun _ -> canon_semiring int_cr //; dump "Final"

