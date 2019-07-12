module Lib.Loops

open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.RawIntTypes

let for start finish inv f =
  C.Loops.for
    (size_to_UInt32 start)
    (size_to_UInt32 finish)
    (fun h i -> v start <= i /\ i <= v finish /\ inv h i)
    (fun i -> f (size_from_UInt32 i))
