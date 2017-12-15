module Spec.Lib.Loops

open FStar.HyperStack
open FStar.HyperStack.ST
open Spec.Lib.IntTypes

let for start finish inv f = C.Loops.for start finish inv f


