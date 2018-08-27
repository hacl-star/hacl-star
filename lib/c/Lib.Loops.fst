module Lib.Loops

open FStar.HyperStack
open FStar.HyperStack.ST
open Lib.IntTypes

inline_for_extraction
let for start finish inv f = C.Loops.for start finish inv f


