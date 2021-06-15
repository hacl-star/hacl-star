module Hacl.Spec.EC.Definition

open Lib.IntTypes
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.Sequence
open FStar.Mul

open Spec.ECC.Curves
open FStar.Math.Lemmas

#set-options " --z3rlimit 100"


open Lib.Buffer

inline_for_extraction
let felem (c: curve) = lbuffer uint64 (getCoordinateLenU64 c)

inline_for_extraction 
let widefelem (c: curve) = lbuffer uint64 (getCoordinateLenU64 c *! 2ul)

inline_for_extraction
type point (c: curve) = lbuffer uint64 (getCoordinateLenU64 c *! 3ul)

inline_for_extraction
type pointAffine (c: curve) = lbuffer uint64 (getCoordinateLenU64 c *! 2ul)

