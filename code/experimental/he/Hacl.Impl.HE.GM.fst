module Hacl.Impl.HE.GM

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.PrintBuffer

module S = Hacl.Spec.HE.GM

inline_for_extraction noextract
let lbytes (len : size_t) = lbuffer uint8 len

inline_for_extraction noextract
let lbignum (len : size_t) = lbuffer uint64 len
