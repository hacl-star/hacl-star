module Spec.Unsafe

open Lib.IntTypes

open FStar.Mul

val unsafe_int64_to_int16: x:Lib.IntTypes.int64 -> y:int16{sint_v y == sint_v x @%. S16}
