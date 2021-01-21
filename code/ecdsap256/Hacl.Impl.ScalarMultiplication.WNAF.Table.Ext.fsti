module Hacl.Impl.ScalarMultiplication.WNAF.Table.Ext	

open FStar.HyperStack
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

open FStar.Mul


val getUInt64: index: size_t {v index < 3456 - 4} -> Stack (lbuffer uint64 (size 4))
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> modifies0 h0 h1)
