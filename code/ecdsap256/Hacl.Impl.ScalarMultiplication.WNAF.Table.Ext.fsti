module Hacl.Impl.ScalarMultiplication.WNAF.Table.Ext	

open FStar.HyperStack
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

open FStar.Mul


val getUInt64: index: uint64 -> Stack (lbuffer uint64 (size 4))
	(requires fun h -> True)
	(ensures fun h0 _ h1 -> True)