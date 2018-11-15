module Hacl.Impl.Curve25519.Field64.Core

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.Sequence
open Lib.IntTypes
open Lib.Buffer
open FStar.Mul
module B = Lib.Buffer

let u256 = lbuffer uint64 4ul
let u512 = lbuffer uint64 8ul
let u1024 = lbuffer uint64 16ul

[@ CInline]
val add1: out:u256 -> f1:u256  -> f2:uint64  -> Stack uint64
          (requires (fun h -> live h f1 /\ live h out))
	  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))

[@ CInline]
val fadd: out:u256 -> f1:u256  -> f2:u256  -> Stack unit
          (requires (fun h -> live h f1 /\ live h f2 /\ live h out))
	  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))

[@ CInline]
val fsub: out:u256 ->  f1:u256  -> f2:u256  -> Stack unit
                   (requires (fun h -> live h f1 /\ live h f2 /\ live h out))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 ))

[@ CInline]
val fmul: out:u256 -> f1:u256 -> f2:u256 -> Stack unit
                   (requires (fun h -> live h out /\ live h f1 /\ live h f2))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))


[@ CInline]
val fmul2:
    out:u512
  -> f1:u512
  -> f2:u512
  -> Stack unit
  (requires (fun h -> live h out /\ live h f1 /\ live h f2))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))


[@ CInline]
val fmul1: out:u256 -> f1:u256 -> f2:uint64 -> Stack unit
                   (requires (fun h -> live h out /\ live h f1))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))

[@ CInline]
val fsqr: out:u256 -> f1:u256 -> Stack unit
                   (requires (fun h -> live h out /\ live h f1))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))

[@ CInline]
val fsqr2: out:u512 -> f:u512 -> Stack unit
        (requires (fun h -> live h out /\ live h f))
	(ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
