module Hacl.Impl.Poly1305

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.Poly1305.Fields

#reset-options "--z3rlimit 50"

inline_for_extraction
val poly1305_mac:
    #s:field_spec
  -> tag:lbuffer uint8 16ul
  -> len:size_t
  -> text:lbuffer uint8 len
  -> key:lbuffer uint8 32ul
  -> Stack unit
    (requires fun h -> live h text /\ live h tag /\ live h key)
    (ensures  fun h0 _ h1 -> modifies (loc tag) h0 h1)
