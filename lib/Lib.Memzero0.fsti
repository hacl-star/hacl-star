/// Separate module that does not depend on Lib.Buffer to avoid a dependency loop.
module Lib.Memzero0

module B = LowStar.Buffer

/// This variant is polymorphic and is implemented in C.
val memzero: #a:Type0 -> b:B.buffer a -> l:UInt32.t { B.len b == l } -> FStar.HyperStack.ST.Stack unit
  (requires fun h -> B.live h b)
  (ensures fun h0 _ h1 -> B.(modifies (loc_buffer b) h0 h1))
