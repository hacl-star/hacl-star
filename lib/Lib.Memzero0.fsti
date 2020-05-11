/// Separate module that does not depend on Lib.Buffer to avoid a dependency loop.
module Lib.Memzero0

module B = LowStar.Buffer

/// This variant is polymorphic and extracts to a call to hacl_memzero to be
/// found in lib/c/hacl_memzero.h -- if your final bundle (named Foo.c) contains
/// a call to the function below, make sure you pass ``-include
/// 'Foo:"hacl_memzero.h"'`` to kremlin.
///
/// DO NOT mark as inline_for_extraction!
val memzero: #a:Type0 -> b:B.buffer a -> l:UInt32.t { B.len b == l } -> FStar.HyperStack.ST.Stack unit
  (requires fun h -> B.live h b)
  (ensures fun h0 _ h1 -> B.(modifies (loc_buffer b) h0 h1))
