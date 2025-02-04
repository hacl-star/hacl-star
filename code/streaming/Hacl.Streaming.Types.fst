module Hacl.Streaming.Types

inline_for_extraction // projectors
type error_code =
  | Success
  | InvalidAlgorithm
  | InvalidLength
  | MaximumLengthExceeded
  | OutOfMemory

// Placement of monomorphizations. The types below appear because of the
// streaming functor stateful class, which now accounts for allocation failures.
// We must i) find the right monomorphization to give it a name and ii) make
// sure there's a dependency arrow towards the definitions below (so that they
// appear *before* their actual uses) and iii) make sure these are not
// eliminated.

/// Part iii) is achieved via bundling (this file in on the left-hand side).

// This is a good place to put monomorphizations in because this file appears
// *before* all streaming instances.

let optional_32 = option (LowStar.Buffer.buffer UInt32.t)
let optional_64 = option (LowStar.Buffer.buffer UInt64.t)
let optional_unit = option unit

let two_pointers = LowStar.Buffer.(buffer UInt64.t & buffer UInt64.t)
