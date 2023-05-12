module Hacl.Streaming.Types

type error_code =
  | Success
  | InvalidAlgorithm
  | InvalidLength
  | MaximumLengthExceeded
