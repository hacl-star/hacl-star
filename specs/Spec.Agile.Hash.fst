module Spec.Agile.Hash

open FStar.Mul

inline_for_extraction
private let alg (a:algorithm) =
  match a with
  | UNSAFE_HASH_MD5 -> Spec.Hash.Definitions.MD5
  | UNSAFE_HASH_SHA1 -> Spec.Hash.Definitions.SHA1
  | HASH_SHA2_224 -> Spec.Hash.Definitions.SHA2_224
  | HASH_SHA2_256 -> Spec.Hash.Definitions.SHA2_256
  | HASH_SHA2_384 -> Spec.Hash.Definitions.SHA2_384
  | HASH_SHA2_512 -> Spec.Hash.Definitions.SHA2_512

let state (a:algorithm) = Spec.Hash.Definitions.words_state (alg a)

let init (a:algorithm) = Spec.Hash.init (alg a)

let update_block (a:algorithm) block chash = Spec.Hash.update (alg a) chash block

let update_last (a:algorithm) prev len last chash = Spec.Hash.Incremental.update_last (alg a) chash prev last

let finish (a:algorithm) chash = Spec.Hash.PadFinish.finish (alg a) chash

let hash (a:algorithm) input =
  assert(Seq.length input < Spec.Hash.Definitions.max_input_length (alg a));
  Spec.Hash.hash (alg a) input
