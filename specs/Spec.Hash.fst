module Spec.Hash


inline_for_extraction
private let alg (a:algorithm) =
  match a with
  | SHA2_224 -> Spec.SHA2.SHA2_224
  | SHA2_256 -> Spec.SHA2.SHA2_256
  | SHA2_384 -> Spec.SHA2.SHA2_384
  | SHA2_512 -> Spec.SHA2.SHA2_512

let state (a:algorithm) =
  match a with
  | SHA2_224 -> Spec.SHA2.hash_w Spec.SHA2.SHA2_224
  | SHA2_256 -> Spec.SHA2.hash_w Spec.SHA2.SHA2_256
  | SHA2_384 -> Spec.SHA2.hash_w Spec.SHA2.SHA2_384
  | SHA2_512 -> Spec.SHA2.hash_w Spec.SHA2.SHA2_512


let init (a:algorithm) = Spec.SHA2.init (alg a)

let update_block (a:algorithm) block chash = Spec.SHA2.update_block (alg a) block chash

let update_last (a:algorithm) prev len last chash = Spec.SHA2.update_last (alg a) prev len last chash

let finish (a:algorithm) chash = Spec.SHA2.finish (alg a) chash

let hash (a:algorithm) input = Spec.SHA2.hash (alg a) input
