module Spec.Agile.Hash


inline_for_extraction
private let alg (a:algorithm) =
  match a with
  | HASH_SHA2_224 -> Spec.SHA2.Normal.SHA2_224
  | HASH_SHA2_256 -> Spec.SHA2.Normal.SHA2_256
  | HASH_SHA2_384 -> Spec.SHA2.Normal.SHA2_384
  | HASH_SHA2_512 -> Spec.SHA2.Normal.SHA2_512

let state (a:algorithm) =
  match a with
  | HASH_SHA2_224 -> Spec.SHA2.Normal.hash_w Spec.SHA2.Normal.SHA2_224
  | HASH_SHA2_256 -> Spec.SHA2.Normal.hash_w Spec.SHA2.Normal.SHA2_256
  | HASH_SHA2_384 -> Spec.SHA2.Normal.hash_w Spec.SHA2.Normal.SHA2_384
  | HASH_SHA2_512 -> Spec.SHA2.Normal.hash_w Spec.SHA2.Normal.SHA2_512


let init (a:algorithm) = Spec.SHA2.Normal.init (alg a)

let update_block (a:algorithm) block chash = Spec.SHA2.Normal.update_block (alg a) block chash

let update_last (a:algorithm) prev len last chash = Spec.SHA2.Normal.update_last (alg a) prev len last chash

let finish (a:algorithm) chash = Spec.SHA2.Normal.finish (alg a) chash

let hash (a:algorithm) input = Spec.SHA2.Normal.hash (alg a) input
