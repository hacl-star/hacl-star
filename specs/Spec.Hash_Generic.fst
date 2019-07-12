module Spec.Hash_Generic

#set-options "--z3rlimit 25"

private unfold let typ_of_alg (a:algorithm) : Type =
  match a with
  | Blake2S | Blake2B -> Spec.Blake2.alg
  | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 -> Spec.SHA2.alg


inline_for_extraction
private unfold let alg (a:algorithm) : (typ_of_alg a) =
  match a with
  | Blake2S  -> Spec.Blake2.Blake2S
  | Blake2B  -> Spec.Blake2.Blake2B
  | SHA2_224 -> Spec.SHA2.SHA2_224
  | SHA2_256 -> Spec.SHA2.SHA2_256
  | SHA2_384 -> Spec.SHA2.SHA2_384
  | SHA2_512 -> Spec.SHA2.SHA2_512

let state (a:algorithm) =
  match a with
  | Blake2S  -> Spec.Blake2.hash_ws Spec.Blake2.Blake2S
  | Blake2B  -> Spec.Blake2.hash_ws Spec.Blake2.Blake2B
  | SHA2_224 -> Spec.SHA2.hash_w Spec.SHA2.SHA2_224
  | SHA2_256 -> Spec.SHA2.hash_w Spec.SHA2.SHA2_256
  | SHA2_384 -> Spec.SHA2.hash_w Spec.SHA2.SHA2_384
  | SHA2_512 -> Spec.SHA2.hash_w Spec.SHA2.SHA2_512

let init (a:algorithm) hlen =
  match a with
  | Blake2S | Blake2B -> Spec.Blake2.blake2_init (alg a) 0 (Lib.Sequence.create 0 (u8 0)) hlen
  | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 -> Spec.SHA2.init (alg a)

let update_block (a:algorithm) prev block chash =
  match a with
  | Blake2S | Blake2B -> Spec.Blake2.blake2_update_block (alg a) prev block chash
  | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 -> Spec.SHA2.update_block (alg a) block chash

let update_last (a:algorithm) prev len last chash =
  match a with
  | Blake2S | Blake2B -> Spec.Blake2.blake2_update_last (alg a) prev len last chash
  | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 -> Spec.SHA2.update_last (alg a) prev len last chash

let finish (a:algorithm) chash hlen =
  match a with
  | Blake2S | Blake2B -> Spec.Blake2.blake2_finish (alg a) chash hlen
  | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 -> Spec.SHA2.finish (alg a) chash

let hash (a:algorithm) input hlen =
  match a with
  | Blake2S | Blake2B -> Spec.Blake2.blake2 (alg a) input 0 (Lib.Sequence.create 0 (u8 0)) hlen
  | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 -> Spec.SHA2.hash (alg a) input
