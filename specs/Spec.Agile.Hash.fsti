module Spec.Agile.Hash

module S = FStar.Seq

include Spec.Hash.Definitions
open Spec.Hash.PadFinish
open FStar.Mul

val init (a:hash_alg): init_t a
val update (a:hash_alg): update_t a

val update_multi (a:hash_alg) (hash:words_state a) (blocks:bytes_blocks a):
  Tot (words_state a) (decreases (S.length blocks))

val hash (a:hash_alg) (input:bytes{S.length input <= max_input_length a}):
  Tot (Lib.ByteSequence.lbytes (hash_length a))
