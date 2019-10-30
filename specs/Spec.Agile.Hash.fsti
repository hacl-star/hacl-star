module Spec.Agile.Hash

module S = FStar.Seq

include Spec.Hash.Definitions
open Spec.Hash.PadFinish

val init (a:hash_alg): init_t a
val update (a:hash_alg): update_t a

(* A helper that deals with the modulo proof obligation to make things go smoothly. *)
val split_block (a: hash_alg)
  (blocks: bytes_blocks a)
  (n: nat{n <= S.length blocks / block_length a}):
  Tot (p:(Spec.Hash.Definitions.bytes_blocks a * Spec.Hash.Definitions.bytes_blocks a)
         {fst p == fst (Seq.split blocks (FStar.Mul.(n * block_length a))) /\
	  snd p == snd (Seq.split blocks (FStar.Mul.(n * block_length a)))})

val update_multi (a:hash_alg) (hash:words_state a) (blocks:bytes_blocks a):
  Tot (words_state a) (decreases (S.length blocks))

val hash (a:hash_alg) (input:bytes{S.length input <= max_input_length a}):
  Tot (hash:Lib.ByteSequence.lbytes (hash_length a))
