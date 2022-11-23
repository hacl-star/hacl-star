module Spec.Agile.Hash

module S = FStar.Seq

include Spec.Hash.Definitions
open Spec.Hash.PadFinish
open FStar.Mul

(** Hashes, agility, incrementality, streaming, and hash laws.

For various historical reasons, this module serves two purposes.
- For Merkle-Damgård algorithms (MD5, SHA1, SHA2), this module acts as a
  *definitional* specification. This *is* the spec of the MD algorithms, and
  low-level implementations (at least, historically) we shown to refine this
  specification.
- For non-MD algorithms (Blake2, SHA3), this module serves a different purpose:
  it shows that Blake2 and SHA3 obey the hash laws (more on that below), and
  that therefore they can be suitably interpreted as behaving like hash
  algorithms in this agile specification. The agile hash therefore obeys the
  hash laws, because every algorithm does.

This agile specification, in addition to establishing the high-level property that
"all hash algorithms behave like hashes" (i.e., obey the hash laws), serves as
a specification of the agile, multiplexing hash known as EverCrypt.Hash.

The hash laws are as follows.
- Any hash algorithm can be decomposed into an *incremental* specification,
  relying on: init, update_multi, update_last, finish. (The MD hashes
  specifically decompose update_last as padding + update but this is not
  generally true of all hashes.) See
  Spec.Hash.Incremental.Definitions.hash_incremental, along with the various
  proofs in Spec.Hash.Incremental.X that algorithm X is equivalent to its
  incremental specification.
- The update_multi function, which processes n full blocks into the internal
  hash state (also known as the accumulator, borrowing from functional
  programming terminology for folds), takes the empty input as its neutral element.
  Concretely:
    update_multi acc empty == acc
- The update_multi function is associative. Concretely:
    update_multi (update_multi acc blocks) blocks' == update_multi acc (blocks @ blocks')

Proving the three hash laws is important: they are needed by the streaming
functor (which turns a block-by-block implementation into a buffered
implementation that can take arbitrary amounts of data) for functional
correctness.

(In the case of MD hashes, the proof of incrementality specifically relies on
the two properties of update_multi, but this is not true in the general case.)
*)

val init (a:hash_alg): init_t a

(* The individual update function. This is an implementation detail, and clients
should reason in terms of update_multi to be fully agile. None of the hash laws
refer to update. *)
val update (a:md_alg): update_t a

(* Because of blake2, we unfortunately have this precondition creeping up. *)
let update_multi_pre
  (a:hash_alg)
  (hash:words_state a)
  (prev:nat)
  (blocks:bytes)
=
  match a with
  | Blake2B | Blake2S ->
      (S.length blocks + prev) `less_than_max_input_length` a
  | _ -> true

(* Agile multi-block processing function shown to obey the hash laws. *)
val update_multi
  (a:hash_alg)
  (hash:words_state a)
  (prev:nat)
  (blocks:bytes_blocks a):
  Pure (words_state a)
    (requires update_multi_pre a hash prev blocks)
    (ensures fun _ -> True)

val hash (a:hash_alg) (input:bytes{S.length input `less_than_max_input_length` a}):
  Tot (Lib.ByteSequence.lbytes (hash_length a))
