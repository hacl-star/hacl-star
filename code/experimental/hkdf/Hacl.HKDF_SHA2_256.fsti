module Hacl.HKDF_SHA2_256

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.LoopCombinators

module ST = FStar.HyperStack.ST
module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators


inline_for_extraction noextract
let a = Spec.Hash.Definitions.SHA2_256



val hkdf_extract:
    output: buffer uint8{length output == Spec.Hash.Definitions.hash_length a}
  -> salt: buffer uint8 {length salt <= Spec.Hash.Definitions.max_input_length a}
  -> slen: size_t{v slen == length salt}
  -> ikm: buffer uint8
  -> ilen: size_t{ v ilen == length ikm
                /\ length salt + length ikm + Spec.Hash.Definitions.block_length a <= Spec.Hash.Definitions.max_input_length a
                /\ Spec.Hash.Definitions.hash_length a + length ikm + Spec.Hash.Definitions.block_length a <= Spec.Hash.Definitions.max_input_length a} ->
  Stack unit
  (requires (fun h -> live h output /\ live h salt /\ live h ikm
                 /\ disjoint output salt /\ disjoint output ikm))
  (ensures  (fun h0 _ h1 -> modifies1 output h0 h1))



val hkdf_expand:
    output: buffer uint8
  -> prk: buffer uint8
  -> plen: size_t{v plen == length prk /\ length prk + Spec.Hash.Definitions.block_length a < max_size_t}
  -> info: buffer uint8
  -> ilen: size_t{ v ilen == length info
                /\ length info + Spec.Hash.Definitions.hash_length a +
		  Spec.Hash.Definitions.block_length a + 1 < max_size_t
                /\ length prk + length info + 1 + Spec.Hash.Definitions.hash_length a + Spec.Hash.Definitions.block_length a <= Spec.Hash.Definitions.max_input_length a}
  -> len: size_t{ v len == length output
               /\ v len + Spec.Hash.Definitions.hash_length a <= max_size_t
               /\ v len / (Spec.Hash.Definitions.hash_length a) + 2 <= 255} ->
  Stack unit
  (requires (fun h -> live h output /\ live h prk /\ live h info
                 /\ disjoint output prk /\ disjoint output info))
  (ensures  (fun h0 _ h1 -> modifies1 output h0 h1))

val hkdf_build_label:
    output: buffer uint8
  -> secret: buffer uint8
  -> label: buffer uint8
  -> llen: size_t{length label == v llen}
  -> context: buffer uint8
  -> clen: size_t{length context == v clen}
  -> len: size_t{numbytes U16 + numbytes U8 + v llen + numbytes U8 + v clen <= max_size_t /\
    length output >= numbytes U16 + numbytes U8 + v llen + numbytes U8 + v clen /\
    v len < maxint U16
  } ->
  Stack unit
  (requires (fun h -> live h secret /\ live h label /\ live h context /\ live h output /\
    disjoint output label /\ disjoint output context
  ))
  (ensures  (fun h0 _ h1 -> modifies1 output h0 h1))


val hkdf_expand_label:
    output: buffer uint8
  -> secret: lbuffer uint8 (size 32)
  -> label: buffer uint8
  -> llen: size_t{length label == v llen}
  -> context: buffer uint8
  -> clen: size_t{length context == v clen}
  -> len: size_t{numbytes U16 + numbytes U8 + v llen + numbytes U8 + v clen + v len +
    Spec.Hash.Definitions.hash_length a + 1 + Spec.Hash.Definitions.block_length a < max_size_t /\
    length output == v len /\ v len < maxint U16 /\
    v len / (Spec.Hash.Definitions.hash_length a) + 2 <= 255
  } ->
  Stack unit
  (requires (fun h -> live h output /\ live h secret /\ live h label /\ live h context /\
    disjoint output secret /\ disjoint output label /\ disjoint output context
  ))
  (ensures  (fun h0 _ h1 -> modifies1 output h0 h1))
