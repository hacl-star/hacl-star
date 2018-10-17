module Hacl.Impl.Frodo.KEM

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer
open LowStar.BufferOps

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Matrix
open Hacl.Impl.Frodo.Params
open Hacl.Impl.Frodo.Encode
open Hacl.Impl.Frodo.Pack
open Hacl.Impl.Frodo.Sample
open Hacl.Frodo.Random
open Hacl.Frodo.Clear

module ST = FStar.HyperStack.ST
module Lemmas = Spec.Frodo.Lemmas
module S = Spec.Frodo.KEM
module M = Spec.Matrix
module LSeq = Lib.Sequence

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

let bytes_mu :r:size_t{v r == S.bytes_mu} =
  normalize_term (params_extracted_bits *! params_nbar *! params_nbar /. size 8)

let crypto_publickeybytes :r:size_t{v r == S.crypto_publickeybytes} =
  normalize_term (bytes_seed_a +! params_logq *! params_n *! params_nbar /. size 8)

let crypto_secretkeybytes :r:size_t{v r == S.crypto_secretkeybytes} =
  assert_norm (v crypto_bytes + v crypto_publickeybytes + 2 * v params_n * v params_nbar <= max_size_t);
  normalize_term (crypto_bytes +! crypto_publickeybytes +! size 2 *! params_n *! params_nbar)

let crypto_ciphertextbytes :r:size_t{v r == S.crypto_ciphertextbytes} =
  normalize_term ((params_nbar *! params_n +! params_nbar *! params_nbar) *! params_logq /. size 8 +! crypto_bytes)

inline_for_extraction noextract
val clear_matrix:
    #n1:size_t
  -> #n2:size_t{v n1 * v n2 <= max_size_t /\ v n1 * v n2 % 2 = 0}
  -> m:matrix_t n1 n2
  -> Stack unit
    (requires fun h -> live h m)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer m) h0 h1)
let clear_matrix #n1 #n2 m =
  clear_words_u16 (n1 *! n2) m
