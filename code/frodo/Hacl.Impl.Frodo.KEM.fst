module Hacl.Impl.Frodo.KEM

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.Memzero

open Hacl.Impl.Matrix
open Hacl.Impl.Frodo.Params

module S = Spec.Frodo.Params

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

let bytes_mu :r:size_t{v r == S.bytes_mu} =
  normalize_term (params_extracted_bits *! params_nbar *! params_nbar /. size 8)

let crypto_publickeybytes :r:size_t{v r == S.crypto_publickeybytes} =
  normalize_term (bytes_seed_a +! params_logq *! params_n *! params_nbar /. size 8)

let crypto_secretkeybytes :r:size_t{v r == S.crypto_secretkeybytes} =
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
    (ensures  fun h0 _ h1 -> modifies1 m h0 h1)
let clear_matrix #n1 #n2 m =
  clear_words_u16 (n1 *! n2) m
