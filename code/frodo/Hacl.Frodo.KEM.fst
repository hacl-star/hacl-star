module Hacl.Frodo.KEM

open FStar.HyperStack
open FStar.HyperStack.ST

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Matrix
open Hacl.Impl.Frodo.Params
open Hacl.Impl.Frodo.KEM
open Hacl.Frodo.Random

module S = Spec.Frodo.KEM

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val crypto_kem_keypair:
    pk:lbytes crypto_publickeybytes
  -> sk:lbytes crypto_secretkeybytes
  -> Stack uint32
    (requires fun h ->
      live h pk /\ live h sk /\
      disjoint pk sk /\ disjoint state pk /\ disjoint state sk)
    (ensures  fun h0 r h1 ->
      modifies (loc state |+| (loc pk |+| loc sk)) h0 h1 /\
      (as_seq h1 pk, as_seq h1 sk) == S.crypto_kem_keypair (as_seq h0 state))
let crypto_kem_keypair pk sk =
  Hacl.Impl.Frodo.KEM.KeyGen.crypto_kem_keypair pk sk

val crypto_kem_enc:
    ct:lbytes crypto_ciphertextbytes
  -> ss:lbytes crypto_bytes
  -> pk:lbytes crypto_publickeybytes
  -> Stack uint32
    (requires fun h ->
      live h ct /\ live h ss /\ live h pk /\
      disjoint ct ss /\ disjoint ct pk /\ disjoint ss pk /\
      disjoint state ct /\ disjoint state ss /\ disjoint state pk)
    (ensures  fun h0 _ h1 ->
      modifies (loc state |+| (loc ct |+| loc ss)) h0 h1 /\
      (as_seq h1 ct, as_seq h1 ss) == S.crypto_kem_enc (as_seq h0 state) (as_seq h0 pk))
let crypto_kem_enc ct ss pk =
  Hacl.Impl.Frodo.KEM.Encaps.crypto_kem_enc ct ss pk

val crypto_kem_dec:
    ss:lbytes crypto_bytes
  -> ct:lbytes crypto_ciphertextbytes
  -> sk:lbytes crypto_secretkeybytes
  -> Stack uint32
    (requires fun h ->
      live h ss /\ live h ct /\ live h sk /\
      disjoint ss ct /\ disjoint ss sk /\ disjoint ct sk)
    (ensures  fun h0 r h1 ->
      modifies1 ss h0 h1 /\
      as_seq h1 ss == S.crypto_kem_dec (as_seq h0 ct) (as_seq h0 sk))
let crypto_kem_dec ss ct sk =
  Hacl.Impl.Frodo.KEM.Decaps.crypto_kem_dec ss ct sk
