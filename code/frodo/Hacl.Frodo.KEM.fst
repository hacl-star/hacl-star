module Hacl.Frodo.KEM

open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Matrix
open Hacl.Impl.Frodo.Params
open Hacl.Impl.Frodo.KEM
open Hacl.Frodo.Random

module S = Spec.Frodo.KEM
module FP = Spec.Frodo.Params

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let crypto_kem_keypair_st (a:FP.frodo_alg) (gen_a:FP.frodo_gen_a{is_supported gen_a}) =
    pk:lbytes (crypto_publickeybytes a)
  -> sk:lbytes (crypto_secretkeybytes a)
  -> Stack uint32
    (requires fun h ->
      live h pk /\ live h sk /\
      disjoint pk sk /\ disjoint state pk /\ disjoint state sk)
    (ensures  fun h0 r h1 -> modifies (loc state |+| (loc pk |+| loc sk)) h0 h1 /\
      (as_seq h1 pk, as_seq h1 sk) == S.crypto_kem_keypair a gen_a (as_seq h0 state))


inline_for_extraction noextract
val crypto_kem_keypair: a:FP.frodo_alg -> gen_a:FP.frodo_gen_a{is_supported gen_a} -> crypto_kem_keypair_st a gen_a
let crypto_kem_keypair a gen_a pk sk =
  Hacl.Impl.Frodo.KEM.KeyGen.crypto_kem_keypair a gen_a pk sk


inline_for_extraction noextract
let crypto_kem_enc_st (a:FP.frodo_alg) (gen_a:FP.frodo_gen_a{is_supported gen_a}) =
    ct:lbytes (crypto_ciphertextbytes a)
  -> ss:lbytes (crypto_bytes a)
  -> pk:lbytes (crypto_publickeybytes a)
  -> Stack uint32
    (requires fun h ->
      live h ct /\ live h ss /\ live h pk /\
      disjoint ct ss /\ disjoint ct pk /\ disjoint ss pk /\
      disjoint state ct /\ disjoint state ss /\ disjoint state pk)
    (ensures  fun h0 _ h1 -> modifies (loc state |+| (loc ct |+| loc ss)) h0 h1 /\
      (as_seq h1 ct, as_seq h1 ss) == S.crypto_kem_enc a gen_a (as_seq h0 state) (as_seq h0 pk))


inline_for_extraction noextract
val crypto_kem_enc: a:FP.frodo_alg -> gen_a:FP.frodo_gen_a{is_supported gen_a} -> crypto_kem_enc_st a gen_a
let crypto_kem_enc a gen_a ct ss pk =
  Hacl.Impl.Frodo.KEM.Encaps.crypto_kem_enc a gen_a ct ss pk


inline_for_extraction noextract
let crypto_kem_dec_st (a:FP.frodo_alg) (gen_a:FP.frodo_gen_a{is_supported gen_a}) =
    ss:lbytes (crypto_bytes a)
  -> ct:lbytes (crypto_ciphertextbytes a)
  -> sk:lbytes (crypto_secretkeybytes a)
  -> Stack uint32
    (requires fun h ->
      live h ss /\ live h ct /\ live h sk /\
      disjoint ss ct /\ disjoint ss sk /\ disjoint ct sk)
    (ensures  fun h0 r h1 -> modifies (loc ss) h0 h1 /\
      as_seq h1 ss == S.crypto_kem_dec a gen_a (as_seq h0 ct) (as_seq h0 sk))


inline_for_extraction noextract
val crypto_kem_dec: a:FP.frodo_alg -> gen_a:FP.frodo_gen_a{is_supported gen_a} -> crypto_kem_dec_st a gen_a
let crypto_kem_dec a gen_a ss ct sk =
  Hacl.Impl.Frodo.KEM.Decaps.crypto_kem_dec a gen_a ss ct sk
