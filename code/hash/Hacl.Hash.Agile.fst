module Hacl.Hash.Agile

open Hacl.Hash.Definitions
open Spec.Hash.Definitions

(** A series of static multiplexers that will be useful when building the
    generic Merkle-Damgard construction. *)

inline_for_extraction noextract
let alloca (i:impl): alloca_st i =
  [@inline_let] let a = get_alg i in
  [@inline_let] let m = get_spec i in
  match a with
  | MD5 -> Hacl.Hash.Core.MD5.legacy_alloca
  | SHA1 -> Hacl.Hash.Core.SHA1.legacy_alloca
  | SHA2_224 -> Hacl.Hash.Core.SHA2.alloca_224
  | SHA2_256 -> Hacl.Hash.Core.SHA2.alloca_256
  | SHA2_384 -> Hacl.Hash.Core.SHA2.alloca_384
  | SHA2_512 -> Hacl.Hash.Core.SHA2.alloca_512
  | Blake2S -> Hacl.Hash.Core.Blake2.mk_alloca Blake2S m (Hacl.Hash.Core.Blake2.mk_init Blake2S m)
  | Blake2B -> Hacl.Hash.Core.Blake2.mk_alloca Blake2B m (Hacl.Hash.Core.Blake2.mk_init Blake2B m)

inline_for_extraction noextract
let init (i:impl): init_st i =
  [@inline_let] let a = get_alg i in
  [@inline_let] let m = get_spec i in
  match a with
  | MD5 -> Hacl.Hash.Core.MD5.legacy_init
  | SHA1 -> Hacl.Hash.Core.SHA1.legacy_init
  | SHA2_224 -> Hacl.Hash.Core.SHA2.init_224
  | SHA2_256 -> Hacl.Hash.Core.SHA2.init_256
  | SHA2_384 -> Hacl.Hash.Core.SHA2.init_384
  | SHA2_512 -> Hacl.Hash.Core.SHA2.init_512
  | Blake2S -> Hacl.Hash.Core.Blake2.mk_init Blake2S m
  | Blake2B -> Hacl.Hash.Core.Blake2.mk_init Blake2B m


inline_for_extraction noextract
let update (i:impl): update_st i =
  [@inline_let] let a = get_alg i in
  [@inline_let] let m = get_spec i in
  match a with
  | MD5 -> Hacl.Hash.Core.MD5.legacy_update
  | SHA1 -> Hacl.Hash.Core.SHA1.legacy_update
  | SHA2_224 -> Hacl.Hash.Core.SHA2.update_224
  | SHA2_256 -> Hacl.Hash.Core.SHA2.update_256
  | SHA2_384 -> Hacl.Hash.Core.SHA2.update_384
  | SHA2_512 -> Hacl.Hash.Core.SHA2.update_512
  | Blake2S -> Hacl.Hash.Core.Blake2.mk_update Blake2S m
  | Blake2B -> Hacl.Hash.Core.Blake2.mk_update Blake2B m

inline_for_extraction noextract
let pad (a: hash_alg): pad_st a =
  match a with
  | MD5 -> Hacl.Hash.Core.MD5.legacy_pad
  | SHA1 -> Hacl.Hash.Core.SHA1.legacy_pad
  | SHA2_224 -> Hacl.Hash.Core.SHA2.pad_224
  | SHA2_256 -> Hacl.Hash.Core.SHA2.pad_256
  | SHA2_384 -> Hacl.Hash.Core.SHA2.pad_384
  | SHA2_512 -> Hacl.Hash.Core.SHA2.pad_512
  | Blake2S -> Hacl.Hash.Core.Blake2.pad_blake2s
  | Blake2B -> Hacl.Hash.Core.Blake2.pad_blake2b

inline_for_extraction noextract
let finish (i:impl): finish_st i =
  [@inline_let] let a = get_alg i in
  [@inline_let] let m = get_spec i in
  match a with
  | MD5 -> Hacl.Hash.Core.MD5.legacy_finish
  | SHA1 -> Hacl.Hash.Core.SHA1.legacy_finish
  | SHA2_224 -> Hacl.Hash.Core.SHA2.finish_224
  | SHA2_256 -> Hacl.Hash.Core.SHA2.finish_256
  | SHA2_384 -> Hacl.Hash.Core.SHA2.finish_384
  | SHA2_512 -> Hacl.Hash.Core.SHA2.finish_512
  | Blake2S -> Hacl.Hash.Core.Blake2.mk_finish Blake2S m
  | Blake2B -> Hacl.Hash.Core.Blake2.mk_finish Blake2B m
