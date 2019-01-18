module Hacl.Hash.PadFinish

module U32 = FStar.UInt32

open Hacl.Hash.Definitions
open Spec.Hash.Definitions

(** Shared implementations of the pad and finish functions, across all hash algorithms. *)

noextract inline_for_extraction
val pad: a:hash_alg -> pad_st a

(* Allows the caller to compute which length to allocate for padding. *)
inline_for_extraction noextract
val pad_len: a:hash_alg -> len:len_t a ->
  x:U32.t { U32.v x = pad_length a (len_v a len) }

noextract inline_for_extraction
val finish: a:hash_alg -> finish_st a
