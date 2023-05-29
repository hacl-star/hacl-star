(* Agile HMAC *)
module EverCrypt.HMAC

open Hacl.HMAC

// EverCrypt.Hash.Incremental.hash_256 is marked as private, so it is
// inaccessible from here. Furthermore, the EverCrypt.Hash.Incremental module
// does not have an interface, meaning that we can't even friend it! Writing an
// interface for EverCrypt.Hash.Incremental is possible, but doesn't make much
// sense: instantiations of the functor offer, by construction, an abstract
// interface. Fortunately, we can use tactics to stealthily gain access to a
// private definition that F* normally won't let us access.
let super_hack () =
  let open FStar.Tactics in
  let hash_256 = [ "EverCrypt"; "Hash"; "Incremental"; "hash_256"] in
  let hash_256 = FStar.Tactics.pack_fv hash_256 in
  let hash_256 = pack (Tv_FVar hash_256) in
  let fv = pack_fv (cur_module () `FStar.List.Tot.append` [ "hash_256" ]) in
  let t: term = pack Tv_Unknown in
  let se = pack_sigelt (Sg_Let false [ pack_lb ({ lb_fv = fv; lb_us = []; lb_typ = t; lb_def = hash_256 }) ]) in
  [ se ]

%splice[hash_256] (super_hack ())

// Due to the hack above, the dependency arrow is invisible to the F*
// parser/lexer, so we add an explicit dependency edge to avoid build errors.
module Useless = EverCrypt.Hash.Incremental

/// Four monomorphized variants, for callers who already know which algorithm they want

(** @type: true
*)
val compute_sha1: compute_st SHA1

(** @type: true
*)
val compute_sha2_256: compute_st SHA2_256

(** @type: true
*)
val compute_sha2_384: compute_st SHA2_384

(** @type: true
*)
val compute_sha2_512: compute_st SHA2_512

(** @type: true
*)
val compute_blake2s: compute_st Blake2S

(** @type: true
*)
val compute_blake2b: compute_st Blake2B

let compute_sha1 =
  let open Hacl.Hash.SHA1 in
  mk_compute (|SHA1, ()|) legacy_hash legacy_alloca legacy_init legacy_update_multi
             legacy_update_last legacy_finish

(* This implementation calls into EverCrypt.Hash, which multiplexes
   between Hacl and Vale implementations of SHA2_256 functions depending on
   the static configuration and CPUID *)
let compute_sha2_256 =
  let open Hacl.Hash.SHA2 in
  mk_compute (|SHA2_256, ()|) hash_256 alloca_256 init_256
             EverCrypt.Hash.update_multi_256
             update_last_256 finish_256

let compute_sha2_384 =
  let open Hacl.Streaming.SHA2 in
  let open Hacl.Hash.SHA2 in
  mk_compute (|SHA2_384, ()|) hash_384 alloca_384 init_384 update_multi_384
             update_last_384 finish_384

let compute_sha2_512 =
  let open Hacl.Streaming.SHA2 in
  let open Hacl.Hash.SHA2 in
  mk_compute (|SHA2_512, ()|) hash_512 alloca_512 init_512 update_multi_512
             update_last_512 finish_512

let compute_blake2s =
  let open Hacl.Hash.Blake2 in
  mk_compute (|Blake2S, Hacl.Impl.Blake2.Core.M32|) hash_blake2s_32 alloca_blake2s_32
             init_blake2s_32 update_multi_blake2s_32 update_last_blake2s_32 finish_blake2s_32

let compute_blake2b =
  let open Hacl.Hash.Blake2 in
  mk_compute (|Blake2B, Hacl.Impl.Blake2.Core.M32|) hash_blake2b_32 alloca_blake2b_32
             init_blake2b_32 update_multi_blake2b_32 update_last_blake2b_32 finish_blake2b_32

let compute a mac key keylen data datalen =
  match a with
  | SHA1 -> compute_sha1 mac key keylen data datalen
  | SHA2_256 -> compute_sha2_256 mac key keylen data datalen
  | SHA2_384 -> compute_sha2_384 mac key keylen data datalen
  | SHA2_512 -> compute_sha2_512 mac key keylen data datalen
  | Blake2S -> compute_blake2s mac key keylen data datalen
  | Blake2B -> compute_blake2b mac key keylen data datalen
