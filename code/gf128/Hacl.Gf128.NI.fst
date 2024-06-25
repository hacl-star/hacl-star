module Hacl.Gf128.NI

open FStar.HyperStack
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer
open Lib.IntVector

open Hacl.Impl.Gf128.Fields
open Hacl.Impl.Gf128.Generic

module ST = FStar.HyperStack.ST
module Vec = Hacl.Spec.GF128.Vec

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 1"

inline_for_extraction noextract
let gcm_ctx_elem = vec_t U128 1
inline_for_extraction noextract
let gcm_ctx_len = 5ul

inline_for_extraction noextract
let gcm_ctx_elem_zero = vec_zero U128 1
inline_for_extraction noextract
let gcm_ctx = lbuffer gcm_ctx_elem gcm_ctx_len

[@@ CPrologue
"/*******************************************************************************

A verified GHASH library.

This is a 128-bit optimized version of GHASH algorithm over GF(2^128) for data
authenticity that utilizes hardware-accelerated carry-less/polynomial multiplication.

*******************************************************************************/

/************************/
/* GHASH API */
/************************/\n";
Comment
"Initiate GHASH context with the following layout

  Authentication Tag     -> CONTEXT.[0] (16-byte)
  h * h^3                -> CONTEXT.[1] (16-byte)
  h * h^2                -> CONTEXT.[2] (16-byte)
  h * h                  -> CONTEXT.[3] (16-byte)
  h (hash key)           -> CONTEXT.[4] (16-byte)"]
let gcm_init : gf128_init_st Vec.NI =
  gf128_init #Vec.NI


[@@ Comment "Expand the input message to have a length of multiple of 16 and pad 
  the extra bytes with zeros. The authentication tag is computed by feeding the
  previous state and applying GHASH algorithm on expanded message"]
let gcm_update_blocks: gf128_update_st Vec.NI =
  gf128_update #Vec.NI


[@@ Comment "Copy hash state from GHASH context to 16-byte output buffer"]
let gcm_emit: gf128_emit_st Vec.NI =
  gf128_emit #Vec.NI


[@@ Comment "Initiate GHASH context, apply GHASH algorithm on input message,
  and copy authentication tag to output buffer"]
let ghash: ghash_st Vec.NI =
  ghash #Vec.NI
