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


[@CInline]
let gcm_init : gf128_init_st Vec.NI =
  gf128_init #Vec.NI


[@CInline]
let gcm_update_blocks: gf128_update_st Vec.NI =
  gf128_update #Vec.NI


[@CInline]
let gcm_update_padded: gf128_update_st Vec.NI =
  gcm_update_blocks


[@CInline]
let gcm_emit: gf128_emit_st Vec.NI =
  gf128_emit #Vec.NI


[@CInline]
let ghash: ghash_st Vec.NI =
  ghash #Vec.NI
