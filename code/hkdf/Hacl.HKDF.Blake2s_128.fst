module Hacl.HKDF.Blake2s_128

open Spec.Hash.Definitions
open Hacl.HKDF

#set-options "--z3rlimit 20 --fuel 0 --ifuel 0"

let expand_blake2s_128: expand_st Blake2S =
  mk_expand Blake2S Hacl.HMAC.Blake2s_128.compute_blake2s_128

let extract_blake2s_128: extract_st Blake2S =
  mk_extract Blake2S Hacl.HMAC.Blake2s_128.compute_blake2s_128
