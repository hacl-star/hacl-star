module Hacl.HKDF.Blake2b_256

open Spec.Hash.Definitions
open Hacl.HKDF

#set-options "--z3rlimit 20 --fuel 0 --ifuel 0"

let expand_blake2b_256: expand_st Blake2B =
  mk_expand Blake2B Hacl.HMAC.Blake2b_256.compute_blake2b_256

let extract_blake2b_256: extract_st Blake2B =
  mk_extract Blake2B Hacl.HMAC.Blake2b_256.compute_blake2b_256
