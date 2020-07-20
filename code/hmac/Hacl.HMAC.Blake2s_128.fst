module Hacl.HMAC.Blake2s_128

module B = LowStar.Buffer
module D = Hacl.Hash.Definitions

open Spec.Agile.HMAC
open Spec.Hash.Definitions
open FStar.HyperStack.ST
open Lib.IntTypes

open EverCrypt.Helpers

open Hacl.HMAC
open Hacl.Hash.Blake2s_128

#set-options "--z3rlimit 25 --fuel 0 --ifuel 0"

let compute_blake2s_128: compute_st Blake2S =
  let open Hacl.Hash.Blake2 in
  mk_compute (D.mk_impl Blake2S Hacl.Impl.Blake2.Core.M128)
             hash_blake2s_128 alloca_blake2s_128 init_blake2s_128
             update_multi_blake2s_128 update_last_blake2s_128 finish_blake2s_128

