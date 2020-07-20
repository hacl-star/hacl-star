module Hacl.HMAC.Blake2b_256

module B = LowStar.Buffer
module D = Hacl.Hash.Definitions

open Spec.Agile.HMAC
open Spec.Hash.Definitions
open FStar.HyperStack.ST
open Lib.IntTypes

open EverCrypt.Helpers

open Hacl.HMAC
open Hacl.Hash.Blake2b_256

#set-options "--z3rlimit 25 --fuel 0 --ifuel 0"

let compute_blake2b_256: compute_st Blake2B =
  let open Hacl.Hash.Blake2 in
  mk_compute (D.mk_impl Blake2B Hacl.Impl.Blake2.Core.M256)
             hash_blake2b_256 alloca_blake2b_256 init_blake2b_256
             update_multi_blake2b_256 update_last_blake2b_256 finish_blake2b_256

