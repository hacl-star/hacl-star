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

[@@ Comment "Write the HMAC-BLAKE2s MAC of a message (`data`) by using a key (`key`) into `dst`.

The key can be any length and will be hashed if it is longer and padded if it is shorter than 64 bytes.
`dst` must point to 32 bytes of memory."]
let compute_blake2s_128: compute_st Blake2S =
  mk_compute (D.mk_impl Blake2S Hacl.Impl.Blake2.Core.M128)
             hash alloca init update_multi update_last finish
