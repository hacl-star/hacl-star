module Hacl.Impl.SHA512.Ed25519

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.UInt32
open FStar.HyperStack
open FStar.Seq
open FStar.Buffer

#reset-options "--max_fuel 0 --z3rlimit 20"

open Hacl.Impl.SHA512.Ed25519_3

let sha512_pre_msg h prefix input len =
  sha512_pre_msg h prefix input len

let sha512_pre_pre2_msg h prefix prefix2 input len =
  sha512_pre_pre2_msg h prefix prefix2 input len
