module Hacl.Salsa20

open Hacl.Impl.Salsa20
open Hacl.Impl.HSalsa20

#reset-options "--max_fuel 0 --z3rlimit 20"

let salsa20 output plain len k n ctr = salsa20 output plain len k n ctr

let hsalsa20 output key nonce =
  crypto_core_hsalsa20 output nonce key
