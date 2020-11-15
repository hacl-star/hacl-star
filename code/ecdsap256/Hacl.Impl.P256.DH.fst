module Hacl.Impl.P256.DH

open Hacl.Impl.P256.Primitives


#set-options "--fuel 0 --ifuel 0 --z3rlimit 200"

let ecp256dh_i result scalar =
  secretToPublic result scalar

let ecp256dh_r result pubKey scalar =
  scalarMult result pubKey scalar
