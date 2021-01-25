module Hacl.Impl.P256.DH

open Hacl.Impl.P256.Primitives



#set-options "--fuel 0 --ifuel 0 --z3rlimit 200"

let ecp256dh_i m result scalar =
  secretToPublic m result scalar

let ecp256dh_r m result pubKey scalar =
  scalarMult m result pubKey scalar
