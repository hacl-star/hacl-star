module Curve25519

open FStar.Mul
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer
open FStar.Buffer.Quantifiers

#reset-options "--max_fuel 0 --z3rlimit 20"

let crypto_scalarmult mypublic secret basepoint =  Hacl.EC.crypto_scalarmult mypublic secret basepoint
