module Vale.Def.Words_s
open FStar.Mul

// Sanity check our constants
let _ = assert_norm (pow2 8 = pow2_8)
let _ = assert_norm (pow2 16 = pow2_16)
let _ = assert_norm (pow2 32 = pow2_32)
let _ = assert_norm (pow2 64 = pow2_64)
let _ = assert_norm (pow2 128 = pow2_128)

#reset-options "--z3cliopt smt.arith.nl=true"
let int_to_natN n i = i % n // arbitrary definition, hidden from clients
#reset-options

