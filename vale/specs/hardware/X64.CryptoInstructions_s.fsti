module X64.CryptoInstructions_s

open Types_s
open Words_s
open Words.Four_s

val sha256_rnds2_spec (src1 src2 wk:quad32) : quad32 

val sha256_msg1_spec (src1 src2:quad32) : quad32

val sha256_msg2_spec (src1 src2:quad32) : quad32
