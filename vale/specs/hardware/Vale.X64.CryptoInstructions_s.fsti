module Vale.X64.CryptoInstructions_s

open FStar.Mul
open Vale.Def.Types_s
open Vale.Def.Words_s
open Vale.Def.Words.Four_s

val sha256_rnds2_spec (src1 src2 wk:quad32) : quad32

val sha256_msg1_spec (src1 src2:quad32) : quad32

val sha256_msg2_spec (src1 src2:quad32) : quad32
