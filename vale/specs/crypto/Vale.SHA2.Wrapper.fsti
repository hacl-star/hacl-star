module Vale.SHA2.Wrapper

open Vale.Def.Words_s

val sigma256_0_0: x:nat32 -> Tot (nat32)

val sigma256_0_1: x:nat32 -> Tot (nat32)

val sigma256_1_0: x:nat32 -> Tot (nat32)

val sigma256_1_1: x:nat32 -> Tot (nat32)

val ch256: x:nat32 -> y:nat32 -> z:nat32 -> Tot (nat32)

val maj256: x:nat32 -> y:nat32 -> z:nat32 -> Tot (nat32)
