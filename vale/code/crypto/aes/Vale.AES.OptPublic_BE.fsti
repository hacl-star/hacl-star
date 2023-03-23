module Vale.AES.OptPublic_BE

open FStar.Mul
open Vale.Def.Types_s

val hkeys_reqs_pub (hkeys:FStar.Seq.seq quad32) (h_BE:quad32) : Vale.Def.Prop_s.prop0
