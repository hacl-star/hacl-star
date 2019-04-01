module OptPublic

open Types_s

val hkeys_reqs_pub (hkeys:FStar.Seq.seq quad32) (h_LE:quad32) : Prop_s.prop0

val get_hkeys_reqs (h_LE:quad32) : (s:Seq.lseq quad32 10{hkeys_reqs_pub s h_LE})
