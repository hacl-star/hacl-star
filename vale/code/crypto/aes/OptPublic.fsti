module OptPublic

open Types_s

val hkeys_reqs_pub (hkeys:FStar.Seq.seq quad32) (h_BE:quad32) : Prop_s.prop0

noextract
val get_hkeys_reqs (h_BE:quad32) : (s:Seq.lseq quad32 8{hkeys_reqs_pub s h_BE})

val get_hkeys_reqs_injective (h_BE:quad32) (s1 s2:Seq.seq quad32) : Lemma
  (requires 
    Seq.length s1 = 8 /\ Seq.length s2 = 8 /\
    hkeys_reqs_pub s1 h_BE /\ hkeys_reqs_pub s2 h_BE)
  (ensures s1 == s2)
