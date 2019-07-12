module X64.Vale.Xmms
open X64.Machine_s
open FStar.FunctionalExtensionality

let equal xmms1 xmms2 = feq xmms1 xmms2
let lemma_equal_intro xmms1 xmms2 = ()
let lemma_equal_elim xmms1 xmms2 = ()

