(*--build-config
  options:--admit_fsi FStar.Set --verify_module Parameters;
  other-files:FStar.Classical.fst seq.fsi FStar.Seq.Base.fst FStar.Seq.Properties.fst FStar.Seq.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Ghost.fst axiomatic.fst intlib.fst;
  --*)

module Parameters

open FStar.Ghost
open IntLib

val prime: erased pos
let prime = IntLib.pow2_increases_lemma 448 224;
  hide (pow2 256 - pow2 224 + pow2 192 + pow2 96 - 1)

val platform_size:pos
let platform_size = 64

val platform_wide:w:pos{w = 2*platform_size}
let platform_wide = 128

val norm_length: pos
let norm_length = 8

val bytes_length: pos
let bytes_length = 32

val templ: nat -> Tot pos
let templ = fun x -> 32

val ndiff: n:pos{n <= platform_size /\ (forall (i:nat). i < norm_length ==> templ i < n)}
let ndiff = 33

val ndiff': n:pos{n < ndiff /\ (forall (i:nat). i < norm_length ==> templ i <= n)}
let ndiff' = 32

val parameters_lemma_0:
  unit -> Lemma (requires (True)) 
	        (ensures (forall (i:nat). i < 2*norm_length - 1 ==> templ i < platform_size))

val parameters_lemma_1:
  unit -> Lemma (requires (True))
	        (ensures (platform_wide - 1 >= IntLib.log_2 norm_length))
let parameters_lemma_0 () = ()
let parameters_lemma_1 () = ()
