(*--build-config
  options:--admit_fsi FStar.Set --verify_module Parameters;
  other-files:FStar.Classical.fst seq.fsi FStar.Seq.Base.fst FStar.Seq.Properties.fst FStar.Seq.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Ghost.fst axiomatic.fst intlib.fst;
  --*)

module Parameters

open FStar.Ghost

val prime: erased pos
let prime = hide (IntLib.pow2 255 - 19)

val platform_size: pos
let platform_size = 64

val platform_wide: w:pos{w = 2 * platform_size }
let platform_wide = 128

val norm_length: pos
let norm_length = 5

val bytes_length: pos
let bytes_length = 32

val templ: t:(nat -> Tot pos)//{forall (i:nat). t i = t 0}
let templ = fun x -> 51

val a24: string
val a24':nat
let a24 = "121665"
let a24' = 121665

val ndiff: n:pos{n <= platform_size /\ (forall (i:nat). i < norm_length ==> templ i < n)}
let ndiff = 53

val ndiff': n:pos{n < ndiff /\ (forall (i:nat). i < norm_length ==> templ i <= n)}
let ndiff' = 51

(* Required at least for addition *)
val parameters_lemma_0:
  unit -> Lemma (requires (True)) 
	        (ensures (forall (i:nat). i < 2*norm_length - 1 ==> templ i < platform_size))

val parameters_lemma_1:
  unit -> Lemma (requires (True))
	        (ensures (platform_wide - 1 >= IntLib.log_2 norm_length))
let parameters_lemma_0 () = ()
let parameters_lemma_1 () = ()
