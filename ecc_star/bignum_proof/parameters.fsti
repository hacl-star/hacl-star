module Parameters

open IntLib
open FStar.Ghost

val prime: erased pos
val platform_size: pos
val platform_wide: w:pos{w = 2 * platform_size }
val norm_length: pos
val bytes_length: pos
val templ: t:(nat -> Tot pos)
val a24: string
val a24':nat
val ndiff: n:pos{n <= platform_size /\ (forall (i:nat). i < norm_length ==> templ i < n)}
val ndiff': n:pos{n < ndiff /\ (forall (i:nat). i < norm_length ==> templ i <= n)}

val templ_lemma: i:nat -> Lemma (requires (True))
			      (ensures  (templ i = templ 0))
			      [SMTPat (templ i)]

(* Required at least for addition *)
val parameters_lemma_0:
  unit -> Lemma (requires (True)) 
	        (ensures (forall (i:nat). i < 2*norm_length - 1 ==> templ i < platform_size))

val parameters_lemma_1:
  unit -> Lemma (requires (True))
	        (ensures (platform_wide - 1 >= log_2 norm_length))
