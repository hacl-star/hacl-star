module Curve.Parameters

open Math.Lib
open FStar.Mul
open FStar.Ghost

val prime: erased pos
let prime = hide (pow2 256 - pow2 224 + pow2 192 + pow2 96 - 1)

val platform_size:pos
let platform_size = 64

val platform_wide:w:pos{w = 2*platform_size}
let platform_wide = 128

val norm_length: pos
let norm_length = 8

val nlength: UInt32.t
let nlength = 8ul

val bytes_length: pos
let bytes_length = 32

val blength: UInt32.t
let blength = 32ul

val templ: nat -> Tot pos
let templ = fun x -> 32

val parameters_lemma_0:
  unit -> Lemma (requires (True)) 
	        (ensures (forall (i:nat). i < 2*norm_length - 1 ==> templ i < platform_size))

val parameters_lemma_1:
  unit -> Lemma (requires (True))
	        (ensures (platform_wide - 1 >= log_2 norm_length))
let parameters_lemma_0 () = ()
let parameters_lemma_1 () = ()
