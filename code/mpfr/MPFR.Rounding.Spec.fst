module MPFR.Rounding.Spec

open FStar.UInt
open MPFR.Lib.Spec

(* Definitions of rounding bit and sticky bit *)
let nth_bit  (#m:pos) (a:uint_t m) (n:nat) = if n < m then nth a n else false

val rb_spec: a:mpfr_structP{valid_structP a} -> p:pos ->
    Tot (rb:bool{rb = nth_bit #a.prec a.mant p})
    
let nth_from (#m:pos) (a:uint_t m) (n:nat) = if n < m then (a % pow2 (m - n) <> 0) else false

val sb_spec: a:mpfr_structP{valid_structP a} -> p:pos -> 
    Tot (sb:bool{sb = nth_from #a.prec a.mant (p + 1)})


(* Useful lemmas for proving rounding/sticky bit proprieties *)		 
let rb_spec a p =
    if a.prec <= p then false
    else nth #a.prec a.mant p

let sb_spec a p = 
    if a.prec <= p + 1 then false
    else (a.mant % pow2 (a.prec - (p + 1)) <> 0)

val rb_mask_lemma: #n:pos -> a:uint_t n -> s:nat{s < n} ->
    Lemma (nth a s = (logand a (pow2_n #n (n - s - 1)) <> 0))
let rb_mask_lemma #n a s =
    if nth a s then nth_lemma (logand a (pow2_n #n (n - s - 1))) (pow2_n #n (n - s - 1))
    else nth_lemma (logand a (pow2_n #n (n - s - 1))) (zero n)

val sb_mask_lemma: #n:pos -> a:uint_t n -> s:pos{s < n} ->
    Lemma (ensures (nth_from a s = (logand a (pow2_n #n (n - s) - 1) <> 0)))
let sb_mask_lemma #n a s = 
    Math.Lemmas.pow2_lt_compat n (n - s);
    logand_mask #n a (n - s)


(* Proprieties of rounding bit and sticky bit *)
val rb_spec_lemma: a:mpfr_structP{valid_structP a} -> p:pos{p < a.prec} ->
    Lemma (rb_spec a p = (logand a.mant (pow2_n #a.prec (a.prec - p - 1)) <> 0))
let rb_spec_lemma a p = rb_mask_lemma #a.prec a.mant p

val sb_spec_lemma: a:mpfr_structP{valid_structP a} -> p:pos{p < a.prec - 1} ->
    Lemma (sb_spec a p = (logand #a.prec a.mant (pow2_n #a.prec (a.prec - p - 1) - 1) <> 0))
let sb_spec_lemma a p = sb_mask_lemma #a.prec a.mant (p + 1)
