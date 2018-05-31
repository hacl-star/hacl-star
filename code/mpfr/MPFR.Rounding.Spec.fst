module MPFR.Rounding.Spec

open FStar.UInt
open MPFR.Lib.Spec

(* Definitions of rounding bit and sticky bit *)
let nth_bit  (#m:pos) (a:uint_t m) (n:nat) = if n < m then nth a n else false

val rb_spec: a:mpfr_structP{valid_mpfr_struct a} -> p:pos{mpfr_prec_cond p} ->
    Tot (rb:bool{rb <==> nth_bit #a.prec a.mant p})
    
let nth_from (#m:pos) (a:uint_t m) (n:nat) = exists (i:nat{n <= i /\ i < m}). nth a i

val sb_spec: a:mpfr_structP{valid_mpfr_struct a} -> p:pos{mpfr_prec_cond p} -> 
    Tot (sb:bool{sb <==> nth_from #a.prec a.mant (p + 1)})


(* Useful lemmas for proving rounding/sticky bit proprieties *)		 
let rb_spec a p =
    if a.prec <= p then false
    else nth #a.prec a.mant p
    
val bitor_from: #n:pos -> a:uint_t n -> s:nat{s < n} ->
    Tot (b:bool{b <==> nth_from #n a s}) (decreases (n - s))
let rec bitor_from #n a s =
    if s + 1 = n then nth a s
                 else nth a s || bitor_from #n a (s + 1)

let sb_spec a p = 
    if a.prec <= p + 1 then false
    else bitor_from #a.prec a.mant (p + 1)

val nth_from_plusone_lemma: #m:pos -> a:uint_t m -> n:nat{n < m} ->
    Lemma (nth_from a n <==> (nth a n \/ nth_from a (n + 1)))
let nth_from_plusone_lemma #m a n = ()

val pow2m1_nth_lemma: #n:pos -> p:nat{p < n} -> i:nat{i < n} ->
    Lemma (ensures (i > n - p - 1 ==> nth #n (pow2_n #n p - 1) i = true) /\
	           (i <= n - p - 1 ==> nth #n (pow2_n #n p - 1) i = false))
          [SMTPat (nth #n (pow2_n #n p - 1) i)]
let pow2m1_nth_lemma #n p i = ()

val logor_pow2_pow2m1_nth_lemma: #n:pos -> p:nat{p + 1 < n} -> i:nat{i < n} ->
    Lemma (ensures (nth #n (logor (pow2_n #n p) (pow2_n #n p - 1)) i =
                    nth #n (pow2_n #n (p + 1) - 1) i))
          [SMTPat (nth #n (logor (pow2_n #n p) (pow2_n #n p - 1)) i)]
let logor_pow2_pow2m1_nth_lemma #n p i = ()

val logand_logor_distr: #n:pos -> a:uint_t n -> b:uint_t n -> c:uint_t n ->
    Lemma (logand a (logor b c) = logor (logand a b) (logand a c))
let logand_logor_distr #n a b c =
    nth_lemma (logand a (logor b c)) (logor (logand a b) (logand a c))

val logor_not_zero: #n:pos -> a:uint_t n -> b:uint_t n ->
    Lemma (logor a b <> 0 <==> (a <> 0 \/ b <> 0))
let logor_not_zero #n a b = if b = 0 then logor_lemma_1 a else logor_ge a b

val rb_mask_lemma: #n:pos -> a:uint_t n -> s:nat{s < n} ->
    Lemma (nth a s <==> logand a (pow2_n #n (n - s - 1)) <> 0)
let rb_mask_lemma #n a s =
    if nth a s then nth_lemma (logand a (pow2_n #n (n - s - 1))) (pow2_n #n (n - s - 1))
    else nth_lemma (logand a (pow2_n #n (n - s - 1))) (zero n)

val sb_mask_lemma: #n:pos -> a:uint_t n -> s:pos{s < n} ->
    Lemma (ensures (nth_from a s <==> logand a (pow2_n #n (n - s) - 1) <> 0))
          (decreases (n - s))
let rec sb_mask_lemma #n a s =
    if s + 1 = n then rb_mask_lemma a s
    else begin
      rb_mask_lemma #n a s;
      sb_mask_lemma #n a (s + 1);
      nth_from_plusone_lemma a s;
      logor_not_zero (logand a (pow2_n #n (n - s - 1))) (logand a (pow2_n #n (n - s - 1) - 1));
      nth_lemma (logor (pow2_n #n (n - s - 1)) (pow2_n #n (n - s - 1) - 1)) (pow2_n #n (n - s) - 1);
      logand_logor_distr a (pow2_n #n (n - s - 1)) (pow2_n #n (n - s - 1) - 1)
    end


(* Proprieties of rounding bit and sticky bit *)
val rb_spec_lemma: a:mpfr_structP{valid_mpfr_struct a} -> p:pos{mpfr_prec_cond p /\ p < a.prec} ->
    Lemma (rb_spec a p = (logand a.mant (pow2_n #a.prec (a.prec - p - 1)) <> 0))
let rb_spec_lemma a p = rb_mask_lemma #a.prec a.mant p

val sb_spec_lemma: a:mpfr_structP{valid_mpfr_struct a} -> p:pos{mpfr_prec_cond p /\ p < a.prec - 1} ->
    Lemma (sb_spec a p = (logand #a.prec a.mant (pow2_n #a.prec (a.prec - p - 1) - 1) <> 0))
let sb_spec_lemma a p = sb_mask_lemma #a.prec a.mant (p + 1)
