module MPFR.Add.Spec

open FStar.Mul
open MPFR.Lib.Spec

(* Proprieties for addition *)
val add: a:mpfr_structP{valid_structP a} ->
         b:mpfr_structP{valid_structP b /\ a.sign = b.sign} ->
    Tot (r:mpfr_structP{r.sign = a.sign /\ r.exp >= mpfr_EMIN_P /\ mpfr_mp_cond r /\
          ((a.mant * pow2 (a.exp - mpfr_EMIN_P)) +
	   (b.mant * pow2 (b.exp - mpfr_EMIN_P)) =
	   (r.mant * pow2 (r.exp - mpfr_EMIN_P)))})

(* Implementation for addition *)
private let min (a:int) (b:int) = if a >= b then b else a
private let max (a:int) (b:int) = if a >= b then a else b

val add_mant: a:mpfr_structP{valid_structP a} ->
              b:mpfr_structP{valid_structP b /\ a.sign = b.sign} ->
	  Tot nat
let add_mant a b =
    if a.exp >= b.exp then a.mant * pow2 (a.exp - b.exp) + b.mant
                     else b.mant * pow2 (b.exp - a.exp) + a.mant
    
val add_exp : a:mpfr_structP{valid_structP a} ->
              b:mpfr_structP{valid_structP b /\ a.sign = b.sign} ->
	 Tot (r:int{r >= mpfr_EMIN_P})
let add_exp a b = min a.exp b.exp

val add_prec: a:mpfr_structP{valid_structP a} ->
              b:mpfr_structP{valid_structP b /\ a.sign = b.sign} ->
	  Tot nat
let add_prec a b =
    let p0 = if a.exp >= b.exp then max (a.prec + a.exp - b.exp) b.prec 
                              else max (b.prec + b.exp - a.exp) a.prec in
    if add_mant a b < pow2 p0 then p0 else p0 + 1

open FStar.Math.Lemmas

val lemma_mult_lt_right: a:pos -> b:nat -> c:nat -> Lemma 
    (requires b < c)
    (ensures  b * a < c * a)
let lemma_mult_lt_right a b c = ()

(* Useful lemmas *)
val add_mp_cond_lemma: a:mpfr_structP{valid_structP a} ->
                       b:mpfr_structP{valid_structP b /\ a.sign = b.sign} ->
    Lemma (let sp = add_prec a b in
           let sm = add_mant a b in
	   pow2 (sp - 1) <= sm /\ sm < pow2 sp)
let add_mp_cond_lemma a b =
    let sp = add_prec a b in
    let sm = add_mant a b in
    let p0 = if a.exp >= b.exp then max (a.prec + a.exp - b.exp) b.prec 
                              else max (b.prec + b.exp - a.exp) a.prec in
    if sm < pow2 p0 then begin
	if a.exp >= b.exp then begin
	    lemma_mult_le_right (pow2 (a.exp - b.exp)) (pow2 (a.prec - 1)) a.mant;
	    pow2_plus (a.prec - 1) (a.exp - b.exp)
	end else begin
	    lemma_mult_le_right (pow2 (b.exp - a.exp)) (pow2 (b.prec - 1)) b.mant;
	    pow2_plus (b.prec - 1) (b.exp - a.exp)
	end
    end else begin
	if a.exp >= b.exp then begin
	    lemma_mult_lt_right (pow2 (a.exp - b.exp)) a.mant (pow2 a.prec);
	    pow2_plus a.prec (a.exp - b.exp);
	    pow2_le_compat (max (a.prec + a.exp - b.exp) b.prec) (a.prec + a.exp - b.exp);
	    pow2_le_compat (max (a.prec + a.exp - b.exp) b.prec) b.prec;
	    pow2_double_sum (max (a.prec + a.exp - b.exp) b.prec)
	end else begin
	    lemma_mult_lt_right (pow2 (b.exp - a.exp)) b.mant (pow2 b.prec);
	    pow2_plus b.prec (b.exp - a.exp);
	    pow2_le_compat (max (b.prec + b.exp - a.exp) a.prec) (b.prec + b.exp - a.exp);
	    pow2_le_compat (max (b.prec + b.exp - a.exp) a.prec) a.prec;
	    pow2_double_sum (max (b.prec + b.exp - a.exp) a.prec)
	end
    end

val add_value_lemma: a:mpfr_structP{valid_structP a} ->
                     b:mpfr_structP{valid_structP b /\ a.sign = b.sign} ->
    Lemma (add_exp a b >= mpfr_EMIN_P /\
           (a.mant * pow2 (a.exp - mpfr_EMIN_P)) +
	   (b.mant * pow2 (b.exp - mpfr_EMIN_P)) =
	   (add_mant a b * pow2 (add_exp a b - mpfr_EMIN_P)))
let add_value_lemma a b = 
    let sx = add_exp a b in
    let sm = add_mant a b in
    if a.exp >= b.exp then begin
        distributivity_add_left (a.mant * pow2 (a.exp - b.exp)) b.mant (pow2 (sx - mpfr_EMIN_P));
	paren_mul_right a.mant (pow2 (a.exp - b.exp)) (pow2 (sx - mpfr_EMIN_P));
	pow2_plus (a.exp - b.exp) (sx - mpfr_EMIN_P)
    end else begin
        distributivity_add_left (b.mant * pow2 (b.exp - a.exp)) a.mant (pow2 (sx - mpfr_EMIN_P));
	paren_mul_right b.mant (pow2 (b.exp - a.exp)) (pow2 (sx - mpfr_EMIN_P));
	pow2_plus (b.exp - a.exp) (sx - mpfr_EMIN_P)
    end

let add a b = 
    add_mp_cond_lemma a b;
    add_value_lemma a b;
    {sign = a.sign; prec = add_prec a b; mant = add_mant a b; exp = add_exp a b}
