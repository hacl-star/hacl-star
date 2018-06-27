module MPFR.Add.Spec

open FStar.Mul
open MPFR.Lib.Spec

#set-options "--z3refresh --z3rlimit 5 --max_fuel 1 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 0"

(* Proprieties for addition *)
val add: a:floating_point ->
         b:floating_point{a.sign = b.sign} ->
    Tot (r:floating_point{r.sign = a.sign /\
          (let elb = min a.exp b.exp in
	   r.exp >= elb /\
           (a.mant * pow2 (a.exp - elb)) +
	   (b.mant * pow2 (b.exp - elb)) =
	   (r.mant * pow2 (r.exp - elb)))})

(* Implementation for addition *)
private let min (a:int) (b:int) = if a >= b then b else a
private let max (a:int) (b:int) = if a >= b then a else b

val add_mant: a:floating_point ->
              b:floating_point{a.sign = b.sign} ->
	  Tot nat
let add_mant a b =
    if a.exp >= b.exp then a.mant * pow2 (a.exp - b.exp) + b.mant
                     else b.mant * pow2 (b.exp - a.exp) + a.mant
    
val add_exp : a:floating_point ->
              b:floating_point{a.sign = b.sign} ->
	 Tot (r:int{r >= min a.exp b.exp})
let add_exp a b = min a.exp b.exp

val add_prec: a:floating_point ->
              b:floating_point{a.sign = b.sign} ->
	  Tot (p:nat{let p0 = if a.exp >= b.exp then max (a.prec + a.exp - b.exp) b.prec 
                                             else max (b.prec + b.exp - a.exp) a.prec in
	           p0 <= p /\ p <= p0 + 1})
let add_prec a b =
    let p0 = if a.exp >= b.exp then max (a.prec + a.exp - b.exp) b.prec 
                              else max (b.prec + b.exp - a.exp) a.prec in
    if add_mant a b < pow2 p0 then p0 else p0 + 1


open MPFR.Lemmas

(* Useful lemmas *)
val add_fp_lemma: a:floating_point ->
                  b:floating_point{a.sign = b.sign} ->
    Lemma (let sp = add_prec a b in
           let sm = add_mant a b in
	   pow2 (sp - 1) <= sm /\ sm < pow2 sp)
let add_fp_lemma a b =
    let sp = add_prec a b in
    let sm = add_mant a b in
    let p0 = if a.exp >= b.exp then max (a.prec + a.exp - b.exp) b.prec 
                              else max (b.prec + b.exp - a.exp) a.prec in
    if sm < pow2 p0 then begin
	if a.exp >= b.exp then begin
	    lemma_mul_le_right (pow2 (a.exp - b.exp)) (pow2 (a.prec - 1)) a.mant;
	    lemma_pow2_mul (a.prec - 1) (a.exp - b.exp)
	end else begin
	    lemma_mul_le_right (pow2 (b.exp - a.exp)) (pow2 (b.prec - 1)) b.mant;
	    lemma_pow2_mul (b.prec - 1) (b.exp - a.exp)
	end
    end else begin
	if a.exp >= b.exp then begin
	    lemma_mul_lt_right (pow2 (a.exp - b.exp)) a.mant (pow2 a.prec);
	    lemma_pow2_mul a.prec (a.exp - b.exp);
	    lemma_pow2_le (a.prec + a.exp - b.exp) (max (a.prec + a.exp - b.exp) b.prec);
	    lemma_pow2_le b.prec (max (a.prec + a.exp - b.exp) b.prec);
	    lemma_pow2_double (max (a.prec + a.exp - b.exp) b.prec)
	end else begin
	    lemma_mul_lt_right (pow2 (b.exp - a.exp)) b.mant (pow2 b.prec);
	    lemma_pow2_mul b.prec (b.exp - a.exp);
	    lemma_pow2_le (b.prec + b.exp - a.exp) (max (b.prec + b.exp - a.exp) a.prec);
	    lemma_pow2_le a.prec (max (b.prec + b.exp - a.exp) a.prec);
	    lemma_pow2_double (max (b.prec + b.exp - a.exp) a.prec)
	end
    end

val add_value_lemma: a:floating_point ->
                     b:floating_point{a.sign = b.sign} ->
    Lemma (let elb = min a.exp b.exp in
           add_exp a b >= elb /\
           (a.mant * pow2 (a.exp - elb)) +
	   (b.mant * pow2 (b.exp - elb)) =
	   (add_mant a b * pow2 (add_exp a b - elb)))
let add_value_lemma a b = 
    let sx = add_exp a b in
    let sm = add_mant a b in
    let elb = min a.exp b.exp in
    if a.exp >= b.exp then begin
        lemma_distr_add_left (a.mant * pow2 (a.exp - b.exp)) b.mant (pow2 (sx - elb));
	lemma_paren_mul_right a.mant (pow2 (a.exp - b.exp)) (pow2 (sx - elb));
	lemma_pow2_mul (a.exp - b.exp) (sx - elb)
    end else begin
        lemma_distr_add_left (b.mant * pow2 (b.exp - a.exp)) a.mant (pow2 (sx - elb));
	lemma_paren_mul_right b.mant (pow2 (b.exp - a.exp)) (pow2 (sx - elb));
	lemma_pow2_mul (b.exp - a.exp) (sx - elb)
    end

let add a b = 
    add_fp_lemma a b;
    add_value_lemma a b;
    {sign = a.sign; prec = add_prec a b; mant = add_mant a b; exp = add_exp a b}
