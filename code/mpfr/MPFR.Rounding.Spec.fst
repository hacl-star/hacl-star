module MPFR.Rounding.Spec

open FStar.Mul
open FStar.UInt
open MPFR.Lemmas
open MPFR.Lib.Spec

#set-options "--z3refresh --z3rlimit 5 --max_fuel 1 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 0"

///////////////////////////////////////////////
//  Some useful implementation for rounding  //
///////////////////////////////////////////////

(* When target precision is larger than before *)
val rnd_large_p: a:floating_point -> p:pos{p >= a.prec} ->
    Tot (r:floating_point{r.sign = a.sign /\ r.prec = p /\
        (let elb = min a.exp r.exp in
	r.mant * pow2 (r.exp - elb) = a.mant * pow2 (a.exp - elb))})
	
let rnd_large_p a p =
    let elb = min a.exp (a.exp + a.prec - p) in
    lemma_pow2_mul (p - a.prec) a.prec;
    lemma_pow2_mul (p - a.prec) (a.prec - 1);
    lemma_pow2_mul (p - a.prec) (a.exp + a.prec - p - elb);
    {sign = a.sign; prec = p; mant = a.mant * pow2 (p - a.prec); exp = a.exp + a.prec - p}

(* Splitting the significand when target precision is smaller *)
let ulp    (a:floating_point) (p:pos{p < a.prec}) = pow2 (a.prec - p)
let l_mant (a:floating_point) (p:pos{p < a.prec}) = a.mant % ulp a p
let h_mant (a:floating_point) (p:pos{p < a.prec}) = a.mant - l_mant a p

//////////////////////////////////////////////////////////////////////////////////////
//  RNDN Definition: Rounding to the nearest                                        //
//  Given floating point number 'a' and precision 'p', got result r = RNDN(a, p)    //
//  Splitting 'a' into two floating point numbers a = a_high + a_low                //
//  Rounding 'a' to a_high or a_high + ulp depending on a_low                       //
//  We should always have the following inequality:                                 //
//  (r.mant - 0.5) * 2 ^ r.exp <= a.mant * 2 ^ a.exp <= (r.mant + 0.5) * 2 ^ r.exp  //
//  But it slightly varies according to "round to even rule"                        //
//////////////////////////////////////////////////////////////////////////////////////

(* RNDN definition *)
let even_hm (a:floating_point) (p:pos{p < a.prec}) = ((a.mant / ulp a p) % 2 = 0)

let rndn_def (a:floating_point) (p:pos): (r:fp_struct{r.sign = a.sign}) =
    if a.prec <= p then rnd_large_p a p
    else begin
        if (l_mant a p < ulp a p / 2 || (l_mant a p = ulp a p / 2 && even_hm a p)) then
	{sign = a.sign; prec = a.prec; mant = h_mant a p; exp = a.exp} else
	{sign = a.sign; prec = a.prec; mant = h_mant a p + ulp a p; exp = a.exp}
    end

(* Check if the result has the same value as defined by rndn_def *)
let rndn_value_cond (a:floating_point) (p:pos) (r:floating_point{r.sign = a.sign}) =
    let d = rndn_def a p in
    let elb = min d.exp r.exp in
    d.mant * pow2 (d.exp - elb) = r.mant * pow2 (r.exp - elb)

(* Check if the original value lies in certain interval *)
let rndn_range_cond (a:floating_point) (p:pos) (r:floating_point) =
    let elb = min a.exp r.exp in
    (r.mant % 2 = 1 ==> 
        ((r.mant * 2 - 1) * pow2 (r.exp - elb) < a.mant * pow2 (a.exp - elb + 1) /\
         (r.mant * 2 + 1) * pow2 (r.exp - elb) > a.mant * pow2 (a.exp - elb + 1))) /\
    (r.mant = pow2 (r.prec - 1) ==>
        ((r.mant * 4 - 1) * pow2 (r.exp - elb) <= a.mant * pow2 (a.exp - elb + 2) /\
         (r.mant * 2 + 1) * pow2 (r.exp - elb) >= a.mant * pow2 (a.exp - elb + 1))) /\
    ((r.mant <> pow2 (r.prec - 1) /\ r.mant % 2 = 0) ==>
        ((r.mant * 2 - 1) * pow2 (r.exp - elb) <= a.mant * pow2 (a.exp - elb + 1) /\
         (r.mant * 2 + 1) * pow2 (r.exp - elb) >= a.mant * pow2 (a.exp - elb + 1)))

(* The specification should satisfy two conditions, which are actually equivalent *)
val rndn_spec: a:floating_point -> p:pos ->
    Tot (r:floating_point{r.prec = p /\ r.sign = a.sign /\
                          rndn_value_cond a p r /\ rndn_range_cond a p r})

////////////////////////////////////////////////////////////////
//  Implementation for each rounding mode                     //
//  Including implementation of rounding/sticky bit for RNDN  //
////////////////////////////////////////////////////////////////

(* Getting the first p bits of mantissa *)
val main_mant: a:floating_point -> p:pos{p < a.prec} -> 
    Tot (rmant:nat{pow2 (p - 1) <= rmant /\ rmant < pow2 p /\
        (let rexp = a.exp + a.prec - p in
	 let elb = min a.exp rexp in
	 rmant * pow2 (rexp - elb) <= a.mant * pow2 (a.exp - elb) /\
         a.mant * pow2 (a.exp - elb) < (rmant + 1) * pow2 (rexp - elb))})
	 
let main_mant a p =
    let rexp = a.exp + a.prec - p in
    let elb = min a.exp rexp in
    lemma_pow2_div (a.prec - 1) (a.prec - p);
    lemma_div_le (pow2 (a.prec - 1)) a.mant (pow2 (a.prec - p));
    lemma_pow2_div_lt a.mant a.prec (a.prec - p);
    lemma_distr_add_left (a.mant / pow2 (a.prec - p)) 1 (pow2 (rexp - elb));
    a.mant / pow2 (a.prec - p)

(* Implementation of rounding bit *)
val rb_spec: a:floating_point -> p:pos -> Tot bool
let rb_spec a p =
    if a.prec <= p then false
    else nth #a.prec a.mant p

(* Proprieties of rounding bit *)
val rb_spec_mask_lemma: a:floating_point -> p:pos{p < a.prec} ->
    Lemma (rb_spec a p = (logand a.mant (pow2_n #a.prec (a.prec - p - 1)) = pow2_n #a.prec (a.prec - p - 1)))
    
let rb_spec_mask_lemma a p = 
    if nth #a.prec a.mant p then 
        nth_lemma (logand a.mant (pow2_n #a.prec (a.prec - p - 1))) (pow2_n #a.prec (a.prec - p - 1))
    else 
        nth_lemma (logand a.mant (pow2_n #a.prec (a.prec - p - 1))) (zero a.prec)

val rb_spec_value_lemma: a:floating_point -> p:pos{p < a.prec} ->
    Lemma (a.mant % pow2 (a.prec - p) = (if rb_spec a p then pow2 (a.prec - p - 1) else 0) +
                                        a.mant % pow2 (a.prec - p - 1))
					
let rb_spec_value_lemma a p =
    assert(nth #a.prec a.mant p = nth (shift_right #a.prec a.mant (a.prec - p - 1)) (a.prec - 1));
    lemma_pow2_mod_div a.mant (a.prec - p) (a.prec - p - 1);
    lemma_pow2_mod_mod a.mant (a.prec - p) (a.prec - p - 1)

(* Implementation of sticky bit *)
val sb_spec: a:floating_point -> p:pos -> Tot bool
let sb_spec a p = 
    if a.prec <= p + 1 then false
    else (a.mant % pow2 (a.prec - (p + 1)) <> 0)

(* Proprieties of sticky bit *)
val sb_spec_mask_lemma: a:floating_point -> p:pos{p < a.prec - 1} ->
    Lemma (sb_spec a p = (logand #a.prec a.mant (pow2_n #a.prec (a.prec - p - 1) - 1) <> 0))
    
let sb_spec_mask_lemma a p = 
    lemma_pow2_lt (a.prec - p - 1) a.prec;
    logand_mask #a.prec a.mant (a.prec - p - 1)

val sb_spec_value_lemma: a:floating_point -> p:pos{p < a.prec} ->
    Lemma (sb_spec a p = (a.mant % pow2 (a.prec - p - 1) <> 0))
    
let sb_spec_value_lemma a p = ()


//////////////////////////////////////////////////////////////
//  Implementation for RNDN                                 //
//  3 lemmas for different branches in main implementation  //
//////////////////////////////////////////////////////////////
(* Two conditions are equivalent *)
val rndn_value_imp_range_lemma: a:floating_point -> p:pos -> r:floating_point{r.sign = a.sign} -> Lemma
    (requires (rndn_value_cond a p r))
    (ensures  (rndn_range_cond a p r))

let rndn_value_imp_range_lemma a p r = admit()

(* Lemmas for RNDN *)
val rndn_spec_branch1: a:floating_point ->
    p:pos{p < a.prec /\ (rb_spec a p = false \/ (sb_spec a p = false && main_mant a p % 2 = 0))} ->
    Tot (r:floating_point{r.prec = p /\ r.sign = a.sign /\
                          rndn_value_cond a p r /\ rndn_range_cond a p r})
			  
let rndn_spec_branch1 a p =
    let rmant = main_mant a p in
    let rexp = a.exp + a.prec - p in
    let r = {sign = a.sign; prec = p; mant = rmant; exp = rexp} in
    let d = rndn_def a p in
    let elb = min d.exp rexp in
    rb_spec_value_lemma a p;
    sb_spec_value_lemma a p;
    lemma_pow2_mul (a.prec - p) (d.exp - elb);
    rndn_value_imp_range_lemma a p r;
    r

val rndn_spec_branch2: a:floating_point -> 
    p:pos{p < a.prec /\ rb_spec a p = true /\
         (sb_spec a p = true \/ (sb_spec a p = false /\ main_mant a p % 2 = 1)) /\
	 main_mant a p + 1 < pow2 p} ->
    Tot (r:floating_point{r.prec = p /\ r.sign = a.sign /\
                          rndn_value_cond a p r /\ rndn_range_cond a p r})

let rndn_spec_branch2 a p =
    let rmant = main_mant a p + 1 in
    let rexp = a.exp + a.prec - p in
    let r = {sign = a.sign; prec = p; mant = rmant; exp = rexp} in
    let d = rndn_def a p in
    let elb = min a.exp rexp in
    rb_spec_value_lemma a p;
    sb_spec_value_lemma a p;
    lemma_pow2_mul (a.prec - p) (d.exp - elb);
    rndn_value_imp_range_lemma a p r;
    r
    
val rndn_spec_branch3: a:floating_point -> 
    p:pos{p < a.prec /\ rb_spec a p = true /\
         (sb_spec a p = true \/ (sb_spec a p = false /\ main_mant a p % 2 = 1)) /\
	 main_mant a p + 1 = pow2 p} ->
    Tot (r:floating_point{r.prec = p /\ r.sign = a.sign /\
                          rndn_value_cond a p r /\ rndn_range_cond a p r})

let rndn_spec_branch3 a p =
    let rmant = pow2 (p - 1) in
    let rexp = a.exp + a.prec - p + 1 in
    let r = {sign = a.sign; prec = p; mant = rmant; exp = rexp} in
    let d = rndn_def a p in
    let elb = min d.exp rexp in
    rb_spec_value_lemma a p;
    sb_spec_value_lemma a p;
    lemma_pow2_mul (a.prec - p) (d.exp - elb);
    rndn_value_imp_range_lemma a p r;
    r

let rndn_spec a p = 
    if a.prec <= p then
        rnd_large_p a p
    else if rb_spec a p = false || (sb_spec a p = false && main_mant a p % 2 = 0) then 
        rndn_spec_branch1 a p
    else if main_mant a p + 1 < pow2 p then
        rndn_spec_branch2 a p
    else
        rndn_spec_branch3 a p
