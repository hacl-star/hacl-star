module MPFR.Dyadic

open FStar.Mul
open MPFR.Maths

#set-options "--z3refresh --z3rlimit 20 --max_fuel 1 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 0"

(* Arbitrary precision floating point number: significand * 2 ^ exponent 
 * this allows multiple representations for one value. *)
noeq type dyadic = {significand:int; exponent:int}

let mk_dyadic m x = {significand = m; exponent = x}
    
(* Constants *)
let zero_dyadic = mk_dyadic 0 0

let unit_dyadic x = mk_dyadic 1 x

(* Evaluation to integer after adding a sufficient large exponent 
 * Maybe evaluate to a real number when F* have one. *)
let eval_i d (elb:int{d.exponent - elb >= 0}) = d.significand * pow2 (d.exponent - elb)

(* Comparison *)
let eq (a:dyadic) (b:dyadic) = let elb = min a.exponent b.exponent in eval_i a elb = eval_i b elb
let gt (a:dyadic) (b:dyadic) = let elb = min a.exponent b.exponent in eval_i a elb > eval_i b elb
let ge (a:dyadic) (b:dyadic) = let elb = min a.exponent b.exponent in eval_i a elb >= eval_i b elb
let lt (a:dyadic) (b:dyadic) = let elb = min a.exponent b.exponent in eval_i a elb < eval_i b elb
let le (a:dyadic) (b:dyadic) = let elb = min a.exponent b.exponent in eval_i a elb <= eval_i b elb

(* Negation post-condition:
 * r.mant * 2 ^ (r.exp - elb) = - a.mant * 2 ^ (a.exp - elb)
 * is equivalent to
 * r.mant * 2 ^ r.exp = - a.mant * 2 ^ a.exp *)
val fneg: a:dyadic -> Tot (r:dyadic{
    let elb = a.exponent in
    r.exponent >= elb /\
    eval_i r elb = - eval_i a elb})
    
let fneg a = mk_dyadic (- a.significand) a.exponent

let fabs a = if ge a zero_dyadic then a else fneg a

(* Addition post-condition:
 * a.mant * 2 ^ (a.exp - elb) + b.mant * 2 ^ (b.exp - elb) = r.mant * 2 ^ (r.exp - elb)
 * is equivalent to
 * a.mant * 2 ^ a.exp + b.mant * 2 ^ b.exp = r.mant * 2 ^ r.exp *)
val fadd: a:dyadic -> b:dyadic -> Tot (r:dyadic{
    let elb = min a.exponent b.exponent in
    r.exponent >= elb /\
    eval_i a elb + eval_i b elb = eval_i r elb})
    
let fadd a b =
    let elb = min a.exponent b.exponent in
    mk_dyadic (a.significand * pow2 (a.exponent - elb) + b.significand * pow2 (b.exponent - elb)) elb
    
(* Subtraction post-condition
 * a.mant * 2 ^ (a.exp - elb) - b.mant * 2 ^ (b.exp - elb) = r.mant * 2 ^ (r.exp - elb)
 * is equivalent to
 * a.mant * 2 ^ a.exp - b.mant * 2 ^ b.exp = r.mant * 2 ^ r.exp *)
val fsub: a:dyadic -> b:dyadic -> Tot (r:dyadic{
    let elb = min a.exponent b.exponent in
    r.exponent >= elb /\
    eval_i a elb - eval_i b elb = eval_i r elb})
    
let fsub a b = fadd a (fneg b)

(* Multiplication post-condition
 * a.mant * 2 ^ (a.exp - elb) * b.mant * 2 ^ (b.exp - elb) = r.mant * 2 ^ (r.exp - 2 * elb)
 * is equivalent to
 * a.mant * 2 ^ a.exp * b.mant * 2 ^ b.exp = r.mant * 2 ^ r.exp *)
val fmul: a:dyadic -> b:dyadic -> Tot (r:dyadic{
    let elb = min a.exponent b.exponent in
    r.exponent >= 2 * elb /\
    eval_i a elb * eval_i b elb = eval_i r (2 * elb)})
    
let fmul a b =
    let elb = min a.exponent b.exponent in
    lemma_pow2_mul (a.exponent - elb) (b.exponent - elb);
    mk_dyadic (a.significand * b.significand) (a.exponent + b.exponent)

(* Pow2 Division post-condition
 * a.mant * 2 ^ (a.exp - elb) = r.mant * 2 ^ (r.exp - elb) * 2 ^ e
 * is equivalent to
 * a.mant * 2 ^ a.exp / 2 ^ e = r.mant * 2 ^ r.exp *)
val fdiv_pow2: a:dyadic -> e:nat -> Tot (r:dyadic{
    let elb = a.exponent - e in
    r.exponent >= elb /\
    eval_i a elb = eval_i r elb * pow2 e})
    
let fdiv_pow2 a e = mk_dyadic a.significand (a.exponent - e)

(* Infix notations *)
unfold let op_Equals_Dot  = eq
unfold let op_Greater_Dot  = gt
unfold let op_Greater_Equals_Dot = ge
unfold let op_Less_Dot  = lt
unfold let op_Less_Equals_Dot = le
unfold let op_Plus_Dot  = fadd
unfold let op_Subtraction_Dot  = fsub
unfold let op_Star_Dot  = fmul


(* Lemmas *)
val dyadic_eq_symm_lemma: a:dyadic -> b:dyadic -> Lemma
    (requires (a =. b))
    (ensures  (b =. a))
    [SMTPat (a =. b)]
let dyadic_eq_symm_lemma a b = ()

val dyadic_gt_symm_lemma: a:dyadic -> b:dyadic -> Lemma
    (requires (a >. b))
    (ensures  (b <. a))
let dyadic_gt_symm_lemma a b = ()

val dyadic_ge_symm_lemma: a:dyadic -> b:dyadic -> Lemma
    (requires (a >=. b))
    (ensures  (b <=. a))
let dyadic_ge_symm_lemma a b = ()

val dyadic_lt_symm_lemma: a:dyadic -> b:dyadic -> Lemma
    (requires (a <. b))
    (ensures  (b >. a))
let dyadic_lt_symm_lemma a b = ()

val dyadic_le_symm_lemma: a:dyadic -> b:dyadic -> Lemma
    (requires (a <=. b))
    (ensures  (b >=. a))
let dyadic_le_symm_lemma a b = ()

val dyadic_eq_trans_lemma: a:dyadic -> b:dyadic -> c:dyadic -> Lemma
    (requires (a =. b /\ b =. c))
    (ensures  (a =. c))
    [SMTPat (a =. b); SMTPat (b =. c)]

let dyadic_eq_trans_lemma a b c =
    let elbab = min a.exponent b.exponent in
    let elbbc = min b.exponent c.exponent in
    let elbac = min a.exponent c.exponent in
    let elb = min elbab elbbc in
    lemma_pow2_mul (a.exponent - elbab) (elbab - elb);
    lemma_pow2_mul (a.exponent - elbac) (elbac - elb);
    lemma_pow2_mul (b.exponent - elbab) (elbab - elb);
    lemma_pow2_mul (b.exponent - elbbc) (elbbc - elb);
    lemma_pow2_mul (c.exponent - elbac) (elbac - elb);
    lemma_pow2_mul (c.exponent - elbbc) (elbbc - elb)

val dyadic_gt_trans_lemma: a:dyadic -> b:dyadic -> c:dyadic -> Lemma
    (requires ((a >=. b /\ b >. c) \/ (a >. b /\ b >=. c)))
    (ensures  (a >. c))
    [SMTPatOr [[SMTPat (a  >. b); SMTPat (b  >. c)];
               [SMTPat (a  =. b); SMTPat (b  >. c)];
               [SMTPat (a  >. b); SMTPat (b  =. c)];
               [SMTPat (a >=. b); SMTPat (b  >. c)];
               [SMTPat (a  >. b); SMTPat (b >=. c)]]]

let dyadic_gt_trans_lemma a b c =
    let elbab = min a.exponent b.exponent in
    let elbbc = min b.exponent c.exponent in
    let elbac = min a.exponent c.exponent in
    let elb = min elbab elbbc in
    lemma_pow2_mul (a.exponent - elbab) (elbab - elb);
    lemma_pow2_mul (a.exponent - elbac) (elbac - elb);
    lemma_pow2_mul (b.exponent - elbab) (elbab - elb);
    lemma_pow2_mul (b.exponent - elbbc) (elbbc - elb);
    lemma_pow2_mul (c.exponent - elbac) (elbac - elb);
    lemma_pow2_mul (c.exponent - elbbc) (elbbc - elb)
    
val dyadic_ge_trans_lemma: a:dyadic -> b:dyadic -> c:dyadic -> Lemma
    (requires (a >=. b /\ b >=. c))
    (ensures  (a >=. c))
    [SMTPatOr [[SMTPat (a >=. b); SMTPat (b >=. c)];
               [SMTPat (a  =. b); SMTPat (b >=. c)];
               [SMTPat (a >=. b); SMTPat (b  =. c)]]]

let dyadic_ge_trans_lemma a b c =
    let elbab = min a.exponent b.exponent in
    let elbbc = min b.exponent c.exponent in
    let elbac = min a.exponent c.exponent in
    let elb = min elbab elbbc in
    lemma_pow2_mul (a.exponent - elbab) (elbab - elb);
    lemma_pow2_mul (a.exponent - elbac) (elbac - elb);
    lemma_pow2_mul (b.exponent - elbab) (elbab - elb);
    lemma_pow2_mul (b.exponent - elbbc) (elbbc - elb);
    lemma_pow2_mul (c.exponent - elbac) (elbac - elb);
    lemma_pow2_mul (c.exponent - elbbc) (elbbc - elb)
    
val dyadic_lt_trans_lemma: a:dyadic -> b:dyadic -> c:dyadic -> Lemma
    (requires ((a <=. b /\ b <. c) \/ (a <. b /\ b <=. c)))
    (ensures  (a <. c))
    [SMTPatOr [[SMTPat (a  <. b); SMTPat (b  <. c)];
               [SMTPat (a  =. b); SMTPat (b  <. c)];
               [SMTPat (a  <. b); SMTPat (b  =. c)];
               [SMTPat (a <=. b); SMTPat (b  <. c)];
               [SMTPat (a  <. b); SMTPat (b <=. c)]]]
	       
let dyadic_lt_trans_lemma a b c = 
    let elbab = min a.exponent b.exponent in
    let elbbc = min b.exponent c.exponent in
    let elbac = min a.exponent c.exponent in
    let elb = min elbab elbbc in
    lemma_pow2_mul (a.exponent - elbab) (elbab - elb);
    lemma_pow2_mul (a.exponent - elbac) (elbac - elb);
    lemma_pow2_mul (b.exponent - elbab) (elbab - elb);
    lemma_pow2_mul (b.exponent - elbbc) (elbbc - elb);
    lemma_pow2_mul (c.exponent - elbac) (elbac - elb);
    lemma_pow2_mul (c.exponent - elbbc) (elbbc - elb)
    
val dyadic_le_trans_lemma: a:dyadic -> b:dyadic -> c:dyadic -> Lemma
    (requires (a <=. b /\ b <=. c))
    (ensures  (a <=. c))
    [SMTPatOr [[SMTPat (a <=. b); SMTPat (b <=. c)];
               [SMTPat (a  =. b); SMTPat (b <=. c)];
               [SMTPat (a <=. b); SMTPat (b  =. c)]]]
	       
let dyadic_le_trans_lemma a b c = 
    let elbab = min a.exponent b.exponent in
    let elbbc = min b.exponent c.exponent in
    let elbac = min a.exponent c.exponent in
    let elb = min elbab elbbc in
    lemma_pow2_mul (a.exponent - elbab) (elbab - elb);
    lemma_pow2_mul (a.exponent - elbac) (elbac - elb);
    lemma_pow2_mul (b.exponent - elbab) (elbab - elb);
    lemma_pow2_mul (b.exponent - elbbc) (elbbc - elb);
    lemma_pow2_mul (c.exponent - elbac) (elbac - elb);
    lemma_pow2_mul (c.exponent - elbbc) (elbbc - elb)

val fadd_eq_lemma: a:dyadic -> b:dyadic -> c:dyadic -> Lemma
    (requires (b =. c))
    (ensures  (a +. b =. a +. c))
    [SMTPat (a +. b); SMTPat (b =. c); SMTPat (a +. c)]

let fadd_eq_lemma a b c =
    let elbab = min a.exponent b.exponent in
    let elbac = min a.exponent c.exponent in
    let elbbc = min b.exponent c.exponent in
    let elb = min elbab elbac in
    lemma_distr_add_right (pow2 (elbab - elb)) (a.significand * pow2 (a.exponent - elbab)) (b.significand * pow2 (b.exponent - elbab));
    lemma_pow2_mul (a.exponent - elbab) (elbab - elb);
    lemma_pow2_mul (b.exponent - elbab) (elbab - elb);
    lemma_distr_add_right (pow2 (elbac - elb)) (a.significand * pow2 (a.exponent - elbac)) (c.significand * pow2 (c.exponent - elbac));
    lemma_pow2_mul (a.exponent - elbac) (elbac - elb);
    lemma_pow2_mul (c.exponent - elbac) (elbac - elb);
    lemma_pow2_mul (b.exponent - elbbc) (elbbc - elb);
    lemma_pow2_mul (c.exponent - elbbc) (elbbc - elb)

val fadd_comm_lemma: a:dyadic -> b:dyadic -> Lemma
    (a +. b =. b +. a)
    [SMTPat (a +. b)]
    
let fadd_comm_lemma a b = ()

val fadd_asso_lemma: a:dyadic -> b:dyadic -> c:dyadic -> Lemma
    (a +. b +. c =. a +. (b +. c))
    [SMTPat (a +. (b +. c))]

let fadd_asso_lemma a b c =
    let elbab = min a.exponent b.exponent in
    let elbbc = min b.exponent c.exponent in
    let elb = min elbab elbbc in
    lemma_distr_add_right (pow2 (elbab - elb)) (a.significand * pow2 (a.exponent - elbab)) (b.significand * pow2 (b.exponent - elbab));
    lemma_pow2_mul (a.exponent - elbab) (elbab - elb);
    lemma_pow2_mul (b.exponent - elbab) (elbab - elb);
    lemma_distr_add_right (pow2 (elbbc - elb)) (b.significand * pow2 (b.exponent - elbbc)) (c.significand * pow2 (c.exponent - elbbc));
    lemma_pow2_mul (b.exponent - elbbc) (elbbc - elb);
    lemma_pow2_mul (c.exponent - elbbc) (elbbc - elb)
