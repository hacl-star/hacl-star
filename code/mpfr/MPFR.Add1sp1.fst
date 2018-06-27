module MPFR.Add1sp1
module ST = FStar.HyperStack.ST

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Buffer
open FStar.UInt64
open FStar.Int.Cast
open FStar.Mul
open MPFR.Lib
open MPFR.Lib.Spec
open MPFR.Rounding.Spec
open MPFR.Lemmas

module I64 = FStar.Int64
module I32 = FStar.Int32
module U32 = FStar.UInt32
module Spec = MPFR.Add.Spec

(*
#set-options "--z3refresh --z3rlimit 20 --log_queries --using_facts_from Prims --using_facts_from FStar.Int,FStar.UInt --using_facts_from FStar.Int32 --using_facts_from FStar.UInt32 --using_facts_from FStar.UInt64 --using_facts_from FStar.Int64 --using_facts_from MPFR.Lib --using_facts_from MPFR.Add1sp1 --smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr native"
*)

#set-options "--z3refresh --z3rlimit 5 --max_fuel 1 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 0"

(* Intermediate calculation result *)
type state = {
    sgn: i32;
    ax: i32;
    am: mp_limb_t;
    rb: mp_limb_t;
    sb: mp_limb_t
}

let mk_state s ax am rb sb = {
    sgn = s;
    ax = ax;
    am = am;
    rb = rb;
    sb = sb
}

private let mpfr_overflow (rnd:mpfr_rnd_t) (sign:mpfr_sign_t) = mk_state sign 0l 0uL 0uL 0uL

let valid_state (s:state) (p:mpfr_prec_t) = mpfr_d_val0_cond s.am /\ mpfr_d_valn_cond s.am p

(* BGreater1 *)
val mpfr_add1sp1_gt_valid_input_lemma:
    bx:mpfr_exp_t ->
    bm:mp_limb_t{mpfr_d_val0_cond bm} -> 
    cx:mpfr_exp_t{I32.v bx > I32.v cx} ->
    cm:mp_limb_t{mpfr_d_val0_cond cm} -> 
    p:mpfr_prec_t{U32.v p < U32.v gmp_NUMB_BITS /\ mpfr_d_valn_cond bm p /\ mpfr_d_valn_cond cm p} -> 
    Lemma (let b = {sign = 1; prec = U32.v p;
                    mant = v bm / pow2 (64 - U32.v p); exp = I32.v bx - U32.v p} in
           let c = {sign = 1; prec = U32.v p;
	            mant = v cm / pow2 (64 - U32.v p); exp = I32.v cx - U32.v p} in
	   fp_cond b /\ mpfr_range_cond b /\ fp_cond c /\ mpfr_range_cond c)
	   
let mpfr_add1sp1_gt_valid_input_lemma bx bm cx cm p =
    lemma_pow2_div 63 (64 - U32.v p);
    let b = {sign = 1; prec = U32.v p;
             mant = v bm / pow2 (64 - U32.v p); exp = I32.v bx - U32.v p} in
    lemma_pow2_div_lt (v bm) 64 (64 - U32.v p);
    lemma_div_le (pow2 63) (v bm) (pow2 (64 - U32.v p));
    let c = {sign = 1; prec = U32.v p;
             mant = v cm / pow2 (64 - U32.v p); exp = I32.v cx - U32.v p} in
    lemma_pow2_div_lt (v cm) 64 (64 - U32.v p);
    lemma_div_le (pow2 63) (v cm) (pow2 (64 - U32.v p))

let mpfr_add1sp1_gt_mant_cond 
    (bx:mpfr_exp_t)
    (bm:mp_limb_t{mpfr_d_val0_cond bm})
    (cx:mpfr_exp_t{I32.v bx > I32.v cx})
    (cm:mp_limb_t{mpfr_d_val0_cond cm})
    (p:mpfr_prec_t{U32.v p < U32.v gmp_NUMB_BITS /\ mpfr_d_valn_cond bm p /\ mpfr_d_valn_cond cm p}) 
    (st:state) =
    let b = {sign = 1; prec = U32.v p;
             mant = v bm / pow2 (64 - U32.v p); exp = I32.v bx - U32.v p} in
    let c = {sign = 1; prec = U32.v p;
             mant = v cm / pow2 (64 - U32.v p); exp = I32.v cx - U32.v p} in
    mpfr_add1sp1_gt_valid_input_lemma bx bm cx cm p;
    let r = Spec.add b c in
    v st.am / pow2 (64 - U32.v p) = main_mant r (U32.v p)
    
let mpfr_add1sp1_gt_rb_cond 
    (bx:mpfr_exp_t)
    (bm:mp_limb_t{mpfr_d_val0_cond bm})
    (cx:mpfr_exp_t{I32.v bx > I32.v cx})
    (cm:mp_limb_t{mpfr_d_val0_cond cm})
    (p:mpfr_prec_t{U32.v p < U32.v gmp_NUMB_BITS /\ mpfr_d_valn_cond bm p /\ mpfr_d_valn_cond cm p}) 
    (st:state) =
    let b = {sign = 1; prec = U32.v p;
             mant = v bm / pow2 (64 - U32.v p); exp = I32.v bx - U32.v p} in
    let c = {sign = 1; prec = U32.v p;
             mant = v cm / pow2 (64 - U32.v p); exp = I32.v cx - U32.v p} in
    mpfr_add1sp1_gt_valid_input_lemma bx bm cx cm p;
    let r = Spec.add b c in
    ((v st.rb <> 0) = rb_spec r (U32.v p))

let mpfr_add1sp1_gt_sb_cond 
    (bx:mpfr_exp_t)
    (bm:mp_limb_t{mpfr_d_val0_cond bm})
    (cx:mpfr_exp_t{I32.v bx > I32.v cx})
    (cm:mp_limb_t{mpfr_d_val0_cond cm})
    (p:mpfr_prec_t{U32.v p < U32.v gmp_NUMB_BITS /\ mpfr_d_valn_cond bm p /\ mpfr_d_valn_cond cm p}) 
    (st:state) =
    let b = {sign = 1; prec = U32.v p;
             mant = v bm / pow2 (64 - U32.v p); exp = I32.v bx - U32.v p} in
    let c = {sign = 1; prec = U32.v p;
             mant = v cm / pow2 (64 - U32.v p); exp = I32.v cx - U32.v p} in
    mpfr_add1sp1_gt_valid_input_lemma bx bm cx cm p;
    let r = Spec.add b c in
    ((v st.sb <> 0) = sb_spec r (U32.v p))

(*
let mpfr_add1sp1_gt_exp_cond 
    (bx:mpfr_exp_t)
    (bm:mp_limb_t{mpfr_d_val0_cond bm})
    (cx:mpfr_exp_t{I32.v bx > I32.v cx})
    (cm:mp_limb_t{mpfr_d_val0_cond cm})
    (p:mpfr_prec_t{U32.v p < U32.v gmp_NUMB_BITS /\ mpfr_d_valn_cond bm p /\ mpfr_d_valn_cond cm p}) 
    (st:state) =
    let b = {sign = 1; prec = U32.v p;
             mant = v bm / pow2 (64 - U32.v p); exp = I32.v bx - U32.v p} in
    let c = {sign = 1; prec = U32.v p;
             mant = v cm / pow2 (64 - U32.v p); exp = I32.v cx - U32.v p} in
    mpfr_add1sp1_gt_valid_input_lemma bx bm cx cm p;
    let r = Spec.add b c in
    I32.v st.ax = r.exp
*)

(* TODO: replace ax by bx *)
val mpfr_add1sp1_gt_branch1_valid_lemma:
    bx:mpfr_exp_t ->
    bm:mp_limb_t{mpfr_d_val0_cond bm} -> 
    cx:mpfr_exp_t{I32.v bx > I32.v cx} ->
    cm:mp_limb_t{mpfr_d_val0_cond cm} -> 
    p:mpfr_prec_t{U32.v p < U32.v gmp_NUMB_BITS /\ mpfr_d_valn_cond bm p /\ mpfr_d_valn_cond cm p} -> 
    sh:u32{U32.v sh = U32.v gmp_NUMB_BITS - U32.v p} ->
    d:u32{U32.v d = I32.v bx - I32.v cx /\ U32.v d < U32.v sh} -> Lemma (
    let sh_high = mpfr_LIMB_ONE <<^ U32.(sh -^ 1ul) in
    let mask = mpfr_LIMB_MASK sh in
    let am = bm +%^ (cm >>^ d) in
    let (am, ax) = 
	if am <^ bm then 
	    (mpfr_LIMB_HIGHBIT |^ (am >>^ 1ul), I32.(bx +^ 1l))
	else (am, bx) in
    let rb = am &^ sh_high in
    let sb = (am &^ mask) ^^ rb in
    let am = am &^ (lognot mask) in
    let st = mk_state 0l ax am rb sb in
    valid_state st p)

let mpfr_add1sp1_gt_branch1_valid_lemma bx bm cx cm p sh d =
    let sh_high = mpfr_LIMB_ONE <<^ U32.(sh -^ 1ul) in
    let mask = mpfr_LIMB_MASK sh in
    let am = bm +%^ (cm >>^ d) in
    let (am, ax) = 
	if am <^ bm then begin
	    lemma_ge_pow2_imp_fst_bit mpfr_LIMB_HIGHBIT;
	    lemma_fst_bit_imp_ge_pow2 (mpfr_LIMB_HIGHBIT |^ (am >>^ 1ul));
	    (mpfr_LIMB_HIGHBIT |^ (am >>^ 1ul), I32.(bx +^ 1l))
	end else begin 
	    (am, bx) 
	end in
    lemma_ge_pow2_imp_fst_bit am;
    let rb = am &^ sh_high in
    let sb = (am &^ mask) ^^ rb in
    let am = am &^ (lognot mask) in
    lemma_fst_bit_imp_ge_pow2 am;
    lemma_tl_zero_imp_mod_pow2 am (U32.v sh)
    
val mpfr_add1sp1_gt_branch1_aux_tm_mod_lemma:
    bx:mpfr_exp_t ->
    bm:mp_limb_t{mpfr_d_val0_cond bm} -> 
    cx:mpfr_exp_t{I32.v bx > I32.v cx} ->
    cm:mp_limb_t{mpfr_d_val0_cond cm} -> 
    p:mpfr_prec_t{U32.v p < U32.v gmp_NUMB_BITS /\ mpfr_d_valn_cond bm p /\ mpfr_d_valn_cond cm p} -> 
    sh:u32{U32.v sh = U32.v gmp_NUMB_BITS - U32.v p} ->
    d:u32{U32.v d = I32.v bx - I32.v cx /\ U32.v d < U32.v sh} -> Lemma (
    let tm = v bm + v cm / pow2 (U32.v d) in
    tm % pow2 (U32.v sh - U32.v d) = 0)

let mpfr_add1sp1_gt_branch1_aux_tm_mod_lemma bx bm cx cm p sh d =
    lemma_pow2_mod_mod (v bm) (U32.v sh) (U32.v sh - U32.v d);
    lemma_pow2_mod_div (v cm) (U32.v sh) (U32.v d);
    lemma_mod_distr (v bm) (v cm / pow2 (U32.v d)) (pow2 (U32.v sh - U32.v d))

val mpfr_add1sp1_gt_branch1_aux_rm_tm_lemma:
    bx:mpfr_exp_t ->
    bm:mp_limb_t{mpfr_d_val0_cond bm} -> 
    cx:mpfr_exp_t{I32.v bx > I32.v cx} ->
    cm:mp_limb_t{mpfr_d_val0_cond cm} -> 
    p:mpfr_prec_t{U32.v p < U32.v gmp_NUMB_BITS /\ mpfr_d_valn_cond bm p /\ mpfr_d_valn_cond cm p} -> 
    sh:u32{U32.v sh = U32.v gmp_NUMB_BITS - U32.v p} ->
    d:u32{U32.v d = I32.v bx - I32.v cx /\ U32.v d < U32.v sh} -> Lemma (
    let b = {sign = 1; prec = U32.v p;
             mant = v bm / pow2 (U32.v sh); exp = I32.v bx - U32.v p} in
    let c = {sign = 1; prec = U32.v p;
             mant = v cm / pow2 (U32.v sh); exp = I32.v cx - U32.v p} in
    mpfr_add1sp1_gt_valid_input_lemma bx bm cx cm p;
    let r = Spec.add b c in
    let tm = v bm + v cm / pow2 (U32.v d) in
    r.mant * pow2 (U32.v sh - U32.v d) = tm)

let mpfr_add1sp1_gt_branch1_aux_rm_tm_lemma bx bm cx cm p sh d =
    let b = {sign = 1; prec = U32.v p;
             mant = v bm / pow2 (U32.v sh); exp = I32.v bx - U32.v p} in
    let c = {sign = 1; prec = U32.v p;
             mant = v cm / pow2 (U32.v sh); exp = I32.v cx - U32.v p} in
    mpfr_add1sp1_gt_valid_input_lemma bx bm cx cm p;
    let r = Spec.add b c in
    //! assert(r.mant = (v bm / pow2 (U32.v sh)) * pow2 (U32.v d) + (v cm / pow2 (U32.v sh)));
    lemma_mul_div (v bm) (pow2 (U32.v d)) (pow2 (U32.v sh));
    lemma_pow2_div_div (v bm * pow2 (U32.v d)) (U32.v d) (U32.v sh - U32.v d);
    lemma_multiple_div (v bm) (pow2 (U32.v d));
    //! assert((v bm / pow2 (U32.v sh)) * pow2 (U32.v d) = v bm / pow2 (U32.v sh - U32.v d));
    lemma_pow2_div_div (v cm) (U32.v d) (U32.v sh - U32.v d);
    //! assert(v cm / pow2 (U32.v sh) = (v cm / pow2 (U32.v d)) / pow2 (U32.v sh - U32.v d));
    lemma_pow2_mod_div (v cm) (U32.v sh) (U32.v d);
    lemma_div_distr (v cm / pow2 (U32.v d)) (v bm) (pow2 (U32.v sh - U32.v d));
    let tm = v bm + v cm / pow2 (U32.v d) in
    //! assert(r.mant = tm / pow2 (U32.v sh - U32.v d));
    mpfr_add1sp1_gt_branch1_aux_tm_mod_lemma bx bm cx cm p sh d;
    //! assert(tm % pow2 (U32.v sh - U32.v d) = 0)
    lemma_mul_div tm (pow2 (U32.v sh - U32.v d)) (pow2 (U32.v sh - U32.v d));
    lemma_multiple_div tm (pow2 (U32.v sh - U32.v d))
    
val mpfr_add1sp1_gt_branch1_aux_am_tm_lemma:
    bx:mpfr_exp_t ->
    bm:mp_limb_t{mpfr_d_val0_cond bm} -> 
    cx:mpfr_exp_t{I32.v bx > I32.v cx} ->
    cm:mp_limb_t{mpfr_d_val0_cond cm} -> 
    p:mpfr_prec_t{U32.v p < U32.v gmp_NUMB_BITS /\ mpfr_d_valn_cond bm p /\ mpfr_d_valn_cond cm p} -> 
    sh:u32{U32.v sh = U32.v gmp_NUMB_BITS - U32.v p} ->
    d:u32{U32.v d = I32.v bx - I32.v cx /\ U32.v d < U32.v sh} -> Lemma (
    let b = {sign = 1; prec = U32.v p;
             mant = v bm / pow2 (U32.v sh); exp = I32.v bx - U32.v p} in
    let c = {sign = 1; prec = U32.v p;
             mant = v cm / pow2 (U32.v sh); exp = I32.v cx - U32.v p} in
    mpfr_add1sp1_gt_valid_input_lemma bx bm cx cm p;
    let r = Spec.add b c in
    let sh_high = mpfr_LIMB_ONE <<^ U32.(sh -^ 1ul) in
    let mask = mpfr_LIMB_MASK sh in
    let am = bm +%^ (cm >>^ d) in
    let (am, ax) = 
	if am <^ bm then 
	    (mpfr_LIMB_HIGHBIT |^ (am >>^ 1ul), I32.(bx +^ 1l))
	else (am, bx) in
    let tm = v bm + v cm / pow2 (U32.v d) in
    v am * pow2 (r.prec - U32.v d - U32.v p) = tm)

let mpfr_add1sp1_gt_branch1_aux_am_tm_lemma bx bm cx cm p sh d =
    let b = {sign = 1; prec = U32.v p;
             mant = v bm / pow2 (U32.v sh); exp = I32.v bx - U32.v p} in
    let c = {sign = 1; prec = U32.v p;
             mant = v cm / pow2 (U32.v sh); exp = I32.v cx - U32.v p} in
    mpfr_add1sp1_gt_valid_input_lemma bx bm cx cm p;
    let r = Spec.add b c in
    let tm = v bm + v cm / pow2 (U32.v d) in
    mpfr_add1sp1_gt_branch1_aux_rm_tm_lemma bx bm cx cm p sh d;
    //! assert(r.mant * pow2 (U32.v sh - U32.v d) = tm);
    let sh_high = mpfr_LIMB_ONE <<^ U32.(sh -^ 1ul) in
    let mask = mpfr_LIMB_MASK sh in
    let am = bm +%^ (cm >>^ d) in
    //! assert(v am = tm % pow2 64);
    let (am, ax) = 
	if am <^ bm then begin
	    //! assert(pow2 64 + v am = tm);
	    //! assert(tm >= pow2 64);
	    Spec.add_fp_lemma b c;
	    lemma_pow2_mul r.prec (U32.v sh - U32.v d);
	    //! assert(tm < pow2 (r.prec + U32.v sh - U32.v d));
	    //! assert(r.prec > p0);
	    //! assert(r.prec = p0 + 1);
	    lemma_div_distr (pow2 64) (v am) 2;
	    //! assert(pow2 63 + v am / 2 = tm / pow2 (r.prec - p0));
	    let nam = mpfr_LIMB_HIGHBIT |^ (am >>^ 1ul) in
	    lemma_logor_disjoint mpfr_LIMB_HIGHBIT (am >>^ 1ul) 63;
	    //! assert(v nam = tm / pow2 (r.prec - U32.v p - U32.v d));
	    mpfr_add1sp1_gt_branch1_aux_tm_mod_lemma bx bm cx cm p sh d;
	    lemma_pow2_mod_mod tm (U32.v sh - U32.v d) (r.prec - U32.v p - U32.v d);
	    //! assert(tm % pow2 (r.prec - U32.v p - U32.v d) = 0);
	    lemma_mul_div tm (pow2 (r.prec - U32.v p - U32.v d)) (pow2 (r.prec - U32.v p - U32.v d));
	    lemma_multiple_div tm (pow2 (r.prec - U32.v p - U32.v d));
	    //! assert(v nam * pow2 (r.prec - U32.v p - U32.v d) = tm);
	    (nam, I32.(bx +^ 1l))
	end else begin
	    //! assert(tm = v am);
	    //! assert(tm < pow2 64)
	    Spec.add_fp_lemma b c;
	    lemma_pow2_mul (r.prec - 1) (U32.v sh - U32.v d);
	    //! assert(tm >= pow2 (r.prec - 1 + U32.v sh - U32.v d));
	    //! assert(r.prec < p0 + 1);
	    //! assert(r.prec = p0);
	    //! assert(v am * pow2 (r.prec - p0) = tm);
	    (am, bx) 
	end in
    ()

val mpfr_add1sp1_gt_branch1_aux_am_rm_lemma:
    bx:mpfr_exp_t ->
    bm:mp_limb_t{mpfr_d_val0_cond bm} -> 
    cx:mpfr_exp_t{I32.v bx > I32.v cx} ->
    cm:mp_limb_t{mpfr_d_val0_cond cm} -> 
    p:mpfr_prec_t{U32.v p < U32.v gmp_NUMB_BITS /\ mpfr_d_valn_cond bm p /\ mpfr_d_valn_cond cm p} -> 
    sh:u32{U32.v sh = U32.v gmp_NUMB_BITS - U32.v p} ->
    d:u32{U32.v d = I32.v bx - I32.v cx /\ U32.v d < U32.v sh} -> Lemma (
    let b = {sign = 1; prec = U32.v p;
             mant = v bm / pow2 (U32.v sh); exp = I32.v bx - U32.v p} in
    let c = {sign = 1; prec = U32.v p;
             mant = v cm / pow2 (U32.v sh); exp = I32.v cx - U32.v p} in
    mpfr_add1sp1_gt_valid_input_lemma bx bm cx cm p;
    let r = Spec.add b c in
    let sh_high = mpfr_LIMB_ONE <<^ U32.(sh -^ 1ul) in
    let mask = mpfr_LIMB_MASK sh in
    let am = bm +%^ (cm >>^ d) in
    let (am, ax) = 
	if am <^ bm then 
	    (mpfr_LIMB_HIGHBIT |^ (am >>^ 1ul), I32.(bx +^ 1l))
	else (am, bx) in
    v am = r.mant * pow2 (64 - r.prec))

let mpfr_add1sp1_gt_branch1_aux_am_rm_lemma bx bm cx cm p sh d =
    let b = {sign = 1; prec = U32.v p;
             mant = v bm / pow2 (U32.v sh); exp = I32.v bx - U32.v p} in
    let c = {sign = 1; prec = U32.v p;
             mant = v cm / pow2 (U32.v sh); exp = I32.v cx - U32.v p} in
    mpfr_add1sp1_gt_valid_input_lemma bx bm cx cm p;
    let r = Spec.add b c in
    let tm = v bm + v cm / pow2 (U32.v d) in
    mpfr_add1sp1_gt_branch1_aux_rm_tm_lemma bx bm cx cm p sh d;
    //! assert(r.mant * pow2 (U32.v sh - U32.v d) = tm);
    let sh_high = mpfr_LIMB_ONE <<^ U32.(sh -^ 1ul) in
    let mask = mpfr_LIMB_MASK sh in
    let am = bm +%^ (cm >>^ d) in
    let (am, ax) = 
	if am <^ bm then begin
	    (mpfr_LIMB_HIGHBIT |^ (am >>^ 1ul), I32.(bx +^ 1l))
	end else begin
	    (am, bx) 
	end in
    mpfr_add1sp1_gt_branch1_aux_am_tm_lemma bx bm cx cm p sh d;
    lemma_multiple_div (v am) (pow2 (r.prec - U32.v p - U32.v d));
    //! assert(v am = tm / pow2 (r.prec - U32.v p - U32.v d));
    lemma_pow2_mul (64 - r.prec) (r.prec - U32.v p - U32.v d);
    lemma_paren_mul_right r.mant (pow2 (64 - r.prec)) (pow2 (r.prec - U32.v p - U32.v d));
    lemma_multiple_div (r.mant * pow2 (64 - r.prec)) (pow2 (r.prec - U32.v p - U32.v d));
    //! assert(v am = r.mant * pow2 (64 - r.prec));
    ()

val mpfr_add1sp1_gt_branch1_mant_lemma:
    bx:mpfr_exp_t ->
    bm:mp_limb_t{mpfr_d_val0_cond bm} -> 
    cx:mpfr_exp_t{I32.v bx > I32.v cx} ->
    cm:mp_limb_t{mpfr_d_val0_cond cm} -> 
    p:mpfr_prec_t{U32.v p < U32.v gmp_NUMB_BITS /\ mpfr_d_valn_cond bm p /\ mpfr_d_valn_cond cm p} -> 
    sh:u32{U32.v sh = U32.v gmp_NUMB_BITS - U32.v p} ->
    d:u32{U32.v d = I32.v bx - I32.v cx /\ U32.v d < U32.v sh} -> Lemma (
    let sh_high = mpfr_LIMB_ONE <<^ U32.(sh -^ 1ul) in
    let mask = mpfr_LIMB_MASK sh in
    let am = bm +%^ (cm >>^ d) in
    let (am, ax) = 
	if am <^ bm then 
	    (mpfr_LIMB_HIGHBIT |^ (am >>^ 1ul), I32.(bx +^ 1l))
	else (am, bx) in
    let rb = am &^ sh_high in
    let sb = (am &^ mask) ^^ rb in
    let am = am &^ (lognot mask) in
    let st = mk_state 0l ax am rb sb in
    mpfr_add1sp1_gt_mant_cond bx bm cx cm p st)

let mpfr_add1sp1_gt_branch1_mant_lemma bx bm cx cm p sh d =
    let b = {sign = 1; prec = U32.v p;
             mant = v bm / pow2 (U32.v sh); exp = I32.v bx - U32.v p} in
    let c = {sign = 1; prec = U32.v p;
             mant = v cm / pow2 (U32.v sh); exp = I32.v cx - U32.v p} in
    mpfr_add1sp1_gt_valid_input_lemma bx bm cx cm p;
    let r = Spec.add b c in
    let sh_high = mpfr_LIMB_ONE <<^ U32.(sh -^ 1ul) in
    let mask = mpfr_LIMB_MASK sh in
    //! assert(v mask = pow2 (U32.v sh) - 1);
    let am = bm +%^ (cm >>^ d) in
    let (am, ax) = 
	if am <^ bm then begin
	    (mpfr_LIMB_HIGHBIT |^ (am >>^ 1ul), I32.(bx +^ 1l))
	end else begin
	    (am, bx) 
	end in
    mpfr_add1sp1_gt_branch1_aux_am_rm_lemma bx bm cx cm p sh d;
    lemma_multiple_div r.mant (pow2 (64 - r.prec));
    //! assert(v am / pow2 (64 - r.prec) = r.mant);
    lemma_pow2_div_div (v am) (64 - r.prec) (r.prec - U32.v p);
    //! assert(v am / pow2 (64 - U32.v p) = main_mant r (U32.v p));
    let rb = am &^ sh_high in
    let sb = (am &^ mask) ^^ rb in
    UInt.nth_lemma #64 (UInt.shift_right #64 (v am) (64 - U32.v p)) (UInt.shift_right #64 (UInt.logand (v am) (UInt.lognot (v mask))) (64 - U32.v p));
    //! assert(v am / pow2 (64 - U32.v p) = v (am &^ lognot mask) / pow2 (64 - U32.v p));
    let am = am &^ (lognot mask) in
    let st = mk_state 0l ax am rb sb in
    ()
    
val mpfr_add1sp1_gt_branch1_rb_lemma:
    bx:mpfr_exp_t ->
    bm:mp_limb_t{mpfr_d_val0_cond bm} -> 
    cx:mpfr_exp_t{I32.v bx > I32.v cx} ->
    cm:mp_limb_t{mpfr_d_val0_cond cm} -> 
    p:mpfr_prec_t{U32.v p < U32.v gmp_NUMB_BITS /\ mpfr_d_valn_cond bm p /\ mpfr_d_valn_cond cm p} -> 
    sh:u32{U32.v sh = U32.v gmp_NUMB_BITS - U32.v p} ->
    d:u32{U32.v d = I32.v bx - I32.v cx /\ U32.v d < U32.v sh} -> Lemma (
    let sh_high = mpfr_LIMB_ONE <<^ U32.(sh -^ 1ul) in
    let mask = mpfr_LIMB_MASK sh in
    let am = bm +%^ (cm >>^ d) in
    let (am, ax) = 
	if am <^ bm then 
	    (mpfr_LIMB_HIGHBIT |^ (am >>^ 1ul), I32.(bx +^ 1l))
	else (am, bx) in
    let rb = am &^ sh_high in
    let sb = (am &^ mask) ^^ rb in
    let am = am &^ (lognot mask) in
    let st = mk_state 0l ax am rb sb in
    mpfr_add1sp1_gt_rb_cond bx bm cx cm p st)
    
let mpfr_add1sp1_gt_branch1_rb_lemma bx bm cx cm p sh d =
    let b = {sign = 1; prec = U32.v p;
             mant = v bm / pow2 (U32.v sh); exp = I32.v bx - U32.v p} in
    let c = {sign = 1; prec = U32.v p;
             mant = v cm / pow2 (U32.v sh); exp = I32.v cx - U32.v p} in
    mpfr_add1sp1_gt_valid_input_lemma bx bm cx cm p;
    let r = Spec.add b c in
    let tm = v bm + v cm / pow2 (U32.v d) in
    let sh_high = mpfr_LIMB_ONE <<^ U32.(sh -^ 1ul) in
    lemma_pow2_small_mod (U32.v sh - 1) 64;
    //! assert(v sh_high = pow2 (U32.v sh - 1));
    let mask = mpfr_LIMB_MASK sh in
    let am = bm +%^ (cm >>^ d) in
    let (am, ax) = 
	if am <^ bm then begin
	    (mpfr_LIMB_HIGHBIT |^ (am >>^ 1ul), I32.(bx +^ 1l))
	end else begin
	    (am, bx) 
	end in
    mpfr_add1sp1_gt_branch1_aux_am_rm_lemma bx bm cx cm p sh d;
    lemma_multiple_div r.mant (pow2 (64 - r.prec));
    //! assert(v am / pow2 (64 - r.prec) = r.mant);
    if r.prec = 64 then () else UInt.slice_left_lemma (UInt.to_vec (v am)) r.prec;
    //! assert(Seq.slice (UInt.to_vec (v am)) 0 r.prec = UInt.to_vec #r.prec r.mant);
    //! assert(UInt.nth (v am) (U32.v p) = UInt.nth #r.prec r.mant (U32.v p));
    let rb = am &^ sh_high in
    lemma_bit_mask_value am sh_high (U32.v p);
    //! assert(v rb = (if UInt.nth (v am) (U32.v p) then (v sh_high) else 0));
    if rb_spec r (U32.v p) then assert(v rb <> 0) else assert(v rb = 0);
    let sb = (am &^ mask) ^^ rb in
    let am = am &^ (lognot mask) in
    let st = mk_state 0l ax am rb sb in
    ()
    
val mpfr_add1sp1_gt_branch1_sb_lemma:
    bx:mpfr_exp_t ->
    bm:mp_limb_t{mpfr_d_val0_cond bm} -> 
    cx:mpfr_exp_t{I32.v bx > I32.v cx} ->
    cm:mp_limb_t{mpfr_d_val0_cond cm} -> 
    p:mpfr_prec_t{U32.v p < U32.v gmp_NUMB_BITS /\ mpfr_d_valn_cond bm p /\ mpfr_d_valn_cond cm p} -> 
    sh:u32{U32.v sh = U32.v gmp_NUMB_BITS - U32.v p} ->
    d:u32{U32.v d = I32.v bx - I32.v cx /\ U32.v d < U32.v sh} -> Lemma (
    let sh_high = mpfr_LIMB_ONE <<^ U32.(sh -^ 1ul) in
    let mask = mpfr_LIMB_MASK sh in
    let am = bm +%^ (cm >>^ d) in
    let (am, ax) = 
	if am <^ bm then 
	    (mpfr_LIMB_HIGHBIT |^ (am >>^ 1ul), I32.(bx +^ 1l))
	else (am, bx) in
    let rb = am &^ sh_high in
    let sb = (am &^ mask) ^^ rb in
    let am = am &^ (lognot mask) in
    let st = mk_state 0l ax am rb sb in
    mpfr_add1sp1_gt_sb_cond bx bm cx cm p st)
    
let mpfr_add1sp1_gt_branch1_sb_lemma bx bm cx cm p sh d =
    let b = {sign = 1; prec = U32.v p;
             mant = v bm / pow2 (U32.v sh); exp = I32.v bx - U32.v p} in
    let c = {sign = 1; prec = U32.v p;
             mant = v cm / pow2 (U32.v sh); exp = I32.v cx - U32.v p} in
    mpfr_add1sp1_gt_valid_input_lemma bx bm cx cm p;
    let r = Spec.add b c in
    let tm = v bm + v cm / pow2 (U32.v d) in
    let sh_high = mpfr_LIMB_ONE <<^ U32.(sh -^ 1ul) in
    lemma_pow2_small_mod (U32.v sh - 1) 64;
    //! assert(v sh_high = pow2 (U32.v sh - 1));
    lemma_bit_mask sh_high (64 - U32.v sh);
    let mask = mpfr_LIMB_MASK sh in
    //! assert(v mask = pow2 (U32.v sh) - 1);
    lemma_tail_mask mask (U32.v sh);
    let rmask = mpfr_LIMB_MASK U32.(sh -^ 1ul) in
    UInt.nth_lemma #64 (v (mask ^^ sh_high)) (v rmask);
    let am = bm +%^ (cm >>^ d) in
    let (am, ax) = 
	if am <^ bm then begin
	    (mpfr_LIMB_HIGHBIT |^ (am >>^ 1ul), I32.(bx +^ 1l))
	end else begin
	    (am, bx) 
	end in
    let rb = am &^ sh_high in
    let sb = (am &^ mask) ^^ rb in
    lemma_xor_and_distr am mask sh_high;
    //! assert(sb = (am &^ rmask));
    lemma_tail_mask_value am rmask (U32.v sh - 1);
    //! assert(v sb = (v am) % pow2 (U32.v sh - 1));
    mpfr_add1sp1_gt_branch1_aux_am_rm_lemma bx bm cx cm p sh d;
    lemma_multiple_div r.mant (pow2 (64 - r.prec));
    lemma_multiple_mod r.mant (pow2 (64 - r.prec));
    //! assert(v am / pow2 (64 - r.prec) = r.mant);
    //! assert(v am % pow2 (64 - r.prec) = 0);
    lemma_pow2_mod_div (v am) (U32.v sh - 1) (64 - r.prec);
    lemma_pow2_mod_mod (v am) (U32.v sh - 1) (64 - r.prec);
    //! assert(v sb / pow2 (64 - r.prec) = r.mant % pow2 (r.prec - U32.v p - 1));
    //! assert(v sb % pow2 (64 - r.prec) = 0);
    lemma_mul_div (v sb) (pow2 (64 - r.prec)) (pow2 (64 - r.prec));
    lemma_multiple_div (v sb) (pow2 (64 - r.prec));
    //! assert(v sb = (r.mant % pow2 (r.prec - U32.v p - 1)) * pow2 (64 - r.prec));
    ()
    
unfold val mpfr_add1sp1_gt_branch1:
    bx:mpfr_exp_t ->
    bm:mp_limb_t{mpfr_d_val0_cond bm} -> 
    cx:mpfr_exp_t{I32.v bx > I32.v cx} ->
    cm:mp_limb_t{mpfr_d_val0_cond cm} -> 
    p:mpfr_prec_t{U32.v p < U32.v gmp_NUMB_BITS /\ mpfr_d_valn_cond bm p /\ mpfr_d_valn_cond cm p} -> 
    sh:u32{U32.v sh = U32.v gmp_NUMB_BITS - U32.v p} ->
    d:u32{U32.v d = I32.v bx - I32.v cx /\ U32.v d < U32.v sh} ->
    Tot (st:state{valid_state st p /\
                  mpfr_add1sp1_gt_mant_cond bx bm cx cm p st /\
                  mpfr_add1sp1_gt_rb_cond bx bm cx cm p st /\
		  mpfr_add1sp1_gt_sb_cond bx bm cx cm p st})

let mpfr_add1sp1_gt_branch1 bx bm cx cm p sh d =
    let b = {sign = 1; prec = U32.v p;
             mant = v bm / pow2 (64 - U32.v p); exp = I32.v bx - U32.v p} in
    let c = {sign = 1; prec = U32.v p;
             mant = v cm / pow2 (64 - U32.v p); exp = I32.v cx - U32.v p} in
    let sh_high = mpfr_LIMB_ONE <<^ U32.(sh -^ 1ul) in
    let mask = mpfr_LIMB_MASK sh in
    let am = bm +%^ (cm >>^ d) in
    let (am, ax) = 
	if am <^ bm then 
	   (mpfr_LIMB_HIGHBIT |^ (am >>^ 1ul), I32.(bx +^ 1l))
	else (am, bx) in
    let rb = am &^ sh_high in
    let sb = (am &^ mask) ^^ rb in
    let am = am &^ (lognot mask) in
    let st = mk_state 0l ax am rb sb in
    mpfr_add1sp1_gt_branch1_valid_lemma bx bm cx cm p sh d;
    mpfr_add1sp1_gt_branch1_mant_lemma bx bm cx cm p sh d;
    mpfr_add1sp1_gt_branch1_rb_lemma bx bm cx cm p sh d;
    mpfr_add1sp1_gt_branch1_sb_lemma bx bm cx cm p sh d;
    st

unfold val mpfr_add1sp1_gt:
    bx:mpfr_exp_t ->
    bm:mp_limb_t{mpfr_d_val0_cond bm} -> 
    cx:mpfr_exp_t{I32.v bx > I32.v cx} ->
    cm:mp_limb_t{mpfr_d_val0_cond cm} -> 
    p:mpfr_prec_t{U32.v p < U32.v gmp_NUMB_BITS /\ mpfr_d_valn_cond bm p /\ mpfr_d_valn_cond cm p} -> 
    Tot (st:state{valid_state st p /\
                  mpfr_add1sp1_gt_mant_cond bx bm cx cm p st /\
                  mpfr_add1sp1_gt_rb_cond bx bm cx cm p st /\
                  mpfr_add1sp1_gt_sb_cond bx bm cx cm p st})
    
(*
let mpfr_add1sp1_gt bx bm cx cm p =
    let sh = U32.(gmp_NUMB_BITS -^ p) in
    let sh_high = mpfr_LIMB_ONE <<^ U32.(sh -^ 1ul) in
    let d = int32_to_uint32 I32.(bx -^ cx) in
    let mask = mpfr_LIMB_MASK sh in
    if U32.(d <^ sh) then begin
        let am = bm +%^ (cm >>^ d) in
	let (am, ax) = 
	    if am <^ bm then 
	        (mpfr_LIMB_HIGHBIT |^ (am >>^ 1ul), I32.(bx +^ 1l))
	    else (am, bx) in
        let rb = am &^ sh_high in
	let sb = (am &^ mask) ^^ rb in
	let am = am &^ (lognot mask) in
	mk_state 0l ax am rb sb
    end else if U32.(d <^ gmp_NUMB_BITS) then begin
        let sb = cm <<^ U32.(gmp_NUMB_BITS -^ d) in
	let am = bm +%^ (cm >>^ d) in
	let (sb, am, ax) =
	    if am <^ bm then 
	        (sb |^ (am &^ 1uL), mpfr_LIMB_HIGHBIT |^ (am >>^ 1ul), I32.(bx +^ 1l))
	    else (sb, am, bx) in
	let rb = am &^ sh_high in
	let sb = sb |^ ((am &^ mask) ^^ rb) in
        let am = am &^ (lognot mask) in
	mk_state 0l ax am rb sb
    end else begin
        mk_state 0l bx bm 0uL 1uL
    end
*)

val mpfr_add1sp1_any: bx:i32{mpfr_EXP_COND bx} ->
                      bm:u64{mpfr_d_val0_cond bm} -> 
	              cx:i32{mpfr_EXP_COND cx} ->
		      cm:u64{mpfr_d_val0_cond cm} -> 
		      rnd_mode:mpfr_rnd_t -> 
		      p:mpfr_prec_t{U32.v U32.(gmp_NUMB_BITS -^ p) > 1 /\
		          mpfr_d_valn_cond bm p /\ mpfr_d_valn_cond cm p} -> 
		      Tot state
let mpfr_add1sp1_any bx bm cx cm rnd_mode p = 
  let sh = U32.(gmp_NUMB_BITS -^ p) in
  let sh_high = mpfr_LIMB_ONE <<^ U32.(sh -^ 1ul) in
    if I32.(bx =^ cx) then
      let am = (bm >>^ 1ul) +^ (cm >>^ 1ul) in
      let rb = am &^ sh_high in
      let am = am ^^ rb in
      let bx = I32.(bx +^ 1l) in
      mk_state 0l bx am rb 0uL
    else if I32.(bx >^ cx) then
	mpfr_add1sp1_gt bx bm cx cm rnd_mode p
    else mpfr_add1sp1_gt cx cm bx bm rnd_mode p

val add_one_ulp: sign:i32{mpfr_SIGN_COND sign} ->
                 ax:i32{mpfr_EXP_COND ax} ->
		 am:u64{mpfr_d_val0_cond am} ->
		 rnd_mode:mpfr_rnd_t -> 
		 p:u32{mpfr_PREC_COND p /\ mpfr_d_valn_cond am p} ->
		 Tot state
let add_one_ulp sign ax am rnd_mode p = 
	 let am = am +%^ (mpfr_LIMB_ONE <<^ U32.(gmp_NUMB_BITS -^ p)) in
         if (am =^ 0uL) then
            let am = mpfr_LIMB_HIGHBIT in
            if I32.(ax +^ 1l >^ gmpfr_emax) then
  	        mpfr_overflow rnd_mode sign
            else 
                mk_state sign I32.(ax +^ 1l) am 0uL 0uL
         else mk_state sign ax am 0uL 0uL

val mpfr_add1sp1_ : bx:i32{mpfr_EXP_COND bx} ->
                    bm:u64{mpfr_d_val0_cond bm} -> 
	            cx:i32{mpfr_EXP_COND cx} ->
		    cm:u64{mpfr_d_val0_cond cm} -> 
		    rnd_mode:mpfr_rnd_t -> 
		    p:mpfr_prec_t{U32.v U32.(gmp_NUMB_BITS -^ p) > 1 /\
		         mpfr_d_valn_cond bm p /\ mpfr_d_valn_cond cm p} -> 
   	            s: mpfr_sign_t ->
		    Tot state	      
let mpfr_add1sp1_ bx bm cx cm rnd_mode p sign =
  let sh = U32.(gmp_NUMB_BITS -^ p) in
  let sh_high = mpfr_LIMB_ONE <<^ U32.(sh -^ 1ul) in
  let st = mpfr_add1sp1_any bx bm cx cm rnd_mode p in
  let am = st.am in
  let ax = st.ax in
  let rb = st.rb in
  let sb = st.sb in
  if I32.(ax >^ gmpfr_emax) then
	     mpfr_overflow rnd_mode sign
  else if ((rb =^ 0uL && sb =^ 0uL) || (MPFR_RNDF? rnd_mode)) then
        mk_state sign ax am 0uL 0uL
  else if (MPFR_RNDN? rnd_mode) then
	 if ((rb =^ 0uL || (sb =^ 0uL && (am &^ (mpfr_LIMB_ONE <<^ sh)) =^ 0uL))) then (
	     let ns = neg sign in
             mk_state ns ax am 0uL 0uL)
          else (add_one_ulp sign ax am rnd_mode p)
  else if (mpfr_IS_LIKE_RNDZ rnd_mode sign) then (
             let ns = neg sign in
             mk_state ns ax am 0uL 0uL)
  else (add_one_ulp sign ax am rnd_mode p)


val mpfr_add1sp1: a:mpfr_ptr -> b:mpfr_ptr -> c:mpfr_ptr -> 
    		  rnd_mode:mpfr_rnd_t -> p:mpfr_prec_t -> Stack i32 
		  (requires (fun h -> live h a /\ live h b /\ live h c /\ 
		             length a = 1 /\ length b = 1 /\ length c = 1 /\
			     (let am = Seq.index (as_seq h a) 0 in
			     let bm = Seq.index (as_seq h b) 0 in
			     let cm = Seq.index (as_seq h c) 0 in
			     let a0 = am.mpfr_d in
			     let b0 = bm.mpfr_d in
			     let c0 = cm.mpfr_d in
			     live h a0 /\ live h b0 /\ live h c0 /\
			     disjoint a a0 /\
			     disjoint b b0 /\
			     disjoint c c0 /\
			     length a0 = 1 /\
			     length b0 = 1 /\
			     length c0 = 1 /\
			     U32.v gmp_NUMB_BITS - U32.v p > 1 /\ 
   			     U32.v gmp_NUMB_BITS - U32.v p < 32)))
		  (ensures  (fun h0 r h1 -> live h1 a /\ live h1 b /\ live h1 c /\ 
			     (let am = Seq.index (as_seq h1 a) 0 in
			     let bm = Seq.index (as_seq h1 b) 0 in
			     let cm = Seq.index (as_seq h1 c) 0 in
			     let a0 = am.mpfr_d in
			     let b0 = bm.mpfr_d in
			     let c0 = cm.mpfr_d in
			     live h1 a0 /\ live h1 b0 /\ live h1 c0 /\
		             modifies_2 a a0 h0 h1)))
#set-options "--z3refresh --z3rlimit 10"
let mpfr_add1sp1 a b c rnd_mode p = 
    let sign = mpfr_SIGN a in
    let bx = mpfr_GET_EXP b in
    let bm = mpfr_MANT b in
    let cx = mpfr_GET_EXP c in
    let cm = mpfr_MANT c in
    let h = ST.get() in
    assert (live h bm);
    assert (length bm = 1);
    let b0 = bm.(0ul) in
    let c0 = cm.(0ul) in
    let st = mpfr_add1sp1_ bx b0 cx c0 rnd_mode p sign in
    let a0 = st.am in
    let as = st.sign in
    let ax = st.ax in
    let am = mpfr_MANT a in
    am.(0ul) <- a0;
    let h1 = ST.get() in
    assert (live h1 a);
    assert (live h1 am);
    assert (modifies_1 am h h1);
    mpfr_SET_EXP a ax;
    let h2 = ST.get() in
    assert (live h2 a);
    assert (live h2 am);
    assert (modifies_1 a h1 h2);
    as


