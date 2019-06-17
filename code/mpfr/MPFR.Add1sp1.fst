module MPFR.Add1sp1

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Buffer
open FStar.UInt64
open FStar.Int.Cast
open FStar.Mul
open MPFR.Dyadic
open MPFR.Lib.Spec
open MPFR.Add1.Spec
open MPFR.Round.Spec
open MPFR.Maths

open MPFR.Lib
open MPFR.Exceptions

open MPFR.Exceptions.Lemma
open MPFR.Add1sp1.Lemma

module ST = FStar.HyperStack.ST
module I32 = FStar.Int32
module I64 = FStar.Int64
module U32 = FStar.UInt32

#set-options "--z3refresh --z3rlimit 100 --max_fuel 1 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 0"

(* implementations *)
(* intermediate results *)
private type mpfr_tmp_exp_t = x:mpfr_exp_t{I64.(x >=^ mpfr_EMIN /\ x <=^ mpfr_EMAX +^ 1L)}

noeq type state = {
    sh:mpfr_reg_prec_t;
    bx:mpfr_tmp_exp_t;
    rb:mp_limb_t;
    sb:mp_limb_t
}

let mk_state sh bx rb sb = {
    sh = sh;
    bx = bx;
    rb = rb;
    sb = sb
}
    
let mpfr_add1sp1_any_post_cond a b c h0 s h1 =
    let p = I64.v a.mpfr_prec in
    live h1 a.mpfr_d /\ live h1 b.mpfr_d /\ live h1 c.mpfr_d /\
    length a.mpfr_d = 1 /\ length b.mpfr_d = 1 /\ length c.mpfr_d = 1 /\
    modifies_1 a.mpfr_d h0 h1 /\ normal_cond_ h1 a /\
    I64.v a.mpfr_prec = I64.v b.mpfr_prec /\
    I64.v a.mpfr_prec = I64.v c.mpfr_prec /\
    mpfr_reg_cond_ h0 b /\ mpfr_reg_cond_ h0 c /\
    (let r = add1sp_exact (as_reg_fp_ h0 b) (as_reg_fp_ h0 c) in
    as_val h1 a.mpfr_d * pow2 (r.len - 64) = (high_mant r p).limb /\
    I64.v s.sh = I64.v gmp_NUMB_BITS - p /\
    I64.v s.bx = (high_mant r p).exp /\
    (rb_def r p = (v s.rb <> 0)) /\
    (sb_def r p = (v s.sb <> 0)))

(* The following inlined functions have abundant inputs,
 * which are used for simplify the specifications *)
inline_for_extraction val mpfr_add1sp1_gt_branch1:
    a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
    ap:buffer mp_limb_t -> bp:buffer mp_limb_t -> cp:buffer mp_limb_t ->
    bx:mpfr_reg_exp_t ->
    sh:mpfr_reg_prec_t -> d:i64 -> mask:mp_limb_t -> Stack state
    (requires (fun h -> 
        ap == a.mpfr_d /\ bp == b.mpfr_d /\ cp == c.mpfr_d /\
	bx = b.mpfr_exp /\
	mpfr_add1sp1_gt_branch1_pre_cond a b c sh d mask h))
    (ensures  (fun h0 s h1 -> mpfr_add1sp1_any_post_cond a b c h0 s h1))

let mpfr_add1sp1_gt_branch1 a b c ap bp cp bx sh d mask =
    let h = ST.get() in
    let a0 = bp.(0ul) +%^ (cp.(0ul) >>^ (int64_to_uint32 d)) in
    let a0, bx = if a0 <^ bp.(0ul) then mpfr_LIMB_HIGHBIT |^ (a0 >>^ 1ul), I64.(bx +^ 1L)
	         else a0, bx in
    let rb = a0 &^ (mpfr_LIMB_ONE <<^ (int64_to_uint32 I64.(sh -^ 1L))) in
    let sb = (a0 &^ mask) ^^ rb in
    ap.(0ul) <- a0 &^ (lognot mask);
    mpfr_add1sp1_gt_branch12_value_lemma h a b c sh d mask;
    mpfr_add1sp1_gt_branch12_rb_lemma h a b c sh d mask;
    mpfr_add1sp1_gt_branch1_sb_lemma h a b c sh d mask;
    mk_state sh bx rb sb

inline_for_extraction val mpfr_add1sp1_gt_branch2:
    a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
    ap:buffer mp_limb_t -> bp:buffer mp_limb_t -> cp:buffer mp_limb_t ->
    bx:mpfr_reg_exp_t ->
    sh:mpfr_reg_prec_t -> d:i64 -> mask:mp_limb_t -> Stack state
    (requires (fun h -> 
        ap == a.mpfr_d /\ bp == b.mpfr_d /\ cp == c.mpfr_d /\
	bx = b.mpfr_exp /\
	mpfr_add1sp1_gt_branch2_pre_cond a b c sh d mask h))
    (ensures  (fun h0 s h1 -> mpfr_add1sp1_any_post_cond a b c h0 s h1))

let mpfr_add1sp1_gt_branch2 a b c ap bp cp bx sh d mask =
    let h = ST.get() in
    let sb = cp.(0ul) <<^ (int64_to_uint32 I64.(gmp_NUMB_BITS -^ d)) in
    let a0 = bp.(0ul) +%^ (cp.(0ul) >>^ (int64_to_uint32 d)) in
    let sb, a0, bx =
        if a0 <^ bp.(0ul) then
	    sb |^ (a0 &^ 1uL), mpfr_LIMB_HIGHBIT |^ (a0 >>^ 1ul), I64.(bx +^ 1L)
	else sb, a0, bx in
    let rb = a0 &^ (mpfr_LIMB_ONE <<^ (int64_to_uint32 I64.(sh -^ 1L))) in
    let sb = sb |^ ((a0 &^ mask) ^^ rb) in
    ap.(0ul) <- a0 &^ (lognot mask);
    mpfr_add1sp1_gt_branch12_value_lemma h a b c sh d mask;
    mpfr_add1sp1_gt_branch12_rb_lemma h a b c sh d mask;
    mpfr_add1sp1_gt_branch2_sb_lemma h a b c sh d mask;
    mk_state sh bx rb sb
    
inline_for_extraction val mpfr_add1sp1_gt_branch3:
    a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
    ap:buffer mp_limb_t -> bp:buffer mp_limb_t ->
    bx:mpfr_reg_exp_t ->
    sh:mpfr_reg_prec_t -> Stack state
    (requires (fun h -> 
        ap == a.mpfr_d /\ bp == b.mpfr_d /\
	bx = b.mpfr_exp /\
        mpfr_add1sp1_gt_branch3_pre_cond a b c sh h))
    (ensures  (fun h0 s h1 -> mpfr_add1sp1_any_post_cond a b c h0 s h1))

let mpfr_add1sp1_gt_branch3 a b c ap bp bx sh =
    let h = ST.get() in
    ap.(0ul) <- bp.(0ul);
    let rb = 0uL in
    let sb = 1uL in
    mpfr_add1sp1_gt_branch3_value_lemma h a b c sh;
    mpfr_add1sp1_gt_branch3_rb_lemma h a b c sh;
    mpfr_add1sp1_gt_branch3_sb_lemma h a b c sh;
    mk_state sh bx rb sb

inline_for_extraction val mpfr_add1sp1_gt:
    a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
    ap:buffer mp_limb_t -> bp:buffer mp_limb_t -> cp:buffer mp_limb_t ->
    bx:mpfr_reg_exp_t -> cx:mpfr_reg_exp_t ->
    p:mpfr_reg_prec_t -> sh:mpfr_reg_prec_t -> Stack state
    (requires (fun h -> 
        ap == a.mpfr_d /\ bp == b.mpfr_d /\ cp == c.mpfr_d /\
	bx = b.mpfr_exp /\ cx = c.mpfr_exp /\
	mpfr_add1sp1_gt_pre_cond a b c sh h))
    (ensures  (fun h0 s h1 -> 
        mpfr_add1sp1_any_post_cond a b c h0 s h1 /\
        mpfr_add1sp1_any_post_cond a c b h0 s h1))

let mpfr_add1sp1_gt a b c ap bp cp bx cx p sh =
    let d = I64.(bx -^ cx) in
    let mask = mpfr_LIMB_MASK (int64_to_uint32 sh) in
    if I64.(d <^ sh) then mpfr_add1sp1_gt_branch1 a b c ap bp cp bx sh d mask
    else if I64.(d <^ gmp_NUMB_BITS) then mpfr_add1sp1_gt_branch2 a b c ap bp cp bx sh d mask
    else mpfr_add1sp1_gt_branch3 a b c ap bp bx sh

inline_for_extraction val mpfr_add1sp1_eq:
    a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
    ap:buffer mp_limb_t -> bp:buffer mp_limb_t -> cp:buffer mp_limb_t ->
    bx:mpfr_reg_exp_t ->
    p:mpfr_reg_prec_t -> sh:mpfr_reg_prec_t -> Stack state
    (requires (fun h -> 
        ap == a.mpfr_d /\ bp == b.mpfr_d /\ cp == c.mpfr_d /\
	bx = b.mpfr_exp /\
	mpfr_add1sp1_eq_pre_cond a b c sh h))
    (ensures  (fun h0 s h1 -> mpfr_add1sp1_any_post_cond a b c h0 s h1))

let mpfr_add1sp1_eq a b c ap bp cp bx p sh =
    let h = ST.get() in
    let a0 = (bp.(0ul) >>^ 1ul) +^ (cp.(0ul) >>^ 1ul) in
    let bx = I64.(bx +^ 1L) in
    let rb = a0 &^ (mpfr_LIMB_ONE <<^ (int64_to_uint32 I64.(sh -^ 1L))) in
    ap.(0ul) <- a0 ^^ rb;
    let sb = 0uL in
    mpfr_add1sp1_eq_value_lemma h a b c sh;
    mpfr_add1sp1_eq_rb_sb_lemma h a b c sh;
    mk_state sh bx rb sb

inline_for_extraction val mpfr_add1sp1_any:
    a:mpfr_ptr -> b:mpfr_ptr -> c:mpfr_ptr -> ap:buffer mp_limb_t ->
    p:mpfr_reg_prec_t -> Stack state
    (requires (fun h ->
        mpfr_live h a /\ mpfr_live h b /\ mpfr_live h c /\ ap == (as_struct h a).mpfr_d /\
        mpfr_add1sp1_any_pre_cond (as_struct h a) (as_struct h b) (as_struct h c) p h))
    (ensures  (fun h0 s h1 ->
        mpfr_add1sp1_any_post_cond (as_struct h0 a) (as_struct h0 b) (as_struct h0 c) h0 s h1))

let mpfr_add1sp1_any a b c ap p =
    let bx = mpfr_GET_EXP b in
    let cx = mpfr_GET_EXP c in
    let bp = mpfr_MANT b in
    let cp = mpfr_MANT c in
    let sh = I64.(gmp_NUMB_BITS -^ p) in
    let h0 = ST.get() in
    if I64.(bx =^ cx) then mpfr_add1sp1_eq a.(0ul) b.(0ul) c.(0ul) ap bp cp bx p sh
    else if I64.(bx >^ cx) then mpfr_add1sp1_gt a.(0ul) b.(0ul) c.(0ul) ap bp cp bx cx p sh
    else mpfr_add1sp1_gt a.(0ul) c.(0ul) b.(0ul) ap cp bp cx bx p sh

(* rounding specifications *)
inline_for_extraction val mpfr_add_one_ulp:
    a:mpfr_ptr -> ap:buffer mp_limb_t -> rnd_mode:mpfr_rnd_t ->
    sh:mpfr_reg_prec_t -> bx:mpfr_exp_t -> Stack i32
    (requires (fun h -> 
    mpfr_live h a /\ length (as_struct h a).mpfr_d = 1 /\ ap == (as_struct h a).mpfr_d /\
    normal_cond h a /\ mpfr_PREC_COND (I64.v (as_struct h a).mpfr_prec) /\
    sh = I64.(gmp_NUMB_BITS -^ (as_struct h a).mpfr_prec) /\
    bx = (as_struct h a).mpfr_exp /\ mpfr_EXP_COND (I64.v bx)))
    (ensures  (fun h0 t h1 -> 
    mpfr_live h1 a /\ mpfr_modifies a h0 h1 /\ mpfr_valid_cond h1 a /\
    mpfr_round2_cond (add_one_ulp (as_normal h0 a)) rnd_mode (as_fp h1 a) /\
    I32.v t = mpfr_add1sp1_add_one_ulp_ternary_spec (as_normal h0 a) rnd_mode))

inline_for_extraction val mpfr_add_one_ulp_carry:
    a:mpfr_ptr -> ap:buffer mp_limb_t -> rnd_mode:mpfr_rnd_t ->
    sh:mpfr_reg_prec_t -> bx:mpfr_exp_t -> Stack i32
    (requires (fun h -> 
    mpfr_live h a /\ length (as_struct h a).mpfr_d = 1 /\ ap == (as_struct h a).mpfr_d /\
    normal_cond h a /\ mpfr_PREC_COND (I64.v (as_struct h a).mpfr_prec) /\
    sh = I64.(gmp_NUMB_BITS -^ (as_struct h a).mpfr_prec) /\
    bx = (as_struct h a).mpfr_exp /\ mpfr_EXP_COND (I64.v bx) /\
    (get h ap 0) +%^ (mpfr_LIMB_ONE <<^ (int64_to_uint32 sh)) =^ 0uL))
    (ensures  (fun h0 t h1 -> 
    mpfr_live h1 a /\ mpfr_modifies a h0 h1 /\ mpfr_valid_cond h1 a /\
    mpfr_round2_cond (add_one_ulp (as_normal h0 a)) rnd_mode (as_fp h1 a) /\
    I32.v t = mpfr_add1sp1_add_one_ulp_ternary_spec (as_normal h0 a) rnd_mode))

let mpfr_add_one_ulp_carry a ap rnd_mode sh bx=
    let h0 = ST.get() in
    ap.(0ul) <- ap.(0ul) +%^ (mpfr_LIMB_ONE <<^ (int64_to_uint32 sh));
    ap.(0ul) <- mpfr_LIMB_HIGHBIT;
    let h1 = ST.get() in
    lemma_reveal_modifies_1 ap h0 h1;
    lemma_intro_modifies_2 a ap h0 h1;
    if I64.(bx +^ 1L <=^ mpfr_EMAX) then begin
       mpfr_SET_EXP a I64.(bx +^ 1L);
	 let h2 = ST.get() in
	 lemma_pow2_mod 63 (I64.v sh);
	 eval_abs_lt_intro_lemma (as_normal h0 a) (mpfr_max_value (as_normal h0 a).sign (as_normal h0 a).prec);
	 eval_eq_intro_lemma (add_one_ulp (as_normal h0 a)) (as_normal h2 a);
	 assert(mpfr_round2_cond (add_one_ulp (as_normal h0 a)) rnd_mode (as_fp h2 a));//
	 mpfr_modifies_trans_lemma a h0 h1 h2;
	 mpfr_RET (mpfr_SIGN a)
    end else begin 
	assert(eval_abs (as_normal h0 a) == mpfr_overflow_bound (I64.v (as_struct h0 a).mpfr_prec));
	let t = mpfr_overflow a rnd_mode (mpfr_SIGN a) in
	let h2 = ST.get() in
	mpfr_overflow_post_cond_lemma (add_one_ulp (as_normal h0 a)) (add_one_ulp (as_normal h0 a)).prec rnd_mode (I32.v t) (as_fp h2 a);
	mpfr_modifies_trans_lemma a h0 h1 h2;
	mpfr_RET t
    end

let mpfr_add_one_ulp a ap rnd_mode sh bx =
    let h0 = ST.get() in
    if ap.(0ul) +%^ (mpfr_LIMB_ONE <<^ (int64_to_uint32 sh)) =^ 0uL then
        mpfr_add_one_ulp_carry a ap rnd_mode sh bx
    else begin 
        ap.(0ul) <- ap.(0ul) +%^ (mpfr_LIMB_ONE <<^ (int64_to_uint32 sh));
        let h1 = ST.get() in
	lemma_pow2_multiple_le (v (get h0 ap 0)) 64 (I64.v sh);
	assert(v (get h0 ap 0) + pow2 (I64.v sh) = v (get h1 ap 0));
	lemma_pow2_mod (I64.v sh) (I64.v sh);
	lemma_mod_distr_zero (v (get h0 ap 0)) (pow2 (I64.v sh)) (pow2 (I64.v sh));
        exp_impl_no_overflow_lemma (as_normal h1 a);
	lemma_reveal_modifies_1 ap h0 h1;
	lemma_intro_modifies_2 a ap h0 h1;
        mpfr_RET (mpfr_SIGN a)
    end

inline_for_extraction val mpfr_add1sp1_round:
    a:mpfr_ptr -> ap:buffer mp_limb_t -> rnd_mode:mpfr_rnd_t -> st:state -> Stack i32
    (requires (fun h -> mpfr_live h a /\ length (as_struct h a).mpfr_d = 1 /\ normal_cond h a /\
        ap == (as_struct h a).mpfr_d /\
        (let high = {as_normal h a with exp = I64.v st.bx} in
        let p = high.prec in
        as_val h (as_struct h a).mpfr_d * pow2 high.len = high.limb * pow2 64 /\
        I64.v st.sh = I64.v gmp_NUMB_BITS - p /\
        mpfr_EXP_COND (I64.v st.bx))))
    (ensures  (fun h0 t h1 -> 
        mpfr_live h1 a /\ mpfr_modifies a h0 h1 /\ mpfr_valid_cond h1 a /\
        (let high = {as_normal h0 a with exp = I64.v st.bx} in
        mpfr_round2_cond (mpfr_add1sp1_round_spec high (st.rb <> 0uL) (st.sb <> 0uL) rnd_mode)
                          rnd_mode (as_fp h1 a) /\
        I32.v t = mpfr_add1sp1_ternary_spec high (st.rb <> 0uL) (st.sb <> 0uL) rnd_mode)))

let mpfr_add1sp1_round a ap rnd_mode st =
    let a0 = ap.(0ul) in
    let h0 = ST.get() in
    mpfr_SET_EXP a st.bx; // Maybe set it later in truncate and add_one_ulp?
    let h1 = ST.get() in
    mpfr_add1sp1_is_even_lemma a0 st.sh (as_normal_ h0 ({as_struct h0 a with mpfr_exp = st.bx}));
    mpfr_round2_cond_refl_lemma (as_normal h1 a) rnd_mode;
    if (st.rb =^ 0uL && st.sb =^ 0uL) then mpfr_RET 0l
    else if (MPFR_RNDN? rnd_mode) then
        if (st.rb =^ 0uL || (st.sb =^ 0uL && 
	                   ((a0 &^ (mpfr_LIMB_ONE <<^ (int64_to_uint32 st.sh))) =^ 0uL))) then
	    mpfr_RET (mpfr_NEG_SIGN (mpfr_SIGN a))
	else mpfr_add_one_ulp a ap rnd_mode st.sh st.bx
    else if mpfr_IS_LIKE_RNDZ rnd_mode (mpfr_IS_NEG a) then
        mpfr_RET (mpfr_NEG_SIGN (mpfr_SIGN a))
    else mpfr_add_one_ulp a ap rnd_mode st.sh st.bx

(* specifications for mpfr_add1sp1 *)
val mpfr_add1sp1: a:mpfr_ptr -> b:mpfr_ptr -> c:mpfr_ptr ->
                  rnd_mode:mpfr_rnd_t -> p:mpfr_prec_t -> Stack i32
    (requires (fun h -> 
        (* Memory safety *)
        mpfr_live h a /\ mpfr_live h b /\ mpfr_live h c /\
        mpfr_disjoint_or_equal h a b /\ mpfr_disjoint_or_equal h a c /\
        mpfr_disjoint_or_equal h b c /\
        length (as_struct h a).mpfr_d = 1 /\
        length (as_struct h b).mpfr_d = 1 /\ length (as_struct h c).mpfr_d = 1 /\
        (* Functional correctness *)
        I64.v p > 0 /\ I64.v p < 64 /\ p = (as_struct h a).mpfr_prec /\
        p = (as_struct h b).mpfr_prec /\ p = (as_struct h c).mpfr_prec /\
        (as_struct h a).mpfr_sign = (as_struct h b).mpfr_sign /\
        mpfr_valid_cond h a /\ mpfr_reg_cond h b /\ mpfr_reg_cond h c))
    (ensures  (fun h0 t h1 -> 
        let exact = add1sp_exact (as_fp h0 b) (as_fp h0 c) in
        (* Memory safety *)
        mpfr_live h1 a /\ mpfr_live h1 b /\ mpfr_live h1 c /\
        mpfr_disjoint_or_equal h1 a b /\ mpfr_disjoint_or_equal h1 a c /\
        mpfr_disjoint_or_equal h1 b c /\ mpfr_modifies a h0 h1 /\
        (* Functional correctness *)
        mpfr_valid_cond h1 a /\ 
        mpfr_round_cond exact (I64.v p) rnd_mode (as_fp h1 a) /\
        mpfr_ternary_cond (I32.v t) exact (as_fp h1 a)))

let mpfr_add1sp1 a b c rnd_mode p =
    let h0 = ST.get() in
    let ap = mpfr_MANT a in
    let st = mpfr_add1sp1_any a b c ap p in
    let h1 = ST.get() in
    lemma_reveal_modifies_1 (mpfr_MANT a) h0 h1;
    lemma_intro_modifies_2 a (mpfr_MANT a) h0 h1;
    if I64.(st.bx >^ mpfr_EMAX) then begin
        let s = mpfr_SIGN a in
        let t = mpfr_overflow a rnd_mode (mpfr_SIGN a) in
	let h2 = ST.get() in
	mpfr_overflow_post_cond_lemma (add1sp_exact (as_reg_fp h0 b) (as_reg_fp h0 c)) (I64.v (as_struct h0 a).mpfr_prec) rnd_mode (I32.v t) (as_fp h2 a);
//	mpfr_modifies_trans_lemma a h0 h1 h2;
	t
    end else begin
        let t = mpfr_add1sp1_round a ap rnd_mode st in
	let h2 = ST.get() in
	mpfr_add1sp1_round_post_cond_lemma (add1sp_exact (as_reg_fp h0 b) (as_reg_fp h0 c)) (I64.v (as_struct h0 a).mpfr_prec) (as_normal_ h1 ({as_struct h1 a with mpfr_exp = st.bx})) (st.rb <> 0uL) (st.sb <> 0uL) rnd_mode (I32.v t) (as_fp h2 a);
//	mpfr_modifies_trans_lemma a h0 h1 h2;
	t
    end
