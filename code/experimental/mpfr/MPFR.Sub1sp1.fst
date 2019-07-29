module MPFR.Sub1sp1

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Buffer
open FStar.UInt64
open FStar.UInt
open FStar.Int.Cast
open FStar.Mul
open MPFR.Dyadic
open MPFR.Spec.Lib
open MPFR.Spec.Sub1
open MPFR.Spec.Round
open MPFR.Maths

open MPFR.Lib
open MPFR.Exceptions

open MPFR.Exceptions.Lemma
open MPFR.Sub1sp1.Lemma
open MPFR.Add1sp1
open MPFR.Add1sp1.Lemma

module ST = FStar.HyperStack.ST
module I32 = FStar.Int32
module I64 = FStar.Int64
module U32 = FStar.UInt32

#set-options "--z3refresh --z3rlimit 100 --max_fuel 1 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 0"

let mpfr_sub1sp1_post_cond h0 t h1 (a:mpfr_ptr) b c (p:mpfr_reg_prec_t) rnd_mode exact: GTot Type0=
        (* Memory safety *)
        mpfr_live h1 a /\ mpfr_live h1 b /\ mpfr_live h1 c /\
        mpfr_disjoint_or_equal h1 a b /\ mpfr_disjoint_or_equal h1 a c /\
        mpfr_disjoint_or_equal h1 b c /\ mpfr_modifies a h0 h1 /\
        (* Functional correctness *)
        mpfr_valid_cond h1 a /\
        mpfr_round_cond exact (I64.v p) rnd_mode (as_fp h1 a) /\
        mpfr_ternary_cond (I32.v t) exact (as_fp h1 a)

inline_for_extraction 
val count_leading_zeros: a:u64{not (a=^0uL)}->Tot (cnt:u32{U32.v cnt<32 /\ v (a<<^cnt)>=pow2 63 /\ v a*pow2 (U32.v cnt)<pow2 64 /\ U32.v cnt=64-(nbits (v a))})

let count_leading_zeros a = MPFR.Lib.Clz.count_leading_zeros a

inline_for_extraction val mpfr_sub1sp1_eq_branch_1:
    a:mpfr_ptr -> b:mpfr_ptr -> c:mpfr_ptr ->
    ap:buffer mp_limb_t -> bp:buffer mp_limb_t -> cp:buffer mp_limb_t ->
    bx:mpfr_reg_exp_t ->cx:mpfr_reg_exp_t
    ->rnd_mode:mpfr_rnd_t->
    p:mpfr_reg_prec_t -> sh:mpfr_reg_prec_t -> Stack i32
    (requires (fun h->mpfr_sub1sp1_pre_cond h a b c p /\
    mpfr_sub1sp1_pre_cond_2 h a b c bx cx ap bp cp p sh /\
    I64.(bx=^cx) /\ as_val h bp=as_val h cp 
    ))
 (ensures (fun h0 t h1 -> 
   let exact=sub1sp_exact (as_fp h0 b) (as_fp h0 c) in 
   mpfr_sub1sp1_post_cond h0 t h1 a b c p rnd_mode exact))

let mpfr_sub1sp1_eq_branch_1 a b c ap bp cp bx cx rnd_mode p sh=
    if rnd_mode=MPFR_RNDD then mpfr_SET_NEG a else mpfr_SET_POS a;
    mpfr_SET_ZERO a;
    mpfr_RET 0l

let mpfr_sub1sp1_any_post_cond h0 s h1 (a:mpfr_ptr) b c (p:mpfr_reg_prec_t) exact: GTot Type0=
        (* Memory safety *)
        mpfr_live h1 a /\ mpfr_live h1 b /\ mpfr_live h1 c /\
        length (as_struct h1 a).mpfr_d = 1 /\
        length (as_struct h1 b).mpfr_d = 1 /\ length (as_struct h1 c).mpfr_d = 1 /\
        normal_cond h1 a /\ 
        (as_normal h1 a).prec=I64.v p /\  (as_struct h0 a).mpfr_d==(as_struct h1 a).mpfr_d /\
        (*Functional correctness*)
        I64.(v ((as_struct h0 a).mpfr_prec)=v p) /\
        I64.(v ((as_struct h0 b).mpfr_prec)=v p) /\
        I64.(v ((as_struct h0 c).mpfr_prec)=v p) /\
        mpfr_reg_cond h0 b /\ mpfr_reg_cond h0 c /\
        (let r = sub1sp_exact (as_reg_fp h0 b) (as_reg_fp h0 c) in
        normal_fp_cond r /\
        I64.(s.bx<=^mpfr_EMAX) /\
        as_val h1 (as_struct h1 a).mpfr_d * pow2 (high_mant r (I64.v p)).len = (high_mant r (I64.v p)).limb * (pow2 64) /\
        I64.v s.sh = I64.v gmp_NUMB_BITS - I64.v p /\
        I64.v s.bx = (high_mant r (I64.v p)).exp /\
        (rb_def r (I64.v p) = (v s.rb <> 0)) /\
        (sb_def r (I64.v p) = (v s.sb <> 0)))

inline_for_extraction val mpfr_sub1sp1_eq:
    a:mpfr_ptr -> b:mpfr_ptr -> c:mpfr_ptr ->
    ap:buffer mp_limb_t -> bp:buffer mp_limb_t -> cp:buffer mp_limb_t ->
    bx:mpfr_reg_exp_t -> cx:mpfr_reg_exp_t ->
    p:mpfr_reg_prec_t -> sh:mpfr_reg_prec_t -> Stack state
    (requires (fun h-> mpfr_sub1sp1_pre_cond h a b c p /\
    mpfr_sub1sp1_pre_cond_2 h a b c bx cx ap bp cp p sh /\
    I64.(bx=^cx) /\
    I64.(as_val h bp<>as_val h cp)
    ))
    (ensures (fun h0 s h1->
    let exact=sub1sp_exact (as_fp h0 b) (as_fp h0 c) in
    mpfr_sub1sp1_any_post_cond h0 s h1 a b c p exact /\
    modifies_2 a (as_struct h1 a).mpfr_d h0 h1 /\
    mpfr_modifies a h0 h1 /\
    (as_normal h1 a).sign=exact.sign))

let mpfr_sub1sp1_eq a b c ap bp cp bx cx p sh =
    let h0=ST.get() in
    let vb= v bp.(0ul) in
    let vc= v cp.(0ul) in
    let vsh= I64.(v sh) in 
    if(cp.(0ul)>^bp.(0ul)) then begin 
      let a0=cp.(0ul) -^ bp.(0ul) in
      let cnt=count_leading_zeros a0 in
      mpfr_SET_SIGN a (mpfr_NEG_SIGN (mpfr_SIGN b));(*mpfr_SET_OPPOSITE_SIGN does exactly this, but makes it harder to check*)
      ap.(0ul) <- a0<<^cnt;
      lemma_mod_distr_sub_zero vc vb (pow2 vsh);
      lemma_shift_left_mod_pow2 a0 cnt vsh;
      let bx=I64.(bx -^ (uint32_to_int64 cnt)) in
      let h1=ST.get() in
      shift_left_value_lemma (v a0) (U32.v cnt);
      lemma_small_mod (v a0*pow2 (U32.v cnt)) (pow2 64);
      mpfr_sub1sp1_eq_value_lemma ({(as_normal h1 a) with exp=I64.v bx}) (as_reg_fp h0 b) (as_reg_fp h0 c) (U32.v cnt) (I64.v p);
      mpfr_sub1sp1_eq_rb_sb_lemma (as_reg_fp h0 b) (as_reg_fp h0 c) (I64.v p);
      mk_state sh bx 0uL 0uL
    end else begin
      let a0=bp.(0ul) -^ cp.(0ul) in
      let cnt=count_leading_zeros a0 in
      mpfr_SET_SAME_SIGN a b;
      ap.(0ul) <- a0<<^cnt;
      lemma_mod_distr_sub_zero vb vc (pow2 vsh);
      lemma_shift_left_mod_pow2 a0 cnt vsh;
      let bx=I64.(bx -^ (uint32_to_int64 cnt)) in
      let h1=ST.get() in
      shift_left_value_lemma (v a0) (U32.v cnt);
      lemma_small_mod (v a0*pow2 (U32.v cnt)) (pow2 64);
      mpfr_sub1sp1_eq_value_lemma ({(as_normal h1 a) with exp=I64.v bx}) (as_reg_fp h0 b) (as_reg_fp h0 c) (U32.v cnt) (I64.v p);
      mpfr_sub1sp1_eq_rb_sb_lemma (as_reg_fp h0 b) (as_reg_fp h0 c) (I64.v p);
      mk_state sh bx 0uL 0uL
    end

val mpfr_sub1sp1_gt_branch_1:  a:mpfr_ptr -> b:mpfr_ptr -> c:mpfr_ptr ->
    ap:buffer mp_limb_t -> bp:buffer mp_limb_t -> cp:buffer mp_limb_t ->
    bx:mpfr_reg_exp_t ->cx:mpfr_reg_exp_t ->
    p:mpfr_reg_prec_t -> sh:mpfr_reg_prec_t ->
    mask:u64 -> sb_1:u64 -> a0_base:u64 -> Stack state
    (requires (fun h->
    v a0_base<>0 /\
    v mask=pow2 (I64.v sh)-1 /\
    I64.(v (bx -^ cx))<64 /\
    mpfr_sub1sp1_pre_cond h a b c p /\
    mpfr_sub1sp1_pre_cond_2 h a b c bx cx ap bp cp p sh /\
    I64.(bx>^cx) /\
    v sb_1=add_mod #64 (pow2 64-1-(shift_left #64 (as_val h cp) (64-I64.(v (bx -^ cx))))) 1 /\
    v a0_base=((as_val h bp)-(if (v sb_1)=0 then 0 else 1))-(shift_right #64 (as_val h cp) I64.(v (bx -^ cx))) ))
    (ensures (fun h0 s h1->
    let exact=sub1sp_exact (as_fp h0 b) (as_fp h0 c) in
    mpfr_sub1sp1_any_post_cond h0 s h1 a b c p exact /\
    modifies_1 (as_struct h1 a).mpfr_d h0 h1))

#set-options "--z3rlimit 400"

let mpfr_sub1sp1_gt_branch_1 a b c ap bp cp bx cx p sh mask sb_1 a0_base=
    let h0=ST.get() in
    lemma_gt_exp_sub1sp (as_reg_fp h0 b) (as_reg_fp h0 c);
    let cnt=count_leading_zeros a0_base in
    let a0=if U32.(cnt =^ 0ul) then a0_base else
    (a0_base <<^ cnt) |^ (sb_1 >>^ U32.(64ul -^ cnt)) in
    let sb_2=sb_1 <<^ cnt in
    let rb=a0 &^ (mpfr_LIMB_ONE <<^ (int64_to_uint32 I64.(sh-^1L))) in
    let sb=sb_2 |^ ((a0 &^ mask) ^^ rb) in
    ap.(0ul) <- a0 &^ (UInt64.lognot mask);

    lemma_nth_top_bit (v (a0_base <<^ cnt));
    lemma_lognot_value mask;
    lemma_pow2_le (I64.v sh) 63;
    lemma_nth_top_bit (v (UInt64.lognot mask));
    lemma_nth_top_bit (v (a0 &^ (UInt64.lognot mask)));
    lemma_lognot_mask_mod a0 mask (I64.v sh);

    (let r=sub1sp_exact (as_reg_fp h0 b) (as_reg_fp h0 c) in
    let d=I64.(v (bx-^cx)) in
    let a0sb=(v a0)*pow2 64+(v sb_2) in
    lemma_sub1sp1_gt_branch_1_a0_bx (as_reg_fp h0 b) (as_reg_fp h0 c) (I64.v p) (v sb_1) (v a0_base);
    lemma_shift_left_dp (v a0_base) (v sb_1) U32.(v cnt);
    assert((v a0)*pow2 64+(v sb_2)=((v a0_base)*pow2 64+(v sb_1))*pow2 U32.(v cnt));
    assert((v a0_base)*pow2 64+(v sb_1)=r.limb*pow2(64-d));
    lemma_paren_mul_right r.limb (pow2 (64-d)) (pow2 U32.(v cnt));
    lemma_pow2_mul (64-d) U32.(v cnt);
    assert(a0sb=r.limb*pow2 (128-r.len));
    lemma_sub1sp1_gt_branch_1_rb_sb_value r (v a0) (v sb_2) (v mask) (I64.v p)
    );
    mk_state sh I64.(bx-^(uint32_to_int64 cnt)) rb sb

inline_for_extraction val mpfr_sub1sp1_gt:
    a:mpfr_ptr -> b:mpfr_ptr -> c:mpfr_ptr ->
    ap:buffer mp_limb_t -> bp:buffer mp_limb_t -> cp:buffer mp_limb_t ->
    bx:mpfr_reg_exp_t ->cx:mpfr_reg_exp_t ->
    p:mpfr_reg_prec_t -> sh:mpfr_reg_prec_t -> Stack state
    (requires (fun h->
    mpfr_sub1sp1_pre_cond h a b c p /\
    mpfr_sub1sp1_pre_cond_2 h a b c bx cx ap bp cp p sh /\
    I64.(bx>^cx)))
    (ensures (fun h0 s h1->
    let exact=sub1sp_exact (as_fp h0 b) (as_fp h0 c) in
    mpfr_sub1sp1_any_post_cond h0 s h1 a b c p exact /\
    modifies_1 (as_struct h1 a).mpfr_d h0 h1))

let mpfr_sub1sp1_gt a b c ap bp cp bx cx p sh =
    let h0=ST.get() in
    let d=I64.(bx-^cx) in
    let bp0ul=bp.(0ul) in
    let cp0ul=cp.(0ul) in
    let mask=mpfr_LIMB_MASK (int64_to_uint32 sh) in
    lemma_gt_exp_sub1sp (as_reg_fp h0 b) (as_reg_fp h0 c);
    if(I64.(d<^64L)) then begin
      let sb_1=UInt64.minus (cp0ul<<^(int64_to_uint32 I64.(gmp_NUMB_BITS -^ d))) in
      lemma_lognot_value (cp0ul<<^(int64_to_uint32 I64.(gmp_NUMB_BITS -^ d)));
      assert(v sb_1=add_mod #64 (pow2 64-1-(shift_left #64 (v cp0ul) (64-I64.v d))) 1);
      assert(v cp0ul%(pow2 (I64.v sh))=0);
      lemma_pow2_mod_mod_zero (v cp0ul) (I64.v sh) 1;
      lemma_sub1sp1_gt_1_valid bp0ul cp0ul d;
      mpfr_sub1sp1_gt_branch_1 a b c ap bp cp bx cx p sh mask sb_1 (bp0ul -^ (if sb_1=^0uL then 0uL else 1uL) -^ (cp0ul >>^ (int64_to_uint32 d)))
    end else begin 
      if(bp0ul>^mpfr_LIMB_HIGHBIT) then begin
        assert((v bp0ul)%(pow2 (I64.v sh))=0);
        lemma_mod_ge_zero (v bp0ul) (pow2 (I64.v sh));
        lemma_pow2_mod 63 (I64.v sh);
        lemma_mod_distr_sub_zero (v bp0ul) (v mpfr_LIMB_HIGHBIT) (pow2 (I64.v sh));
        lemma_mod_ge_zero (v bp0ul-v mpfr_LIMB_HIGHBIT) (pow2 (I64.v sh));
        assert(bp0ul -^ mpfr_LIMB_HIGHBIT >=^ (mpfr_LIMB_ONE <<^ (int64_to_uint32 sh)));
        assert((bp0ul -^ (mpfr_LIMB_ONE <<^ (int64_to_uint32 sh)))>=^mpfr_LIMB_HIGHBIT);
        ap.(0ul) <- bp0ul -^ (mpfr_LIMB_ONE <<^ (int64_to_uint32 sh));
        let h1=ST.get() in
        shift_left_value_lemma (v mpfr_LIMB_ONE) (I64.v sh);
        lemma_pow2_mul_mod (v mpfr_LIMB_ONE) (I64.v sh) 64;
        lemma_multiple_mod (v mpfr_LIMB_ONE%pow2 (64-(I64.v sh))) (pow2 (I64.v sh));
        lemma_mod_distr_sub_zero (v bp0ul) (v (mpfr_LIMB_ONE <<^ (int64_to_uint32 sh))) (pow2 (I64.v sh));
        lemma_sub1sp1_gt_rb_sb_exp_2 (as_reg_fp h0 b) (as_reg_fp h0 c) (I64.v p);
        lemma_sub1sp1_gt_value_2 (as_reg_fp h0 b) (as_reg_fp h0 c) (I64.v p);
        mk_state sh bx 1uL 1uL
      end else begin
        let rb=(I64.(sh>^1L||d>^gmp_NUMB_BITS)||cp0ul=mpfr_LIMB_HIGHBIT) in
        let sb=(I64.(sh>^1L||d>^gmp_NUMB_BITS)||cp0ul<>mpfr_LIMB_HIGHBIT) in
        ap.(0ul) <- (UInt64.lognot mask);
        let h1=ST.get() in
        lemma_lognot_value mask;
        lemma_pow2_mod 64 (I64.v sh);
        lemma_mod_distr_sub_zero (pow2 64) (pow2 (I64.v sh)) (pow2 (I64.v sh));
        lemma_sub1sp1_gt_rb_sb_exp_3 (as_reg_fp h0 b) (as_reg_fp h0 c) (I64.v p);
        lemma_sub1sp1_gt_value_3 (as_reg_fp h0 b) (as_reg_fp h0 c) (I64.v p);
        assert(I64.(v (bx-^1L))=(sub1sp_exact (as_reg_fp h0 b) (as_reg_fp h0 c)).exp);
        mk_state sh I64.(bx-^1L) (if rb then 1uL else 0uL) (if sb then 1uL else 0uL)
      end
    end

#set-options "--z3rlimit 100"

(* specifications for mpfr_sub1sp1 *)
val mpfr_sub1sp1: a:mpfr_ptr -> b:mpfr_ptr -> c:mpfr_ptr ->
                  rnd_mode:mpfr_rnd_t -> p:mpfr_prec_t -> Stack i32
    (requires (fun h -> mpfr_sub1sp1_pre_cond h a b c p))
    (ensures  (fun h0 t h1 ->
    let exact=sub1sp_exact (as_fp h0 b) (as_fp h0 c) in
    mpfr_sub1sp1_post_cond h0 t h1 a b c p rnd_mode exact))

inline_for_extraction val mpfr_sub1sp1_any:
    a:mpfr_ptr -> b:mpfr_ptr -> c:mpfr_ptr ->
    ap:buffer mp_limb_t -> bp:buffer mp_limb_t -> cp:buffer mp_limb_t ->
    bx:mpfr_reg_exp_t -> cx:mpfr_reg_exp_t ->
    p:mpfr_reg_prec_t -> sh:mpfr_reg_prec_t -> Stack state
    (requires (fun h-> mpfr_sub1sp1_pre_cond h a b c p /\
    mpfr_sub1sp1_pre_cond_2 h a b c bx cx ap bp cp p sh /\
    (I64.(~(bx=^cx)) \/ I64.(as_val h bp<>as_val h cp))
    ))
    (ensures (fun h0 s h1->
    let exact=sub1sp_exact (as_fp h0 b) (as_fp h0 c) in
    mpfr_sub1sp1_any_post_cond h0 s h1 a b c p exact /\
    modifies_2 a (as_struct h1 a).mpfr_d h0 h1 /\
    mpfr_modifies a h0 h1 /\
    (as_normal h1 a).sign=exact.sign))

let mpfr_sub1sp1_any a b c ap bp cp bx cx p sh =
    let h0=ST.get() in
    if I64.(bx =^ cx) then begin
      mpfr_sub1sp1_eq a b c ap bp cp bx cx p sh
    end else begin 
    let b,c,bx,cx,bp,cp=(if I64.(bx >=^ cx)
    then (mpfr_SET_SAME_SIGN a b;lemma_gt_exp_sub1sp (as_fp h0 b) (as_fp h0 c);b,c,bx,cx,bp,cp)
    else (mpfr_SET_SIGN a (mpfr_NEG_SIGN (mpfr_SIGN b));lemma_gt_exp_sub1sp (as_fp h0 c) (as_fp h0 b);c,b,cx,bx,cp,bp)) in       
    mpfr_sub1sp1_gt a b c ap bp cp bx cx p sh
    end

val lemma_eval_small_exp: r:normal_fp -> emax:int -> Lemma
    (requires r.exp<emax)
    (ensures eval_abs r<.(mk_dyadic 1 (emax-1)))
    
let lemma_eval_small_exp r emax=
assert((mk_dyadic 1 r.exp) <=. (mk_dyadic 1 (emax-1)));
assert(eval_abs r<. (mk_dyadic 1 r.exp))

val lemma_dyadic_pow2: k:nat -> e:int -> Lemma
    ((mk_dyadic (pow2 k) e) =. mk_dyadic 1 (k+e))

let lemma_dyadic_pow2 k e=()

val lemma_underflow_low_prec: b:mpfr_reg_fp -> c:mpfr_reg_fp{b.prec=c.prec} -> r:normal_fp -> Lemma
    (requires (r==sub1sp_exact b c /\ r.exp<mpfr_EMIN_spec))
    (ensures (r.prec<b.prec))

let lemma_underflow_low_prec b c r=()

val lemma_eval_abs_zero: a:valid_fp{a.limb=0} -> r:valid_fp{r.limb<>0} -> Lemma
    (ensures (eval_abs a <. eval_abs r))

let lemma_eval_abs_zero a r=()

val lemma_sub1sp1_rndn_eval: r:normal_fp{mpfr_PREC_COND r.prec /\ r.prec<=128} -> Lemma
    (requires (r.exp<mpfr_EMIN_spec-1 \/ (r.exp=mpfr_EMIN_spec-1 /\ r.limb=pow2 (r.len-1)) ))
    (ensures  (eval_abs r <=. fdiv_pow2 (mpfr_underflow_bound r.prec) 1 /\
               eval_abs r <. mpfr_overflow_bound r.prec))

let lemma_sub1sp1_rndn_eval r=
    if r.exp=mpfr_EMIN_spec-1 then begin
        lemma_dyadic_pow2 (r.len-1) (r.exp-r.len);
        assert(eval_abs r <=. mk_dyadic 1 (mpfr_EMIN_spec-2))
    end
    else begin
        lemma_dyadic_pow2 r.len (r.exp-r.len);
        dyadic_le_exp_lemma r.exp (mpfr_EMIN_spec-2);
        assert(eval_abs r <=. mk_dyadic 1 (mpfr_EMIN_spec-2))
    end;
    let l = prec_to_len r.prec in
    lemma_dyadic_pow2 (l-1) (mpfr_EMIN_spec-l-1);
    lemma_pow2_lt (l-r.prec) l;
    dyadic_le_limb_lemma 1 (pow2 l-pow2 (l-r.prec)) (mpfr_EMAX_spec-l);
    assert(mk_dyadic 1 (mpfr_EMAX_spec-l) <=. mpfr_overflow_bound r.prec);
    assert(mpfr_EMIN_spec-2<mpfr_EMAX_spec-l);
    assert(fdiv_pow2 (mpfr_underflow_bound r.prec) 1 <=. mk_dyadic 1 (mpfr_EMIN_spec-2));
    dyadic_lt_exp_lemma (mpfr_EMIN_spec-2) (mpfr_EMAX_spec-l);
    assert(fdiv_pow2 (mpfr_underflow_bound r.prec) 1 <. mpfr_overflow_bound r.prec)

#set-options "--z3rlimit 400"

let mpfr_sub1sp1 a b c rnd_mode p =
    let bx=mpfr_GET_EXP b in
    let cx=mpfr_GET_EXP c in
    let ap=mpfr_MANT a in
    let bp=mpfr_MANT b in
    let cp=mpfr_MANT c in
    let sh=I64.(gmp_NUMB_BITS -^ p) in
    let bp0ul=bp.(0ul) in
    let cp0ul=cp.(0ul) in
    let h0=ST.get() in
    if I64.(bx =^ cx) && (bp0ul=cp0ul) then
       mpfr_sub1sp1_eq_branch_1 a b c ap bp cp bx cx rnd_mode p sh
    else begin
    let st=mpfr_sub1sp1_any a b c ap bp cp bx cx p sh in
    let h1 = ST.get() in
    if I64.(st.bx <^ mpfr_EMIN) then begin 
        let s = mpfr_SIGN a in
        let ap0ul=ap.(0ul) in
        if(rnd_mode=MPFR_RNDN&&(I64.(st.bx<^(mpfr_EMIN-^1L))||ap0ul=mpfr_LIMB_HIGHBIT)) then begin
            mpfr_SET_ZERO a;
            let h2=ST.get() in
            (let r=(sub1sp_exact (as_reg_fp h0 b) (as_reg_fp h0 c)) in
            let p=I64.v p in
            lemma_underflow_low_prec (as_reg_fp h0 b) (as_reg_fp h0 c) r;
            let hm=high_mant r p in
            assert(eval_abs r =. eval_abs hm);
            if hm.exp=mpfr_EMIN_spec-1 then begin
                lemma_pow2_mul 63 hm.len;
                lemma_pow2_mul (hm.len-1) 64;
                assert(hm.limb=pow2 (hm.len-1))
            end;
            assert(hm.prec<=128);
            lemma_sub1sp1_rndn_eval hm;
            assert(eval_abs r =. eval_abs (round_def r p MPFR_RNDN));
            let a=(as_fp h2 a) in
            lemma_eval_abs_zero a r;
            if r.sign>0 then
                eval_lt_intro_lemma a r
            else
                eval_lt_intro_lemma r a
            );
            mpfr_NEG_SIGN s
        end else begin 
            let h1b=ST.get() in
            let t=mpfr_underflow a rnd_mode s in
            let h2=ST.get() in
            (let r=(sub1sp_exact (as_reg_fp h0 b) (as_reg_fp h0 c)) in
            let p=(I64.v p) in
            lemma_underflow_low_prec (as_reg_fp h0 b) (as_reg_fp h0 c) r;
            if rnd_mode=MPFR_RNDN then begin
                let hm=high_mant r p in
                assert(eval_abs r =. eval_abs hm);
                lemma_mul_lt_right (pow2 hm.len) (pow2 63) (v ap0ul);
                lemma_pow2_mul 63 hm.len;
                lemma_pow2_mul (hm.len-1) 64;
                lemma_dyadic_pow2 (hm.len-1) (hm.exp-hm.len);
                assert (eval_abs hm >. mk_dyadic 1 (mpfr_EMIN_spec-2));
                lemma_dyadic_pow2 ((prec_to_len p)-1) (mpfr_EMIN_spec-(prec_to_len p)-1);
                assert(eval_abs hm >. fdiv_pow2 (mpfr_underflow_bound p) 1);
                assert(eval_abs r >. fdiv_pow2 (mpfr_underflow_bound p) 1)
            end;
            assert(eval_abs r =. eval_abs (round_def r p MPFR_RNDN));
            assert( (MPFR_RNDN? rnd_mode ==> eval_abs r >. fdiv_pow2 (mpfr_underflow_bound p) 1));
            lemma_eval_small_exp r mpfr_EMIN_spec;
            lemma_dyadic_pow2 ((prec_to_len p)-1) (mpfr_EMIN_spec-(prec_to_len p));
            assert(eval_abs r =. eval_abs (round_def r p rnd_mode));
            assert(eval_abs (round_def r p rnd_mode) <. mpfr_underflow_bound p);
            mpfr_underflow_post_cond_lemma r p rnd_mode (I32.v t) (as_fp h2 a)
            );
            assert (modifies_0 h1 h1b);
            mpfr_modifies_trans_lemma a h0 h1 h2;
            t
        end
    end else begin
        let t = mpfr_add1sp1_round a ap rnd_mode st in
	let h2 = ST.get() in
	mpfr_add1sp1_round_post_cond_lemma (sub1sp_exact (as_reg_fp h0 b) (as_reg_fp h0 c)) (I64.v (as_struct h0 a).mpfr_prec) (as_normal_ h1 ({as_struct h1 a with mpfr_exp = st.bx})) (st.rb <> 0uL) (st.sb <> 0uL) rnd_mode (I32.v t) (as_fp h2 a); 
	mpfr_modifies_trans_lemma a h0 h1 h2;
	t
    end
    end
