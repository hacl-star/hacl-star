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
open MPFR.Lib.Spec
open MPFR.Sub1.Spec
open MPFR.Round.Spec
open MPFR.Maths

open MPFR.Lib
open MPFR.Exceptions

open MPFR.Exceptions.Lemma
(*open MPFR.Sub1sp1.Lemma*)
open MPFR.Add1sp1
open MPFR.Add1sp1.Lemma

module ST = FStar.HyperStack.ST
module I32 = FStar.Int32
module I64 = FStar.Int64
module U32 = FStar.UInt32

#set-options "--z3refresh --z3rlimit 100 --max_fuel 1 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 0"

private type mpfr_tmp_exp_t = x:mpfr_exp_t{I64.((*x >=^ mpfr_EMIN /\*) x <=^ mpfr_EMAX +^ 1L)}

let mpfr_sub1sp1_pre_cond h (a:mpfr_ptr) b c (p:mpfr_prec_t): GTot Type0=
        (* Memory safety *)
        mpfr_live h a /\ mpfr_live h b /\ mpfr_live h c /\
        mpfr_disjoint_or_equal h a b /\ mpfr_disjoint_or_equal h a c /\
        mpfr_disjoint_or_equal h b c /\
        length (as_struct h a).mpfr_d = 1 /\
        length (as_struct h b).mpfr_d = 1 /\ length (as_struct h c).mpfr_d = 1 /\
        (* Functional correctness *)
        I64.v p > 0 /\ I64.v p < 64 /\ p = (as_struct h a).mpfr_prec /\
        p = (as_struct h b).mpfr_prec /\ p = (as_struct h c).mpfr_prec /\
        mpfr_valid_cond h a /\ mpfr_reg_cond h b /\ mpfr_reg_cond h c

let mpfr_sub1sp1_pre_cond_2 h (a:mpfr_ptr) b c bx cx ap bp cp p sh: GTot Type0=
 (as_struct h b).mpfr_exp=bx /\
 (as_struct h c).mpfr_exp=cx /\ 
 (as_struct h a).mpfr_d==ap /\
 (as_struct h b).mpfr_d==bp /\
 (as_struct h c).mpfr_d==cp /\
 live h ap /\ live h bp /\ live h cp /\
 I64.v sh = I64.v gmp_NUMB_BITS - I64.v p

let mpfr_sub1sp1_post_cond h0 t h1 (a:mpfr_ptr) b c (p:mpfr_reg_prec_t) rnd_mode exact: GTot Type0=
        (* Memory safety *)
        mpfr_live h1 a /\ mpfr_live h1 b /\ mpfr_live h1 c /\
        mpfr_disjoint_or_equal h1 a b /\ mpfr_disjoint_or_equal h1 a c /\
        mpfr_disjoint_or_equal h1 b c /\ mpfr_modifies a h0 h1 /\
        (* Functional correctness *)
        mpfr_valid_cond h1 a /\
        mpfr_round_cond exact (I64.v p) rnd_mode (as_fp h1 a) /\
        mpfr_ternary_cond (I32.v t) exact (as_fp h1 a)

inline_for_extraction val count_leading_zeros: a:u64{not (a=^0uL)}->Tot (cnt:u32{U32.v cnt<32 /\ v (a<<^cnt)>=pow2 63 /\ v a*pow2 (U32.v cnt)<pow2 64 /\ U32.v cnt=64-(nbits (v a))})

let  count_leading_zeros a=admit()

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

val lemma_shift_left_mod_pow2: a:t -> s:U32.t -> k:nat -> Lemma
  (requires ((v a)%(pow2 k)=0)/\U32.v s<64 /\ k<64)//could be proven without the k<64 condition
  (ensures ((v (a<<^s))%(pow2 k)=0))
  
let lemma_shift_left_mod_pow2 a s k=
   shift_left_value_lemma (v a) U32.(v s);//a<<^s=(a*2^s)%(2^64)
   lemma_pow2_mod_mod (v a*pow2 U32.(v s)) 64 k;//a<<^s%(2^k)=a*(2^s)%(2^k)
   lemma_mul_mod_zero (v a) (pow2 U32.(v s)) (pow2 k)

let mpfr_sub1sp1_any_post_cond h0 s h1 (a:mpfr_ptr) b c (p:mpfr_reg_prec_t) rnd_mode exact: GTot Type0=
        (* Memory safety *)
        mpfr_live h1 a /\ mpfr_live h1 b /\ mpfr_live h1 c /\
        length (as_struct h1 a).mpfr_d = 1 /\
        length (as_struct h1 b).mpfr_d = 1 /\ length (as_struct h1 c).mpfr_d = 1 /\
        modifies_2 a (as_struct h1 a).mpfr_d h0 h1 /\ normal_cond h1 a /\ 
        mpfr_modifies a h0 h1 /\
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
        (sb_def r (I64.v p) = (v s.sb <> 0)) /\
        (high_mant r (I64.v p)).sign = (as_normal h1 a).sign)

val mpfr_sub1sp1_eq_rb_sb_lemma:
    b:mpfr_reg_fp -> c:mpfr_reg_fp -> p:pos -> Lemma
    (requires (
    b.prec=p /\ c.prec=p /\
    b.exp=c.exp /\
    b.limb<>c.limb
    ))
    (ensures (let r = sub1sp_exact b c in rb_def r p=false /\ sb_def r p=false))
    
let mpfr_sub1sp1_eq_rb_sb_lemma b c p=
    let r=sub1sp_exact b c in
    let b,c=if gt (eval_abs c) (eval_abs b) then c,b else b,c in
    assert(pow2 (b.exp-c.exp)=1);
    lemma_mod_distr_sub_zero (b.limb * pow2 (b.exp - c.exp)) c.limb (pow2 (c.len-c.prec));
    lemma_pow2_gt_rev (sub1sp_gt_len b c) (c.len-c.prec);
    assert(b.limb>=r.limb \/ c.limb>=r.limb);
    assert(pow2 b.len>=r.limb);
    assert(pow2 b.len>pow2 (r.len-1));
    lemma_pow2_gt_rev b.len (r.len-1);
    assert(r.limb%pow2 (b.len-b.prec)=0);
    if(p<r.prec) then (rb_value_lemma r p;
      lemma_pow2_mod_mod_zero r.limb (b.len-b.prec) (r.len-p-1);
      lemma_pow2_mod_mod_zero r.limb (b.len-b.prec) (r.len-p))

val lemma_fp_eq_cross:
    a:valid_fp -> b:valid_fp ->Lemma
    (requires (eval_abs a =. eval_abs b /\ a.exp=b.exp))
    (ensures (a.limb*pow2 b.len=b.limb*pow2 a.len)) 

let lemma_fp_eq_cross a b=
    let da,db=eval a,eval b in
    let elb=min da.exponent db.exponent in
    assert(a.limb*pow2(a.exp-a.len-elb)=b.limb*pow2(b.exp-b.len-elb));
    assert(a.limb*pow2(a.exp-a.len-elb)*pow2 a.len=b.limb*pow2 a.len*pow2(b.exp-b.len-elb));
    lemma_pow2_mul (a.exp-a.len-elb) a.len;
    assert(a.limb*pow2(a.exp-elb)=b.limb*pow2 a.len*pow2(b.exp-b.len-elb));
    assert(a.limb*pow2 b.len*pow2(a.exp-elb)=b.limb*pow2 a.len*pow2(b.exp-b.len-elb)*pow2 b.len);
    lemma_paren_mul_right (b.limb*pow2 a.len) (pow2 (b.exp-b.len-elb)) (pow2 b.len);
    lemma_pow2_mul (b.exp-b.len-elb) b.len;
    assert(a.limb*pow2 b.len*pow2(a.exp-elb)=(b.limb*pow2 a.len)*pow2(b.exp-elb));
    lemma_mul_simp (a.limb*pow2 b.len) (b.limb*pow2 a.len) (pow2 (a.exp-elb))

val mpfr_sub1sp1_eq_value_lemma:
    a:normal_fp -> b:mpfr_reg_fp -> c:mpfr_reg_fp -> cnt:nat -> p:pos -> Lemma
    (requires (
    b.prec=p /\ c.prec=p /\ p<64 /\
    b.exp=c.exp /\
    b.limb<>c.limb /\
    (let b,c=if gt (eval_abs c) (eval_abs b) then c,b else b,c in
    cnt=64-(nbits (b.limb-c.limb)) /\
    a.limb=(b.limb-c.limb)*pow2 cnt /\
    a.exp=b.exp-cnt /\
    a.len=64
    ) ))
    (ensures (let r = sub1sp_exact b c in  a.limb * pow2 (high_mant r p).len = (high_mant r p).limb * (pow2 64) /\ a.exp = (high_mant r p).exp))

let mpfr_sub1sp1_eq_value_lemma a b c cnt p=
    let r=sub1sp_exact b c in
    let b,c=if gt (eval_abs c) (eval_abs b) then c,b else b,c in
    let k=high_mant r p in
    assert(a.exp=k.exp);
    assert(eval_abs a=.eval_abs r);
    if p<=r.prec then begin 
      assert(r.len<b.len);
      lemma_pow2_lt (r.len-p) (b.len-p);
      assert(b.limb%pow2(b.len-p)=0);
      assert(c.limb%pow2(b.len-p)=0);
      lemma_mod_distr_sub_zero b.limb c.limb (pow2 (b.len-p));
      assert(r.limb%pow2(b.len-p)=0);
      lemma_pow2_mod_mod_zero r.limb (b.len-p) (r.len-p);
      assert(r.limb%pow2(r.len-p)=0);
      lemma_div_mul r.limb (pow2 (r.len-p));
      assert(r.limb=k.limb)
    end;
    assert(eval_abs r=.eval_abs k);
    lemma_fp_eq_cross a k
    

inline_for_extraction val mpfr_sub1sp1_eq:
    a:mpfr_ptr -> b:mpfr_ptr -> c:mpfr_ptr ->
    ap:buffer mp_limb_t -> bp:buffer mp_limb_t -> cp:buffer mp_limb_t ->
    bx:mpfr_reg_exp_t ->cx:mpfr_reg_exp_t
    ->rnd_mode:mpfr_rnd_t->
    p:mpfr_reg_prec_t -> sh:mpfr_reg_prec_t -> Stack state
    (requires (fun h-> mpfr_sub1sp1_pre_cond h a b c p /\
    mpfr_sub1sp1_pre_cond_2 h a b c bx cx ap bp cp p sh /\
    I64.(bx=^cx) /\
    I64.(as_val h bp<>as_val h cp)
    ))
    (ensures (fun h0 s h1->
    let exact=sub1sp_exact (as_fp h0 b) (as_fp h0 c) in
    mpfr_sub1sp1_any_post_cond h0 s h1 a b c p rnd_mode exact))

let mpfr_sub1sp1_eq a b c ap bp cp bx cx rnd_mode p sh =
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

val lemma_gt_exp_sub1sp:  b:mpfr_reg_fp -> c:mpfr_reg_fp -> Lemma
 (requires (b.exp>c.exp))
 (ensures (gt (eval_abs b) (eval_abs c)))

let lemma_gt_exp_sub1sp b c=
    let eb,ec=(eval_abs b),(eval_abs c) in
    let elb=min eb.exponent ec.exponent in
    assert(b.limb>=pow2 (b.len-1));
    assert(b.limb*(pow2 (b.exp-b.len-elb))>=pow2 (b.len-1)*(pow2 (b.exp-b.len-elb)));
    lemma_pow2_mul (b.len-1) (b.exp-b.len-elb);
    assert(b.limb*(pow2 (b.exp-b.len-elb))>=pow2 (b.exp-1-elb));
    assert(pow2 c.len>c.limb);
    lemma_pow2_le (c.exp-elb) (b.exp-1-elb);
    assert(pow2 (b.exp-1-elb)>=pow2 (c.exp-elb));
    lemma_pow2_mul c.len (c.exp-c.len-elb);
    assert(b.limb*(pow2 (b.exp-b.len-elb))>=(pow2 c.len)*(pow2 (c.exp-c.len-elb)))

val lemma_sub1sp1_gt_exp_2_limb1: b:mpfr_reg_fp -> c:mpfr_reg_fp -> p:pos{b.prec=p /\ c.prec=p /\ p<64} -> Lemma
    (requires (b.exp>c.exp /\ b.exp-c.exp>=64 /\ b.limb<>v mpfr_LIMB_HIGHBIT))
    (ensures (let r=sub1sp_exact b c in
        let d=b.exp-c.exp in
        r.limb>=pow2 (63+d)
    ))

let lemma_sub1sp1_gt_exp_2_limb1 b c p=
    lemma_gt_exp_sub1sp b c;
    let d=b.exp-c.exp in
    let r=sub1sp_exact b c in
    assert(r.limb=b.limb*pow2 d-c.limb);
    assert(c.limb<pow2 c.len);
    assert(c.len<=d);
    lemma_pow2_le c.len d;
    assert(r.limb>=(b.limb-1)*pow2 d);
    assert(b.limb-1>=pow2 63);
    lemma_pow2_mul 63 d;
    assert(r.limb>=pow2 (63+d))

val lemma_sub1sp1_gt_exp_2_limb2: b:mpfr_reg_fp -> c:mpfr_reg_fp -> p:pos{b.prec=p /\ c.prec=p /\ p<64} -> Lemma
    (requires (b.exp>c.exp /\ b.exp-c.exp>=64 /\ b.limb<>v mpfr_LIMB_HIGHBIT))
    (ensures (let r=sub1sp_exact b c in
        let d=b.exp-c.exp in
        r.limb<pow2 (64+d)
    ))

let lemma_sub1sp1_gt_exp_2_limb2 b c p=
    lemma_gt_exp_sub1sp b c;
    let d=b.exp-c.exp in
    let r=sub1sp_exact b c in
    assert(r.limb=b.limb*pow2 d-c.limb);
    assert(r.limb<=b.limb*pow2 d);
    assert(b.limb<pow2 b.len);
    assert(b.len=64);
    lemma_pow2_mul 64 d;
    assert(r.limb<pow2 (64+d))

val lemma_sub1sp1_gt_rb_sb_exp_2:  b:mpfr_reg_fp -> c:mpfr_reg_fp -> p:pos{b.prec=p /\ c.prec=p /\ p<64} -> Lemma
    (requires (b.exp>c.exp /\ b.exp-c.exp>=64 /\ b.limb<>v mpfr_LIMB_HIGHBIT))
    (ensures (let r=sub1sp_exact b c in
        r.exp=b.exp /\ rb_def r p /\ sb_def r p
    ))

let lemma_sub1sp1_gt_rb_sb_exp_2 b c p=
    lemma_gt_exp_sub1sp b c;
    let d=b.exp-c.exp in
    let r=sub1sp_exact b c in
    lemma_sub1sp1_gt_exp_2_limb1 b c p;
    lemma_sub1sp1_gt_exp_2_limb2 b c p;
    lemma_pow2_nbits_rev r.limb (64+d);
    (*sb*)
    lemma_pow2_le 64 (r.len-p-1);
    lemma_small_mod c.limb (pow2 (r.len - p - 1));
    let cm=c.limb % pow2 (r.len - p - 1) in
    lemma_pow2_mod_mod_zero b.limb (64-p) (r.len-p-d);
    lemma_mod_mul b.limb (pow2 (r.len-p-d)) (pow2 d);
    lemma_pow2_mul (r.len-p-d) d;
    lemma_pow2_mod_mod_zero (b.limb*pow2 d) (r.len-p) (r.len-p-1);
    lemma_mod_distr_sub (b.limb * pow2 d) c.limb (pow2 (r.len - p - 1));
    (*rb*)
    lemma_pow2_le 64 (r.len-p);
    lemma_small_mod c.limb (pow2 (r.len - p));
    lemma_mod_distr_sub (b.limb * pow2 d) c.limb (pow2 (r.len - p));
    lemma_small_mod_neg cm (pow2 (r.len - p));
    lemma_small_mod_neg cm (pow2 (r.len - p-1));
    rb_value_lemma r p

val lemma_sub1sp1_gt_value_2:  b:mpfr_reg_fp -> c:mpfr_reg_fp -> p:pos{b.prec=p /\ c.prec=p /\ p<64} -> Lemma
    (requires (b.exp>c.exp /\ b.exp-c.exp>=64 /\ b.limb<>v mpfr_LIMB_HIGHBIT))
    (ensures (let r=sub1sp_exact b c in
       (b.limb-(pow2 (64-p))) * pow2 (high_mant r p).len = (high_mant r p).limb * (pow2 64)
    ))

let lemma_sub1sp1_gt_value_2 b c p=
    lemma_gt_exp_sub1sp b c;
    let d=b.exp-c.exp in
    let r=sub1sp_exact b c in
    lemma_sub1sp1_gt_exp_2_limb1 b c p;
    lemma_sub1sp1_gt_exp_2_limb2 b c p;
    lemma_pow2_nbits_rev r.limb (64+d);
    lemma_pow2_mod_mod_zero b.limb (64-p) (r.len-p-d);
    lemma_mod_mul b.limb (pow2 (r.len-p-d)) (pow2 d);
    lemma_pow2_mul (r.len-p-d) d;
    lemma_pow2_le 64 (r.len-p);

    lemma_pow2_mul (r.len-64) (64-p);
    lemma_div_div (b.limb*pow2 d) (pow2 d) (pow2 (64-p));
    lemma_multiple_div b.limb (pow2 d);
    //!  assert((b.limb*pow2 d)/(pow2 (r.len-p))=b.limb/(pow2 (64-p)));
    lemma_small_div_neg c.limb (pow2 (r.len - p));
    lemma_div_distr (b.limb*pow2 d) (0-c.limb) (pow2 (r.len-p));
    //! assert((high_mant r p).limb*(pow2 64)=(b.limb / pow2 (64 - p) - 1)*(pow2 (r.len-p))*(pow2 64));
    lemma_paren_mul_right (b.limb / pow2 (64 - p) - 1) (pow2 (r.len-p)) (pow2 64);
    lemma_pow2_mul (r.len-p) 64;
    lemma_paren_mul_right (b.limb / pow2 (64 - p) - 1) (pow2 (64-p)) (pow2 r.len);
    lemma_pow2_mul r.len (64-p);
    //! assert((high_mant r p).limb*(pow2 64)=((b.limb / pow2 (64 - p) - 1)*(pow2 (64-p)))*pow2 r.len);
    lemma_distr_sub_left (b.limb/pow2 (64-p)) 1 (pow2 (64-p));
    lemma_div_mul b.limb (pow2 (64-p))
  

val lemma_sub1sp1_gt_rb_sb_exp_3:  b:mpfr_reg_fp -> c:mpfr_reg_fp -> p:pos{b.prec=p /\ c.prec=p /\ p<64} -> Lemma
    (requires (b.exp>c.exp /\ b.exp-c.exp>=64 /\ b.limb=v mpfr_LIMB_HIGHBIT))
    (ensures (let r=sub1sp_exact b c in
        r.exp=b.exp-1 /\ 
        rb_def r p=(p<63||b.exp-c.exp>64||c.limb=v mpfr_LIMB_HIGHBIT) /\
        sb_def r p=(p<63||b.exp-c.exp>64||c.limb<>v mpfr_LIMB_HIGHBIT)
    ))

let lemma_sub1sp1_gt_rb_sb_exp_3 b c p=
    lemma_gt_exp_sub1sp b c;
    let d=b.exp-c.exp in
    let r=sub1sp_exact b c in
    lemma_pow2_mul 63 d;
    lemma_pow2_le 64 (62+d);
    lemma_pow2_nbits_rev r.limb (63+d);
    
    lemma_mod_product_zero b.limb (pow2 d) (pow2 (64-p)) (pow2 d);
    lemma_pow2_mul (64-p) d;
    
    lemma_pow2_mod_mod_zero (b.limb*pow2 d) (64-p+d) (62+d-p);
    lemma_small_mod 0 (pow2 (62+d-p));
    lemma_mod_distr_sub (b.limb*pow2 d) c.limb (pow2 (62+d-p));
    lemma_mod_distr_sub 0 c.limb (pow2 (62+d-p));

    lemma_pow2_mod_mod_zero (b.limb*pow2 d) (64-p+d) (63+d-p);
    lemma_small_mod 0 (pow2 (63+d-p));
    lemma_mod_distr_sub (b.limb*pow2 d) c.limb (pow2 (63+d-p));
    lemma_mod_distr_sub 0 c.limb (pow2 (63+d-p));

    rb_value_lemma r p;
    if p<63||d>64 then begin
      lemma_pow2_le 64 (62+d-p);
      lemma_small_mod_neg c.limb (pow2 (62+d-p));
      lemma_pow2_le 64 (63+d-p);
      lemma_small_mod_neg c.limb (pow2 (63+d-p))
    end

    

val lemma_sub1sp1_gt_value_3:  b:mpfr_reg_fp -> c:mpfr_reg_fp -> p:pos{b.prec=p /\ c.prec=p /\ p<64} -> Lemma
    (requires (b.exp>c.exp /\ b.exp-c.exp>=64 /\ b.limb=v mpfr_LIMB_HIGHBIT))
    (ensures (let r=sub1sp_exact b c in
       (pow2 64-pow2 (64-p)) * pow2 (high_mant r p).len = (high_mant r p).limb * (pow2 64)
    ))

let lemma_sub1sp1_gt_value_3 b c p=
    lemma_gt_exp_sub1sp b c;
    let d=b.exp-c.exp in
    let r=sub1sp_exact b c in
    lemma_pow2_mul 63 d;
    lemma_pow2_le 64 (62+d);
    lemma_pow2_nbits_rev r.limb (63+d);
    
    lemma_mod_product_zero b.limb (pow2 d) (pow2 (64-p)) (pow2 d);
    lemma_pow2_mul (64-p) d;

    lemma_pow2_mod_mod_zero (b.limb*pow2 d) (64-p+d) (63+d-p);
    lemma_small_mod 0 (pow2 (63+d-p));
    
    lemma_div_distr (b.limb*pow2 d) (0-c.limb) (pow2 (63+d-p));
    lemma_pow2_mul (63+d-p) p;
    lemma_multiple_div (pow2 p) (pow2 (63+d-p));
    lemma_pow2_le 64 (63+d-p);
    lemma_small_div_neg c.limb (pow2 (63+d-p));
    lemma_distr_sub_left (pow2 p) 1 (pow2 (63+d-p));
    lemma_distr_sub_left (pow2 (63+d)) (pow2 (63+d-p)) (pow2 64);
    lemma_distr_sub_left (pow2 (64)) (pow2 (64-p)) (pow2 (63+d));
    lemma_pow2_mul (63+d-p) 64;
    lemma_pow2_mul (64-p) (63+d)
    

inline_for_extraction val mpfr_sub1sp1_gt:
    a:mpfr_ptr -> b:mpfr_ptr -> c:mpfr_ptr ->
    ap:buffer mp_limb_t -> bp:buffer mp_limb_t -> cp:buffer mp_limb_t ->
    bx:mpfr_reg_exp_t ->cx:mpfr_reg_exp_t
    ->rnd_mode:mpfr_rnd_t->
    p:mpfr_reg_prec_t -> sh:mpfr_reg_prec_t -> Stack state
    (requires (fun h->
    mpfr_sub1sp1_pre_cond h a b c p /\
    mpfr_sub1sp1_pre_cond_2 h a b c bx cx ap bp cp p sh /\
    I64.(bx>^cx)))
    (ensures (fun h0 s h1->
   (* let exact=sub1sp_exact (as_fp h0 b) (as_fp h0 c) in*)
    (*mpfr_sub1sp1_any_post_cond h0 s h1 a b c p rnd_mode exact*)  (* Memory safety *)
        mpfr_live h1 a /\ mpfr_live h1 b /\ mpfr_live h1 c /\
        length (as_struct h1 a).mpfr_d = 1 /\
        length (as_struct h1 b).mpfr_d = 1 /\ length (as_struct h1 c).mpfr_d = 1 /\
        modifies_2 a (as_struct h1 a).mpfr_d h0 h1 /\ normal_cond h1 a /\ 
        (as_normal h1 a).prec=I64.v p /\ (as_struct h0 a).mpfr_d==(as_struct h1 a).mpfr_d /\
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
        I64.v s.bx =(high_mant r (I64.v p)).exp /\
        (rb_def r (I64.v p) = (v s.rb <> 0)) /\
        (sb_def r (I64.v p) = (v s.sb <> 0)) /\
        (high_mant r (I64.v p)).sign = (as_normal h1 a).sign)))

let mpfr_sub1sp1_gt a b c ap bp cp bx cx rnd_mode p sh =
    let h0=ST.get() in
    mpfr_SET_SAME_SIGN a b;
    let d=I64.(bx-^cx) in
    let bp0ul=bp.(0ul) in
    let cp0ul=cp.(0ul) in
    let mask=mpfr_LIMB_MASK (int64_to_uint32 sh) in
    lemma_gt_exp_sub1sp (as_reg_fp h0 b) (as_reg_fp h0 c);
    if(I64.(d<^64L)) then begin 
      let sb=0uL-^(cp0ul<<^(int64_to_uint32 I64.(gmp_NUMB_BITS-^d))) in
      let a0=bp0ul -^ (if sb=0 then 0uL else 1uL) -^ (cp0ul >>^ (int64_to_uint32 d)) in
      let cnt=count_leading_zeros a0 in
      //let a0=0 in
      let rb=a0 &^ (mpfr_LIMB_ONE <<^ (int64_to_uint32 I64.(sh-^1L))) in
      let t=mk_state sh I64.(bx-^(uint32_to_int64 cnt)) rb sb in t
    end else begin admit();
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

(* specifications for mpfr_sub1sp1 *)
val mpfr_sub1sp1: a:mpfr_ptr -> b:mpfr_ptr -> c:mpfr_ptr ->
                  rnd_mode:mpfr_rnd_t -> p:mpfr_prec_t -> Stack i32
    (requires (fun h -> mpfr_sub1sp1_pre_cond h a b c p))
    (ensures  (fun h0 t h1 ->
    let exact=sub1sp_exact (as_fp h0 b) (as_fp h0 c) in
    mpfr_sub1sp1_post_cond h0 t h1 a b c p rnd_mode exact))

val lemma_underflow_fp_value: f:normal_fp -> p:nat{mpfr_PREC_COND p} -> Lemma
    (requires (f.exp<mpfr_EMIN_spec))
    (ensures (eval_abs f<.mpfr_underflow_bound p))

let lemma_underflow_fp_value f p=
    let d1=eval_abs f in
    let d2=mpfr_underflow_bound p in
    let elb=min d1.exponent d2.exponent in
    assert(f.limb<pow2 f.len);
    assert(f.limb*pow2(f.exp-f.len-elb)<pow2 f.len*pow2 (f.exp-f.len-elb));
    lemma_pow2_mul f.len (f.exp-f.len-elb);
    assert(f.limb*pow2(f.exp-f.len-elb)<pow2 (f.exp-elb));
    lemma_pow2_le (f.exp-elb) (mpfr_EMIN_spec-1-elb);
    assert(pow2 (f.exp-elb)<=pow2 (mpfr_EMIN_spec-1-elb));
    let l=prec_to_len p in
    lemma_pow2_mul (l-1) (mpfr_EMIN_spec-l-elb);
    assert(pow2 (mpfr_EMIN_spec-1-elb)<=d2.significand*pow2 (d2.exponent-elb))

let my_cond f p=(*f.exp-f.prec>=mpfr_EMIN_spec-p*)(*(f.exp-mpfr_EMIN_spec+p>=0) /\ (f.limb*pow2 (f.exp-mpfr_EMIN_spec+p))%(pow2 f.len)=0*)mpfr_EMIN_spec+f.len-f.exp-p<0 \/ f.limb%pow2 (mpfr_EMIN_spec+f.len-f.exp-p)=0

val lemma_mc_1: f:mpfr_fp -> p:pos{p=f.prec} -> Lemma
    (requires (MPFR_NUM? f.flag))
    (ensures (my_cond f p))
  
let lemma_mc_1 f p=assert(f.exp>=mpfr_EMIN_spec);
    assert(f.limb%pow2(f.len-p)=0);
    if(mpfr_EMIN_spec+f.len-f.exp-p>=0)then begin
      lemma_pow2_mod_mod_zero f.limb (f.len-p) (mpfr_EMIN_spec+f.len-f.exp-p)
    end
   (* assert(f.limb%pow2 (f.len-p)=0);
    lemma_mod_product_zero f.limb (pow2 p) (pow2 (f.len-p)) (pow2 p);
    lemma_pow2_mul (f.len-p) p;
    assert((f.limb*pow2 p)%(pow2 f.len)=0);
    lemma_pow2_mul (f.exp-mpfr_EMIN_spec) p;
    lemma_mul_mod_zero (f.limb*pow2 p) (pow2 (f.exp-mpfr_EMIN_spec)) (pow2 f.len)*)

val lemma_mc_2: b:mpfr_reg_fp -> c:mpfr_reg_fp{b.prec=c.prec} -> p:pos -> Lemma
    (requires (my_cond b p /\ my_cond c p))
    (ensures (my_cond (sub1sp_exact b c) p))

let lemma_mc_2 b c p=let exact=sub1sp_exact b c in
(* fabs (eval_abs a -. eval_abs b) =. eval_abs r*)
(*assert(eval_abs a)
assume(exact.flag=MPFR_NUM)*)admit()

val lemma_underflow_round: f:normal_fp -> p:mpfr_prec_t -> rnd_mode:mpfr_rnd_t -> Lemma
    (requires (my_cond f (I64.v p) /\ f.exp<mpfr_EMIN_spec))
    (ensures (let rnd=(round_def f (I64.v p) rnd_mode) in
    eval_abs f=.eval_abs rnd))

let lemma_underflow_round f p rnd_mode=();admit()

(*
let test_cond x rnd_mode sign h0 t h1=let p = (as_struct h1 x).mpfr_prec in
        mpfr_live h1 x /\ mpfr_modifies x h0 h1 /\
        mpfr_valid_cond h1 x /\ (as_struct h1 x).mpfr_sign = sign /\
	(forall (exact:normal_fp{exact.sign = I32.v sign /\ exact.exp < mpfr_EMIN_spec}).
	as_fp h1 x == mpfr_underflow_spec exact (I64.v p) rnd_mode /\
	I32.v t = mpfr_underflow_ternary_spec exact (I64.v p) rnd_mode)
        
val my_lemma   (requires ((r == mpfr_underflow_spec a p rnd_mode /\
               t = mpfr_underflow_ternary_spec a p rnd_mode) /\
	       eval_abs (round_def a p rnd_mode) <. mpfr_underflow_bound p /\
	       (MPFR_RNDN? rnd_mode ==>
	        eval_abs (rndn_def a p) >. fdiv_pow2 (mpfr_underflow_bound p) 1)))*)

val my_lemma: a:I64.t -> b:I64.t -> Lemma
  (requires I64.(a <^ b /\ not (a<^ (b -^ 1L))))
  (ensures I64.(a =^ (b -^ 1L)))

let my_lemma a b=admit()

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
    let st=if I64.(bx =^ cx) then begin
      mpfr_sub1sp1_eq a b c ap bp cp bx cx rnd_mode p sh
    end else begin  admit();
    let b,c,bx,cx,bp,cp=(if I64.(bx >=^ cx) then (mpfr_SET_SAME_SIGN a b;b,c,bx,cx,bp,cp) else (mpfr_SET_OPPOSITE_SIGN a b;c,b,cx,bx,cp,bp)) in       
    mpfr_sub1sp1_gt a b c ap bp cp bx cx rnd_mode p sh
    end in 
    let h1 = ST.get() in
    if I64.(st.bx <^ mpfr_EMIN) then begin 
        let s = mpfr_SIGN a in
        let ap0ul=ap.(0ul) in
        let t = if(rnd_mode=MPFR_RNDN&&(I64.(st.bx<^(mpfr_EMIN-^1L))||ap0ul=mpfr_LIMB_HIGHBIT)) then begin
            let t=mpfr_underflow a MPFR_RNDZ s in
            admit()//(eval_abs low <. ulp_p high (p + 1))
        end else begin admit();
            let t=mpfr_underflow a rnd_mode s in
            let h2=ST.get() in
(*
           (* lemma_mc_1 (as_reg_fp h0 b) (I64.v p);
            lemma_mc_1 (as_reg_fp h0 c) (I64.v p);
            assert(my_cond (as_reg_fp h0 b) (I64.v p));
            assert(my_cond (as_reg_fp h0 c) (I64.v p));*)
            (let exact=(sub1sp_exact (as_reg_fp h0 b) (as_reg_fp h0 c)) in
            let p=(as_struct h2 a).mpfr_prec in
 
//assert(my_cond exact (I64.v p));
            assert(exact.exp<mpfr_EMIN_spec);
            lemma_underflow_fp_value exact (I64.v p);
            assert(eval_abs exact<.mpfr_underflow_bound (I64.v p));
            assume(my_cond exact (I64.v p));
            lemma_underflow_round exact p rnd_mode;
            assert(eval_abs exact =. eval_abs (round_def exact (I64.v p) rnd_mode));
            assert(eval_abs (round_def exact (I64.v p) rnd_mode) <. mpfr_underflow_bound (I64.v p));
           // assume(not (MPFR_RNDN? rnd_mode));
//assert(exact.exp=I64.v st.bx /\ exact.limb=v ap0ul);admit();
          //  assert(exact.exp=mpfr_EMAX_spec-1(* /\ exact.limb<>v mpfr_LIMB_HIGHBIT*));admit();
            if(MPFR_RNDN? rnd_mode) then begin
            assert(not (I64.(st.bx<^(mpfr_EMIN-^1L))||ap0ul=mpfr_LIMB_HIGHBIT));
            my_lemma st.bx mpfr_EMIN;
            assert(I64.(st.bx=^(mpfr_EMIN-^1L)) && ap0ul <> mpfr_LIMB_HIGHBIT);
          //  (eval_abs low <. ulp_p high (p + 1))
            //assume(rndn_def exact (I64.v p)=add_one_ulp (rndz_def exact (I64.v p)));
             assert(eval_abs (rndz_def exact (I64.v p)) >=. fdiv_pow2 (mpfr_underflow_bound (I64.v p)) 1);
                assume(eval_abs (rndn_def exact (I64.v p)) >. fdiv_pow2 (mpfr_underflow_bound (I64.v p)) 1)
            end;
            assert((MPFR_RNDN? rnd_mode ==>
	            eval_abs (rndn_def exact (I64.v p)) >. fdiv_pow2 (mpfr_underflow_bound (I64.v p)) 1)));
            assert(I64.v p=I64.v (as_struct h2 a).mpfr_prec);

            mpfr_underflow_post_cond_lemma (sub1sp_exact (as_reg_fp h0 b) (as_reg_fp h0 c)) (I64.v p) rnd_mode (I32.v t) (as_fp h2 a);
*)            admit();t
        end in
        

	t
    end else begin admit();
        let t = mpfr_add1sp1_round a ap rnd_mode st in
	let h2 = ST.get() in
	mpfr_add1sp1_round_post_cond_lemma (sub1sp_exact (as_reg_fp h0 b) (as_reg_fp h0 c)) (I64.v p) (as_normal_ h1 ({as_struct h1 a with mpfr_exp = st.bx})) (st.rb <> 0uL) (st.sb <> 0uL) rnd_mode (I32.v t) (as_fp h2 a);
        mpfr_modifies_trans_lemma a h0 h1 h2;
	t
    end
 end
 
