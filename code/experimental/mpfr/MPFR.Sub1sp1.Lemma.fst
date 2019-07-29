module MPFR.Sub1sp1.Lemma

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

val lemma_shift_left_mod_pow2: a:t -> s:U32.t -> k:nat -> Lemma
  (requires ((v a)%(pow2 k)=0)/\U32.v s<64 /\ k<64)//could be proven without the k<64 condition
  (ensures ((v (a<<^s))%(pow2 k)=0))
  
let lemma_shift_left_mod_pow2 a s k=
   shift_left_value_lemma (v a) U32.(v s);//a<<^s=(a*2^s)%(2^64)
   lemma_pow2_mod_mod (v a*pow2 U32.(v s)) 64 k;//a<<^s%(2^k)=a*(2^s)%(2^k)
   lemma_mul_mod_zero (v a) (pow2 U32.(v s)) (pow2 k)

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
    assert(b.limb*(pow2 (b.exp-b.len-elb))>c.limb*pow2 (c.exp-c.len-elb))

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
    lemma_mul_le_left (pow2 d) (pow2 63) (b.limb-1);
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
    
val lemma_sub1sp1_gt_1_valid: bp:mp_limb_t -> cp:mp_limb_t -> d:I64.t{I64.(0L<^d /\ d<^64L)} -> Lemma
    (requires (v bp>=pow2 63 /\ (v cp)%2=0))
    (ensures (let sb=UInt64.minus (cp<<^(int64_to_uint32 I64.(gmp_NUMB_BITS -^ d))) in
    bp -^ (if sb=^0uL then 0uL else 1uL)>^(cp >>^ (int64_to_uint32 d)) ))

let lemma_sub1sp1_gt_1_valid bp cp d=
    let sb=UInt64.minus (cp<<^(int64_to_uint32 I64.(gmp_NUMB_BITS -^ d))) in
    if (I64.v d)=1 then begin
      shift_left_value_lemma (v cp) 63;
      lemma_minus_eq_zero_sub (v (cp<<^(int64_to_uint32 I64.(gmp_NUMB_BITS -^ d))))
    end else begin
      shift_right_value_lemma (v cp) (I64.v d);
      lemma_div_le (v cp) (pow2 64) (pow2 (I64.v d));
      lemma_pow2_div 64 (I64.v d);
      lemma_pow2_le (64-(I64.v d)) 62;
      assert(v (cp >>^ (int64_to_uint32 d)) <= pow2 62);
      assert_norm(pow2 62 < pow2 63-1)
    end

val lemma_sub1sp1_gt_branch_1_high_prec: r:normal_fp -> a0:uint_t 64 -> sb_2:uint_t 64 -> mask:uint_t 64 -> p:pos -> Lemma
    (requires (0<p /\ p<64 /\ p<r.prec /\ mask=pow2 (64-p)-1 /\ r.len<128 /\ a0*pow2 64+sb_2=r.limb*pow2 (128-r.len)))
    (ensures (
    let rb=logand a0 (shift_left #64 1 (64-p-1)) in
    let sb=logor sb_2  (logxor (logand a0 mask) rb) in
    let ad=logand a0 (lognot mask) in
    rb_def r p=(rb<>0) /\
    sb_def r p=(sb<>0) /\
    ad*pow2 (high_mant r p).len=(high_mant r p).limb*pow2 64
    ))

let lemma_sub1sp1_gt_branch_1_high_prec r a0 sb_2 mask p=
    let rb=logand a0 (shift_left #64 1 (64-p-1)) in
    let sb=logor sb_2  (logxor (logand a0 mask) rb) in
    let ad=logand a0 (lognot mask) in
    lemma_pow2_lt (64-p-1) 64;
    lemma_nth_logand #64 a0 p;
    lemma_nth_pow2 #64 64 a0 sb_2 p;
    lemma_nth_pow2 #r.len (128-r.len) r.limb 0 p;
    assert(rb_def r p=(rb<>0));
    lemma_mod_mul r.limb (pow2 (r.len-p-1)) (pow2 (128-r.len));
    lemma_pow2_mul (r.len-p-1) (128-r.len);
    assert((r.limb%pow2 (r.len-p-1))*pow2 (128-r.len) =(a0*pow2 64+sb_2)%pow2 (128-p-1));
    assert(sb_def r p=(((a0*pow2 64+sb_2)%pow2 (128-p-1))<>0));
    assert(128-p-1>=64);

    (if sb=0 then begin
       logor_ge sb_2  (logxor (logand a0 mask) rb);
       if((logand a0 mask)<>rb) then logxor_neq_nonzero (logand a0 mask) rb;

       lemma_tl_zero_imp_mod_pow2 rb (64-p-1);
       logand_mask a0 (64-p);

       lemma_pow2_mul_mod r.limb (128-r.len) (128-p-1);
       lemma_pow2_mul_mod a0 64 (128-p-1);
       lemma_pow2_mod_mod a0 (64-p) (64-p-1)
    end else begin
      if sb_2<>0 then begin
         assert(sb_2%pow2 64<>0);
         assert(((a0*pow2 64+sb_2)%pow2 64)<>0);
         lemma_pow2_mod_mod (a0*pow2 64+sb_2) (128-p-1) 64
      end else begin
        logor_lemma_1 (logxor (logand a0 mask) rb);
        logor_commutative (logxor (logand a0 mask) rb) sb_2;
        lemma_pow2_mul_mod a0 64 (128-p-1);
        nth_lemma (logxor (logand a0 mask) rb) (logand a0 (logxor mask (shift_left #64 1 (64-p-1))));
        logxor_disjoint_zero #64 (pow2 (64-p-1)) (pow2 (64-p-1)-1) (64-p-1);
        lemma_pow2_double (64-p-1);
        logxor_inv #64 (pow2 (64-p-1)-1) (pow2 (64-p-1));
        logxor_commutative #64 (pow2 (64-p-1)-1) (pow2 (64-p-1));
        if p=63 then logand_lemma_1 a0
        else logand_mask a0 (64-p-1)
      end
    end);
    nth_lemma (shift_left (shift_right a0 (64-p)) (64-p)) ad;
    shift_right_value_lemma a0 (64-p);
    lemma_euclidean a0 (pow2 (64-p));
    lemma_multiple_div r.limb (pow2 (128-r.len));
    lemma_pow2_div_div (a0*pow2 64+sb_2) (128-r.len) (r.len-p);
    assert(r.limb=(a0*pow2 64+sb_2)/pow2 (128-r.len));
    lemma_div_distr (a0*pow2 64) sb_2 (pow2 64);
    assert(a0=(a0*pow2 64+sb_2)/pow2 64);
    lemma_pow2_div_div (a0*pow2 64+sb_2) 64 (64-p);
    assert(a0/pow2 (64-p)=(a0*pow2 64+sb_2)/pow2 (128-p));
    assert(ad=(r.limb/pow2 (r.len-p))*pow2 (64-p));
    lemma_pow2_mul (64-p) r.len;
    lemma_pow2_mul (r.len-p) 64;
    lemma_paren_mul_right (r.limb/pow2 (r.len-p)) (pow2 (64-p)) (pow2 r.len);
    lemma_paren_mul_right (r.limb/pow2 (r.len-p)) (pow2 (r.len-p)) (pow2 64)

val lemma_sub1sp1_gt_branch_1_rb_sb_value: r:normal_fp -> a0:uint_t 64 -> sb_2:uint_t 64 -> mask:uint_t 64 -> p:pos -> Lemma
    (requires (0<p /\ p<64 /\ mask=pow2 (64-p)-1 /\ r.len<128 /\ a0*pow2 64+sb_2=r.limb*pow2 (128-r.len)))
    (ensures (
    let rb=logand a0 (shift_left #64 1 (64-p-1)) in
    let sb=logor sb_2  (logxor (logand a0 mask) rb) in
    let ad=logand a0 (lognot mask) in
    rb_def r p=(rb<>0) /\
    sb_def r p=(sb<>0) /\
    ad*pow2 (high_mant r p).len=(high_mant r p).limb*pow2 64
    ))

let lemma_sub1sp1_gt_branch_1_rb_sb_value r a0 sb_2 mask p=
    let rb=logand a0 (shift_left #64 1 (64-p-1)) in
    let sb=logor sb_2  (logxor (logand a0 mask) rb) in
    let ad=logand a0 (lognot mask) in
    if p<r.prec then lemma_sub1sp1_gt_branch_1_high_prec r a0 sb_2 mask p
    else begin
      lemma_pow2_mod_product_zero r.limb (pow2 (128-r.len)) (r.len-r.prec) (128-r.len);
      lemma_pow2_mod_mod_zero (a0*pow2 64+sb_2) (128-r.prec) 64;
      lemma_add_mod sb_2 a0 (pow2 64);
      assert(sb_2=0);
      lemma_pow2_mul (64-r.prec) 64;
      lemma_mod_mul a0 (pow2 (64-r.prec)) (pow2 64);
      lemma_pow2_mod_mod_zero a0 (64-r.prec) (64-p);

      lemma_pow2_lt (64-p-1) 64;
      lemma_nth_logand #64 a0 p;
      lemma_mod_pow2_imp_tl_zero #64 a0 (64-p);
      logand_mask a0 (64-p);
      logxor_self #64 0;
      logor_self #64 0;

      nth_lemma a0 ad;
      if p>r.len then begin
        lemma_pow2_shift a0 r.limb 64 (128-r.len) (p-64);
        lemma_pow2_mul (p-r.len) 64
      end else begin
        lemma_pow2_shift a0 r.limb 64 (128-r.len) (r.len-64)
      end
    end

val lemma_sub1sp1_gt_branch_1_a0_bx: b:mpfr_reg_fp -> c:mpfr_reg_fp -> p:pos{b.prec=p /\ c.prec=p /\ p<64} -> sb_1:uint_t 64 -> a0_base:uint_t 64 -> Lemma
    (requires (b.exp>c.exp /\ b.exp-c.exp<64 /\ sb_1=add_mod #64 (pow2 64-1-(shift_left #64 c.limb (64-(b.exp-c.exp)))) 1 /\ a0_base=(b.limb-(if sb_1=0 then 0 else 1))-(shift_right #64 c.limb (b.exp-c.exp)) /\ a0_base<>0))
    (ensures (let r=sub1sp_exact b c in
              let cnt=64-(nbits a0_base) in
        normal_fp_cond r /\
        a0_base*pow2 64+sb_1=r.limb*pow2 (64-(b.exp-c.exp)) /\
        b.exp-cnt =(high_mant r p).exp
    ))

#set-options "--z3rlimit 400"

let lemma_sub1sp1_gt_branch_1_a0_bx b c p sb_1 a0_base=
    lemma_gt_exp_sub1sp b c;
    let r=sub1sp_exact b c in
    let cnt=64-(nbits a0_base) in
    let d=b.exp-c.exp in
    shift_left_value_lemma #64 c.limb (64-d);
    shift_right_value_lemma #64 c.limb d;
    lemma_multiple_div c.limb (pow2 (64-d));
    assert(shift_right #64 c.limb d=(c.limb*pow2 (64-d) / pow2 (64-d) / pow2 d));
    lemma_div_div (c.limb*pow2 (64-d)) (pow2 (64-d)) (pow2 d);
    lemma_pow2_mul (64-d) d;
    lemma_euclidean (c.limb*pow2 (64-d)) (pow2 64);
    assert(b.limb*pow2 64-c.limb*(pow2 (64-d))=a0_base*pow2 64+sb_1);
    lemma_distr_sub_left (b.limb*pow2 d) c.limb (pow2 64-d);
    assert((b.limb*pow2 d-c.limb)*(pow2 (64-d))=a0_base*pow2 64+sb_1);
    lemma_fp_exp_ge b c;
    assert(sub1sp_gt_limb b c=(b.limb*pow2 d-c.limb));

    lemma_nbits_pow2_add a0_base 64 sb_1;
    lemma_nbits_pow2_mul r.limb (64-d);

    assert(nbits (r.limb*(pow2 (64-d)))=nbits a0_base+64);
    assert(r.len=nbits (r.limb*(pow2 (64-d)))-(64-d));
    assert(nbits r.limb=nbits a0_base+d)

#set-options "--z3rlimit 100"
