module MPFR.Add1sp1.Lemma
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
open MPFR.Add1.Spec
open MPFR.Round.Spec
open MPFR.Dyadic
open MPFR.Maths

module I32 = FStar.Int32
module I64 = FStar.Int64
module U32 = FStar.UInt32

#set-options "--z3refresh --z3rlimit 100 --max_fuel 1 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 0"

(* intermediate results *)
private type mpfr_tmp_exp_t = x:mpfr_exp_t{I64.((*x >=^ mpfr_EMIN /\*) x <=^ mpfr_EMAX +^ 1L)}

(* pre-condition for mpfr_add1sp1_any *)
let mpfr_add1sp1_common_pre_cond a b c (p:mpfr_prec_t) h =
    mpfr_reg_cond_ h b /\ mpfr_reg_cond_ h c /\
    0 < I64.v p /\ I64.v p < I64.v gmp_NUMB_BITS /\
    a.mpfr_prec = p /\ b.mpfr_prec = p /\ c.mpfr_prec = p /\
    live h a.mpfr_d /\ live h b.mpfr_d /\ live h c.mpfr_d /\
    length a.mpfr_d = 1 /\ length b.mpfr_d = 1 /\ length c.mpfr_d = 1

let mpfr_add1sp1_any_pre_cond a b c (p:mpfr_prec_t) h =
    a.mpfr_sign = b.mpfr_sign /\
    mpfr_add1sp1_common_pre_cond a b c p h
    
(* pre-condition for mpfr_add1sp1_gt where b.exp > c.exp *)
let mpfr_add1sp1_gt_pre_cond a b c sh h =
    I64.v b.mpfr_exp > I64.v c.mpfr_exp /\
    I64.v sh = I64.v gmp_NUMB_BITS - I64.v a.mpfr_prec /\
    mpfr_add1sp1_common_pre_cond a b c I64.(gmp_NUMB_BITS -^ sh) h

(* lemmas and implementation for mpfr_add1sp1_gt_branch1 where d < sh *)
let mpfr_add1sp1_gt_branch1_pre_cond a b c sh d mask h =
    mpfr_add1sp1_gt_pre_cond a b c sh h /\
    I64.v d = I64.v b.mpfr_exp - I64.v c.mpfr_exp /\
    v mask = pow2 (I64.v sh) - 1 /\
    I64.v d < I64.v sh
    
(* lemmas and implementation for mpfr_add1sp1_gt_branch1 where sh <= d < 64 *)
let mpfr_add1sp1_gt_branch2_pre_cond a b c sh d mask h =
    mpfr_add1sp1_gt_pre_cond a b c sh h /\
    I64.v d = I64.v b.mpfr_exp - I64.v c.mpfr_exp /\
    v mask = pow2 (I64.v sh) - 1 /\
    I64.v d >= I64.v sh /\ I64.v d < I64.v gmp_NUMB_BITS
    
val mpfr_add1sp1_gt_branch12_a0_bx_lemma:
    h:mem -> a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
    sh:mpfr_reg_prec_t -> d:i64 -> mask:mp_limb_t -> Lemma
    (requires (mpfr_add1sp1_gt_branch1_pre_cond a b c sh d mask h \/
               mpfr_add1sp1_gt_branch2_pre_cond a b c sh d mask h))
    (ensures  (
    let r = add1sp_exact (as_reg_fp_ h b) (as_reg_fp_ h c) in
    let bx = b.mpfr_exp in
    let b0 = Seq.index (as_seq h b.mpfr_d) 0 in
    let c0 = Seq.index (as_seq h c.mpfr_d) 0 in
    let a0 = b0 +%^ (c0 >>^ (int64_to_uint32) d) in
    let a0, bx = if a0 <^ b0 then mpfr_LIMB_HIGHBIT |^ (a0 >>^ 1ul), I64.(bx +^ 1L) else a0, bx in
    v a0 = r.limb / pow2 (r.len - 64) /\ I64.v bx = r.exp))

let mpfr_add1sp1_gt_branch12_a0_bx_lemma h a b c sh d mask =
    admit();
    let r = add1sp_exact (as_reg_fp_ h b) (as_reg_fp_ h c) in
    let bx = b.mpfr_exp in
    let b0 = Seq.index (as_seq h b.mpfr_d) 0 in
    let c0 = Seq.index (as_seq h c.mpfr_d) 0 in
    let a0 = b0 +%^ (c0 >>^ (int64_to_uint32 d)) in
    let t0 = v b0 + v c0 / pow2 (I64.v d) in
    //! assert(v a0 = t0 % pow2 64);
    let a0, bx =
        if a0 <^ b0 then begin
	    //! assert(pow2 64 + v a0 = t0);
	    lemma_add_div (v a0) (pow2 63) 2;
	    //! assert(pow2 63 + v a0 / 2 = t0 / pow2 1);
	    let a0' = mpfr_LIMB_HIGHBIT |^ (a0 >>^ 1ul) in
	    let bx' = I64.(bx +^ 1L) in
	    lemma_logor_pow2_disjoint mpfr_LIMB_HIGHBIT (a0 >>^ 1ul) 63;
	    //! assert(v a0' = t0 / pow2 1);
	    a0', bx'
	end else begin
	    //! assert(v a0 = t0 / pow2 0);
	    a0, bx
	end in
    //! assert(v a0 = t0 / pow2 (I64.v bx - I64.v b.mpfr_exp));
    lemma_add_div (v c0) (v b0) (pow2 (I64.v d));
    //! assert(t0 = r.limb / pow2 (I64.v d));
    lemma_pow2_div_div r.limb (I64.v d) (I64.v bx - I64.v b.mpfr_exp);
    //! assert(v a0 = r.limb / pow2 (I64.v bx - I64.v b.mpfr_exp + I64.v d));
    lemma_pow2_div_range r.limb (I64.v bx - I64.v b.mpfr_exp + I64.v d) r.len;
    lemma_bit_length (v a0) 64 (r.len - I64.v bx + I64.v b.mpfr_exp - I64.v d);
    assert(I64.v bx = r.len + I64.v b.mpfr_exp - I64.v d - 64);
    ()

val mpfr_add1sp1_gt_branch12_value_lemma:
    h:mem -> a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
    sh:mpfr_reg_prec_t -> d:i64 -> mask:mp_limb_t -> Lemma
    (requires (mpfr_add1sp1_gt_branch1_pre_cond a b c sh d mask h \/
               mpfr_add1sp1_gt_branch2_pre_cond a b c sh d mask h))
    (ensures  (
    let p = I64.v a.mpfr_prec in
    let r = add1sp_exact (as_reg_fp_ h b) (as_reg_fp_ h c) in
    let r = high_mant r p in
    let bp = b.mpfr_d in
    let cp = c.mpfr_d in
    let bx = b.mpfr_exp in
    let b0 = Seq.index (as_seq h bp) 0 in
    let c0 = Seq.index (as_seq h cp) 0 in
    admit();
    let a0 = b0 +%^ (c0 >>^ (int64_to_uint32 d)) in
    let a0, bx = if a0 <^ b0 then mpfr_LIMB_HIGHBIT |^ (a0 >>^ 1ul), I64.(bx +^ 1L) else a0, bx in
    let a0 = a0 &^ (lognot mask) in
    v a0 * pow2 (r.len - 64) = r.limb /\ I64.v bx = r.exp /\
    v a0 >= pow2 63 /\ v a0 % pow2 (64 - p) = 0))

let mpfr_add1sp1_gt_branch12_value_lemma h a b c sh d mask =
    let p = I64.v a.mpfr_prec in
    let r = add1sp_exact (as_reg_fp_ h b) (as_reg_fp_ h c) in
    let bp = b.mpfr_d in
    let cp = c.mpfr_d in
    let bx = b.mpfr_exp in
    let b0 = Seq.index (as_seq h bp) 0 in
    let c0 = Seq.index (as_seq h cp) 0 in
    admit();
    let a0 = b0 +%^ (c0 >>^ (int64_to_uint32 d)) in
    let t0 = v b0 + v c0 / pow2 (I64.v d) in
    let a0, bx = if a0 <^ b0 then mpfr_LIMB_HIGHBIT |^ (a0 >>^ 1ul), I64.(bx +^ 1L) else a0, bx in
    mpfr_add1sp1_gt_branch12_a0_bx_lemma h a b c sh d mask;
    lemma_pow2_div_div (r.limb) (r.len - 64) (64 - p);
    //! assert(v a0 / pow2 (64 - p) = r.limb / pow2 (r.len - p));
    UInt.nth_lemma (UInt.shift_right (v a0) (64 - p)) (UInt.shift_right (UInt.logand (v a0) (UInt.lognot (v mask))) (64 - p));
    assert(v (a0 &^ lognot mask) / pow2 (64 - p) = r.limb / pow2 (r.len - p));
    lemma_lognot_mask_mod a0 mask (64 - p);
    //! assert(v (a0 &^ lognot mask) % pow2 (64 - p) = 0);
    let a0 = a0 &^ (lognot mask) in
    lemma_pow2_div_mul (v a0) (64 - p) (r.len - p);
    //! assert((v a0 / pow2 (64 - p)) * pow2 (r.len - p) = r.limb / pow2 (r.len - p) * pow2 (r.len - p));
    let r = high_mant r p in
    lemma_div_le (pow2 (r.len - 1)) (v a0 * pow2 (r.len - 64)) (pow2 (r.len - 64));
    lemma_pow2_div (r.len - 1) (r.len - 64);
    lemma_multiple_div (v a0) (pow2 (r.len - 64));
    //! assert(v a0 >= pow2 63);
    ()

val mpfr_add1sp1_gt_branch12_rb_lemma:
    h:mem -> a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
    sh:mpfr_reg_prec_t -> d:i64 -> mask:mp_limb_t -> Lemma
    (requires (mpfr_add1sp1_gt_branch1_pre_cond a b c sh d mask h \/
               mpfr_add1sp1_gt_branch2_pre_cond a b c sh d mask h))
    (ensures  (
    let p = I64.v a.mpfr_prec in
    let r = add1sp_exact (as_reg_fp_ h b) (as_reg_fp_ h c) in
    let bp = b.mpfr_d in
    let cp = c.mpfr_d in
    let b0 = Seq.index (as_seq h bp) 0 in
    let c0 = Seq.index (as_seq h cp) 0 in
    let a0 = b0 +%^ (c0 >>^ (int64_to_uint32 d)) in
    let a0 = if a0 <^ b0 then mpfr_LIMB_HIGHBIT |^ (a0 >>^ 1ul) else a0 in
    let rb = a0 &^ (mpfr_LIMB_ONE <<^ (int64_to_uint32 I64.(sh -^ 1L))) in
    rb_def r p = (v rb <> 0)))

let mpfr_add1sp1_gt_branch12_rb_lemma h a b c sh d mask = 
    let p = I64.v a.mpfr_prec in
    let r = add1sp_exact (as_reg_fp_ h b) (as_reg_fp_ h c) in
    let bp = b.mpfr_d in
    let cp = c.mpfr_d in
    let b0 = Seq.index (as_seq h bp) 0 in
    let c0 = Seq.index (as_seq h cp) 0 in
    let a0 = b0 +%^ (c0 >>^ (int64_to_uint32 d)) in
    let a0 = if a0 <^ b0 then mpfr_LIMB_HIGHBIT |^ (a0 >>^ 1ul) else a0 in
    mpfr_add1sp1_gt_branch12_a0_bx_lemma h a b c sh d mask;
    //! assert(v a0 = r.limb / pow2 (r.len - 64));
    UInt.slice_left_lemma (UInt.to_vec #r.len r.limb) 64;
    //! assert(UInt.nth (v a0) p = UInt.nth #r.len r.limb p);
    let rb = a0 &^ (mpfr_LIMB_ONE <<^ (int64_to_uint32 I64.(sh -^ 1L))) in
    lemma_pow2_small_mod (I64.v sh - 1) 64;
    //! assert(v (mpfr_LIMB_ONE <<^ I64.(sh -^ 1ul)) = pow2 (I64.v sh - 1));
    lemma_bit_mask_value a0 (mpfr_LIMB_ONE <<^ (int64_to_uint32 I64.(sh -^ 1L))) p;
    assert(rb_def r p=(v rb <> 0))

val mpfr_add1sp1_gt_branch12_former_sb_lemma:
    h:mem -> a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
    sh:mpfr_reg_prec_t -> d:i64 -> mask:mp_limb_t -> Lemma
    (requires (mpfr_add1sp1_gt_branch1_pre_cond a b c sh d mask h \/
               mpfr_add1sp1_gt_branch2_pre_cond a b c sh d mask h))
    (ensures  (
    let p = I64.v a.mpfr_prec in
    let r = add1sp_exact (as_reg_fp_ h b) (as_reg_fp_ h c) in
    let bp = b.mpfr_d in
    let cp = c.mpfr_d in
    let b0 = Seq.index (as_seq h bp) 0 in
    let c0 = Seq.index (as_seq h cp) 0 in
    let a0 = b0 +%^ (c0 >>^ (int64_to_uint32 d)) in
    let a0 = if a0 <^ b0 then mpfr_LIMB_HIGHBIT |^ (a0 >>^ 1ul) else a0 in
    let rb = a0 &^ (mpfr_LIMB_ONE <<^ (int64_to_uint32 I64.(sh -^ 1L))) in
    let sb = (a0 &^ mask) ^^ rb in
    v sb = r.limb % pow2 (r.len - p - 1) / pow2 (r.len - 64)))

let mpfr_add1sp1_gt_branch12_former_sb_lemma h a b c sh d mask =
    let p = I64.v a.mpfr_prec in
    let r = add1sp_exact (as_reg_fp_ h b) (as_reg_fp_ h c) in
    let bp = b.mpfr_d in
    let cp = c.mpfr_d in
    let b0 = Seq.index (as_seq h bp) 0 in
    let c0 = Seq.index (as_seq h cp) 0 in
    let a0 = b0 +%^ (c0 >>^ (int64_to_uint32 d)) in
    let a0 = if a0 <^ b0 then mpfr_LIMB_HIGHBIT |^ (a0 >>^ 1ul) else a0 in
    let rb = a0 &^ (mpfr_LIMB_ONE <<^ (int64_to_uint32 I64.(sh -^ 1L))) in
    let sb = (a0 &^ mask) ^^ rb in
    lemma_pow2_small_mod (I64.v sh - 1) 64;
    //! assert(v (mpfr_LIMB_ONE <<^ I64.(sh -^ 1ul)) = pow2 (I64.v sh - 1));
    lemma_bit_mask (mpfr_LIMB_ONE <<^ (int64_to_uint32 I64.(sh -^ 1L))) (64 - I64.v sh);
    lemma_tail_mask mask (I64.v sh);
    let rmask = mpfr_LIMB_MASK (int64_to_uint32 I64.(sh -^ 1L)) in
    UInt.nth_lemma #64 (v (mask ^^ (mpfr_LIMB_ONE <<^ (int64_to_uint32 I64.(sh -^ 1L))))) (v rmask);
    lemma_xor_and_distr (v a0) (v mask) (v (mpfr_LIMB_ONE <<^ (int64_to_uint32 I64.(sh -^ 1L))));
    //! assert(sb = (a0 &^ rmask));
    lemma_tail_mask_value a0 rmask (I64.v sh - 1);
    //! assert(v sb = (v a0) % pow2 (I64.v sh - 1));
    mpfr_add1sp1_gt_branch12_a0_bx_lemma h a b c sh d mask;
    lemma_pow2_mod_div r.limb (r.len - p - 1) (r.len - 64)

val mpfr_add1sp1_gt_branch1_sb_lemma:
    h:mem -> a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
    sh:mpfr_reg_prec_t -> d:i64 -> mask:mp_limb_t -> Lemma
    (requires (mpfr_add1sp1_gt_branch1_pre_cond a b c sh d mask h))
    (ensures  (
    let p = I64.v a.mpfr_prec in
    let r = add1sp_exact (as_reg_fp_ h b) (as_reg_fp_ h c) in
    let bp = b.mpfr_d in
    let cp = c.mpfr_d in
    let b0 = Seq.index (as_seq h bp) 0 in
    let c0 = Seq.index (as_seq h cp) 0 in
    let a0 = b0 +%^ (c0 >>^ (int64_to_uint32 d)) in
    let a0 = if a0 <^ b0 then mpfr_LIMB_HIGHBIT |^ (a0 >>^ 1ul) else a0 in
    let rb = a0 &^ (mpfr_LIMB_ONE <<^ (int64_to_uint32 I64.(sh -^ 1L))) in
    let sb = (a0 &^ mask) ^^ rb in
    sb_def r p = (v sb <> 0)))

let mpfr_add1sp1_gt_branch1_sb_lemma h a b c sh d mask =
    let p = I64.v a.mpfr_prec in
    let r = add1sp_exact (as_reg_fp_ h b) (as_reg_fp_ h c) in
    let bp = b.mpfr_d in
    let cp = c.mpfr_d in
    let b0 = Seq.index (as_seq h bp) 0 in
    let c0 = Seq.index (as_seq h cp) 0 in
    let a0 = b0 +%^ (c0 >>^ (int64_to_uint32 d)) in
    let a0 = if a0 <^ b0 then mpfr_LIMB_HIGHBIT |^ (a0 >>^ 1ul) else a0 in
    let rb = a0 &^ (mpfr_LIMB_ONE <<^ (int64_to_uint32 I64.(sh -^ 1L))) in
    let sb = (a0 &^ mask) ^^ rb in 
    mpfr_add1sp1_gt_branch12_a0_bx_lemma h a b c sh d mask;
    lemma_pow2_mul_mod (v b0) (I64.v d) (r.len - 64);
    lemma_pow2_mod_mod_zero (v b0) (I64.v sh) (r.len - 64 - I64.v d);
    //! assert(v b0 * pow2 (I64.v d) % pow2 (r.len - 64) = 0);
    lemma_pow2_mod_mod_zero (v c0) (I64.v sh) (r.len - 64);
    //! assert(v c0 % pow2 (r.len - 64) = 0);
    assert(v c0>=0);
    lemma_mod_distr_zero (v b0 * pow2 (I64.v d)) (v c0) (pow2 (r.len - 64));
    //! assert(r.limb % pow2 (r.len - 64) = 0);
    mpfr_add1sp1_gt_branch12_former_sb_lemma h a b c sh d mask;
    lemma_pow2_mod_mod r.limb (r.len - p - 1) (r.len - 64);
    assert((r.limb % pow2 (r.len - p - 1))%(pow2 (r.len - 64))=0);
    lemma_div_mul (r.limb % pow2 (r.len - p - 1)) (pow2 (r.len - 64));
    assert(v sb * pow2 (r.len - 64) = r.limb % pow2 (r.len - p - 1));
    lemma_mul_zero (v sb) (pow2 (r.len - 64))

val mpfr_add1sp1_gt_branch2_latter_sb_lemma:
    h:mem -> a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
    sh:mpfr_reg_prec_t -> d:i64 -> mask:mp_limb_t -> Lemma
    (requires (mpfr_add1sp1_gt_branch2_pre_cond a b c sh d mask h))
    (ensures  (
    let r = add1sp_exact (as_reg_fp_ h b) (as_reg_fp_ h c) in
    let bp = b.mpfr_d in
    let cp = c.mpfr_d in
    let b0 = Seq.index (as_seq h bp) 0 in
    let c0 = Seq.index (as_seq h cp) 0 in
    let sb = c0 <<^ (int64_to_uint32 I64.(gmp_NUMB_BITS -^ d)) in
    let a0 = b0 +%^ (c0 >>^ (int64_to_uint32 d)) in
    (v sb <> 0) = (r.limb % pow2 (I64.v d) <> 0)))

let mpfr_add1sp1_gt_branch2_latter_sb_lemma h a b c sh d mask =
    let r = add1sp_exact (as_reg_fp_ h b) (as_reg_fp_ h c) in
    let bp = b.mpfr_d in
    let cp = c.mpfr_d in
    let b0 = Seq.index (as_seq h bp) 0 in
    let c0 = Seq.index (as_seq h cp) 0 in
    let sb = c0 <<^ (int64_to_uint32 I64.(gmp_NUMB_BITS -^ d)) in
    lemma_pow2_mul_mod (v c0) (64 - I64.v d) 64;
    //! assert(v sb = (v c0 % pow2 (I64.v d)) * pow2 (64 - I64.v d));
    let t0 = v b0 + v c0 / pow2 (I64.v d) in
    lemma_distr_add_right (pow2 (I64.v d)) (v b0) (v c0 / pow2 (I64.v d));
    lemma_euclidean (v c0) (pow2 (I64.v d));
    assert(t0 * pow2 (I64.v d) + v c0 % pow2 (I64.v d) = r.limb);
    lemma_add_mod (v c0 % pow2 (I64.v d)) t0 (pow2 (I64.v d));
    lemma_pow2_mod_mod (v c0) (I64.v d) (I64.v d);
    assert(v c0 % pow2 (I64.v d) = r.limb % pow2 (I64.v d));
    lemma_mul_zero (v c0 % pow2 (I64.v d)) (pow2 (64 - I64.v d))

val mpfr_add1sp1_gt_branch2_sb_lemma:
    h:mem -> a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
    sh:mpfr_reg_prec_t -> d:i64 -> mask:mp_limb_t -> Lemma
    (requires (mpfr_add1sp1_gt_branch2_pre_cond a b c sh d mask h))
    (ensures  (
    let p = I64.v a.mpfr_prec in
    let r = add1sp_exact (as_reg_fp_ h b) (as_reg_fp_ h c) in
    let bp = b.mpfr_d in
    let cp = c.mpfr_d in
    let b0 = Seq.index (as_seq h bp) 0 in
    let c0 = Seq.index (as_seq h cp) 0 in
    let sb = c0 <<^ (int64_to_uint32 I64.(gmp_NUMB_BITS -^ d)) in
    let a0 = b0 +%^ (c0 >>^ (int64_to_uint32 d)) in
    let sb, a0 =
        if a0 <^ b0 then
	    sb |^ (a0 &^ 1uL), mpfr_LIMB_HIGHBIT |^ (a0 >>^ 1ul)
	else sb, a0 in
    let rb = a0 &^ (mpfr_LIMB_ONE <<^ (int64_to_uint32 I64.(sh -^ 1L))) in
    let sb = sb |^ ((a0 &^ mask) ^^ rb) in
    sb_def r p = (v sb <> 0)))

let mpfr_add1sp1_gt_branch2_sb_lemma h a b c sh d mask = 
    let p = I64.v a.mpfr_prec in
    let r = add1sp_exact (as_reg_fp_ h b) (as_reg_fp_ h c) in
    let bp = b.mpfr_d in
    let cp = c.mpfr_d in
    let b0 = Seq.index (as_seq h bp) 0 in
    let c0 = Seq.index (as_seq h cp) 0 in
    let sb = c0 <<^ (int64_to_uint32 I64.(gmp_NUMB_BITS -^ d)) in
    mpfr_add1sp1_gt_branch2_latter_sb_lemma h a b c sh d mask;
    let a0 = b0 +%^ (c0 >>^ (int64_to_uint32 d)) in
    lemma_add_div (v c0) (v b0) (pow2 (I64.v d));
    lemma_pow2_mod_mod (v b0 + v c0 / pow2 (I64.v d)) 64 1;
    //! assert((r.limb / pow2 (I64.v d)) % pow2 1 = v a0 % 2);
    lemma_tail_mask_value a0 1uL 1;
    //! assert((r.limb / pow2 (I64.v d) % pow2 1 <> 0) = (v (a0 &^ 1uL) <> 0));
    mpfr_add1sp1_gt_branch12_a0_bx_lemma h a b c sh d mask;
    let sb, a0 =
        if a0 <^ b0 then begin
	    lemma_sb_logor #r.len r.limb (r.len - 64) (I64.v d) sb (a0 &^ 1uL);
	    sb |^ (a0 &^ 1uL), mpfr_LIMB_HIGHBIT |^ (a0 >>^ 1ul)
	end else begin
	    sb, a0
	end in
    //! assert((r.limb % pow2 (r.len - 64) <> 0) = (v sb <> 0));
    let rb = a0 &^ (mpfr_LIMB_ONE <<^ (int64_to_uint32 I64.(sh -^ 1L))) in
    let sb' = (a0 &^ mask) ^^ rb in
    mpfr_add1sp1_gt_branch12_former_sb_lemma h a b c sh d mask;
    lemma_pow2_mod_div r.limb (r.len - p - 1) (r.len - 64);
    //! assert((r.limb / pow2 (r.len - 64) % pow2 (I64.v sh - 1) <> 0) = (v sb' <> 0));
    lemma_sb_logor #r.len r.limb (r.len - p - 1) (r.len - 64) sb sb'

(* lemmas and implementation for mpfr_add1sp1_gt_branch1 where d >= 64 *)
let mpfr_add1sp1_gt_branch3_pre_cond a b c sh h =
    mpfr_add1sp1_gt_pre_cond a b c sh h /\
    I64.v b.mpfr_exp - I64.v c.mpfr_exp >= I64.v gmp_NUMB_BITS

val mpfr_add1sp1_gt_branch3_value_lemma:
    h:mem -> a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
    sh:mpfr_reg_prec_t -> Lemma
    (requires (mpfr_add1sp1_gt_branch3_pre_cond a b c sh h))
    (ensures  (
    let p = I64.v a.mpfr_prec in
    let r = add1sp_exact (as_reg_fp_ h b) (as_reg_fp_ h c) in
    let r = high_mant r p in
    let bp = b.mpfr_d in
    let bx = b.mpfr_exp in
    let b0 = Seq.index (as_seq h bp) 0 in
    let a0 = b0 in
    v a0 * pow2 (r.len - 64) = r.limb /\ I64.v bx = r.exp /\
    v a0 >= pow2 63 /\ v a0 % pow2 (64 - p) = 0))

let mpfr_add1sp1_gt_branch3_value_lemma h a b c sh =
    let p = I64.v a.mpfr_prec in
    let r = add1sp_exact (as_reg_fp_ h b) (as_reg_fp_ h c) in
    let bp = b.mpfr_d in
    let cp = c.mpfr_d in
    let bx = b.mpfr_exp in
    let cx = c.mpfr_exp in
    let d = I64.v bx - I64.v cx in
    let b0 = Seq.index (as_seq h bp) 0 in
    let c0 = Seq.index (as_seq h cp) 0 in
    let a0 = b0 in
    lemma_pow2_mul_range (v b0) d 64;
    lemma_multiple_mod (v b0) (pow2 d);
    lemma_pow2_multiple_le (v b0 * pow2 d) (d + 64) d;
    lemma_pow2_le 64 d;
    //! assert(v b0 * pow2 d + v c0 < pow2 (d + 64));
    lemma_bit_length r.limb r.len (d + 64);
    //! assert(I32.v bx = r.exp);
    lemma_pow2_mul_mod (v b0) d (r.len - p);
    lemma_div_distr (v b0 * pow2 d) (v c0) (pow2 (r.len - p));
    lemma_pow2_mul_div (v b0) d (r.len - p);
    lemma_pow2_lt d (r.len - p);
    lemma_small_div (v c0) (pow2 (r.len - p));
    //! assert(v a0 / pow2 (64 - p) = r.limb / pow2 (r.len - p));
    lemma_pow2_div_mul (v a0) (64 - p) (r.len - p)

val mpfr_add1sp1_gt_branch3_rb_lemma:
    h:mem -> a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
    sh:mpfr_reg_prec_t -> Lemma
    (requires (mpfr_add1sp1_gt_branch3_pre_cond a b c sh h))
    (ensures  (
    let p = I64.v a.mpfr_prec in
    let r = add1sp_exact (as_reg_fp_ h b) (as_reg_fp_ h c) in
    let rb = 0uL in
    rb_def r p = (v rb <> 0)))

let mpfr_add1sp1_gt_branch3_rb_lemma h a b c sh =
    let p = I64.v a.mpfr_prec in
    let r = add1sp_exact (as_reg_fp_ h b) (as_reg_fp_ h c) in
    let bp = b.mpfr_d in
    let cp = c.mpfr_d in
    let bx = b.mpfr_exp in
    let cx = c.mpfr_exp in
    let d = I64.v bx - I64.v cx in
    let b0 = Seq.index (as_seq h bp) 0 in
    let c0 = Seq.index (as_seq h cp) 0 in
    lemma_pow2_mul_range (v b0) d 64;
    lemma_multiple_mod (v b0) (pow2 d);
    lemma_pow2_multiple_le (v b0 * pow2 d) (d + 64) d;
    lemma_pow2_le 64 d;
    //! assert(v b0 * pow2 d + v c0 < pow2 (d + 64));
    lemma_bit_length r.limb r.len (d + 64);
    //! assert(r.len = d + 64);
    UInt.slice_left_lemma (UInt.to_vec #r.len r.limb) 64;
    lemma_div_distr (v b0 * pow2 d) (v c0) (pow2 d);
    lemma_multiple_div (v b0) (pow2 d);
    lemma_pow2_le 64 d;
    lemma_small_div (v c0) (pow2 d);
    //! assert(UInt.nth (v b0) p = UInt.nth #r.len r.limb p)
    lemma_mod_pow2_imp_tl_zero (v b0) (64 - p);
    assert(UInt.nth (v b0) p = Seq.index (Seq.slice (UInt.to_vec (v b0)) p 64) 0)

val mpfr_add1sp1_gt_branch3_sb_lemma:
    h:mem -> a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
    sh:mpfr_reg_prec_t -> Lemma
    (requires (mpfr_add1sp1_gt_branch3_pre_cond a b c sh h))
    (ensures  (
    let p = I64.v a.mpfr_prec in
    let r = add1sp_exact (as_reg_fp_ h b) (as_reg_fp_ h c) in
    let sb = 1uL in
    sb_def r p = (v sb <> 0)))

let mpfr_add1sp1_gt_branch3_sb_lemma h a b c sh =
    let p = I64.v a.mpfr_prec in
    let r = add1sp_exact (as_reg_fp_ h b) (as_reg_fp_ h c) in
    let bp = b.mpfr_d in
    let cp = c.mpfr_d in
    let bx = b.mpfr_exp in
    let cx = c.mpfr_exp in
    let d = I64.v bx - I64.v cx in
    let b0 = Seq.index (as_seq h bp) 0 in
    let c0 = Seq.index (as_seq h cp) 0 in
    lemma_pow2_mul_range (v b0) d 64;
    lemma_multiple_mod (v b0) (pow2 d);
    lemma_pow2_multiple_le (v b0 * pow2 d) (d + 64) d;
    lemma_pow2_le 64 d;
    //! assert(v b0 * pow2 d + v c0 < pow2 (d + 64));
    lemma_bit_length r.limb r.len (d + 64);
    //! assert(r.len = d + 64);
    lemma_mod_distr (v b0 * pow2 d) (v c0) (pow2 (r.len - p - 1));
    lemma_pow2_mul_mod (v b0) d (r.len - p - 1);
    lemma_pow2_mod_mod_zero (v b0) (64 - p) (r.len - p - 1 - d);
    lemma_pow2_le 64 (r.len - p - 1);
    lemma_small_mod (v c0) (pow2 (r.len - p - 1));
    //! assert(r.limb % pow2 (r.len - p - 1) = v c0);
    ()

(* pre-condition for mpfr_add1sp1_eq where b.exp = c.exp *)
let mpfr_add1sp1_eq_pre_cond a b c sh h =
    I64.v b.mpfr_exp = I64.v c.mpfr_exp /\
    I64.v sh = I64.v gmp_NUMB_BITS - I64.v a.mpfr_prec /\
    mpfr_add1sp1_any_pre_cond a b c I64.(gmp_NUMB_BITS -^ sh) h

val mpfr_add1sp1_eq_value_lemma:
    h:mem -> a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
    sh:mpfr_reg_prec_t -> Lemma
    (requires (mpfr_add1sp1_eq_pre_cond a b c sh h))
    (ensures  (
    let p = I64.v a.mpfr_prec in
    let r = add1sp_exact (as_reg_fp_ h b) (as_reg_fp_ h c) in
    let r = high_mant r p in
    let bp = b.mpfr_d in
    let cp = c.mpfr_d in
    let b0 = Seq.index (as_seq h bp) 0 in
    let c0 = Seq.index (as_seq h cp) 0 in
    let a0 = (b0 >>^ 1ul) +%^ (c0 >>^ 1ul) in
    let bx = I64.(b.mpfr_exp +^ 1L) in
    let rb = a0 &^ (mpfr_LIMB_ONE <<^ (int64_to_uint32 I64.(sh -^ 1L))) in
    let a0 = a0 ^^ rb in
    admit();
    v a0 * pow2 (r.len - 64) = r.limb /\ I64.v bx = r.exp /\
    v a0 >= pow2 63 /\ v a0 % pow2 (64 - p) = 0))

let mpfr_add1sp1_eq_value_lemma h a b c sh =
    admit();
    let p = I64.v a.mpfr_prec in
    let r = add1sp_exact (as_reg_fp_ h b) (as_reg_fp_ h c) in
    let bp = b.mpfr_d in
    let cp = c.mpfr_d in
    let b0 = Seq.index (as_seq h bp) 0 in
    let c0 = Seq.index (as_seq h cp) 0 in
    let a0 = (b0 >>^ 1ul) +%^ (c0 >>^ 1ul) in
    lemma_pow2_mod_mod_zero (v b0) (I64.v sh) 1;
    lemma_div_distr (v b0) (v c0) (pow2 1);
    //! assert(v a0 = r.limb / pow2 (r.len - 64));
    UInt.slice_left_lemma (UInt.to_vec #r.len r.limb) 64;
    //! assert(UInt.nth (v a0) p = UInt.nth #r.len r.limb p);
    lemma_pow2_mod_div (v b0) (I64.v sh) 1;
    lemma_pow2_mod_div (v c0) (I64.v sh) 1;
    lemma_mod_distr_zero (v b0 / 2) (v c0 / 2) (pow2 (I64.v sh - 1));
    //! assert(v a0 % pow2 (I64.v sh - 1) = 0);
    lemma_mod_pow2_imp_tl_zero (v a0) (I64.v sh - 1);
    assert(forall (i:nat{p + 1 <= i /\ i < 64}). UInt.nth (v a0) i = false);
    let rb = a0 &^ (mpfr_LIMB_ONE <<^ (int64_to_uint32 I64.(sh -^ 1L))) in
    lemma_pow2_small_mod (I64.v sh - 1) 64;
    //! assert(v (mpfr_LIMB_ONE <<^ I64.(sh -^ 1ul)) = pow2 (I64.v sh - 1));
    let mask = mpfr_LIMB_ONE <<^ (int64_to_uint32 I64.(sh -^ 1L)) in
    lemma_bit_mask_value a0 mask p;
    lemma_bit_mask mask p;
    //! assert(forall (i:nat{p <= i /\ i < 64}). UInt.nth (v (a0 ^^ rb)) i = false);
    lemma_tl_zero_imp_mod_pow2 (v (a0 ^^ rb)) (I64.v sh);
    UInt.nth_lemma (UInt.shift_right (v a0) (64 - p)) (UInt.shift_right (UInt.logxor (v a0) (v rb)) (64 - p));
    //! assert(v a0 / pow2 (64 - p) = v (a0 ^^ rb) / pow2 (64 - p));
    lemma_pow2_div_div r.limb (r.len - 64) (64 - p);
    lemma_pow2_div_mul (v (a0 ^^ rb)) (64 - p) (r.len - p);
    //! assert(v (a0 ^^ rb) * pow2 (r.len - 64) = r.limb / pow2 (r.len - p) * pow2 (r.len - p));
    let a0 = a0 ^^ rb in
    let r = high_mant r p in
    //! assert(v a0 * pow2 (r.len - 64) = r.limb);
    lemma_pow2_div_range r.limb (r.len - 64) r.len;
    lemma_multiple_div (v a0) (pow2 (r.len - 64));
    //! assert(v a0 >= pow2 63);
    ()

(* exact the same as mpfr_add1sp1_gt_branch12_rb_lemma *)
val mpfr_add1sp1_eq_rb_sb_lemma:
    h:mem -> a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
    sh:mpfr_reg_prec_t -> Lemma
    (requires (mpfr_add1sp1_eq_pre_cond a b c sh h))
    (ensures  (
    let p = I64.v a.mpfr_prec in
    let r = add1sp_exact (as_reg_fp_ h b) (as_reg_fp_ h c) in
    let bp = b.mpfr_d in
    let cp = c.mpfr_d in
    let b0 = Seq.index (as_seq h bp) 0 in
    let c0 = Seq.index (as_seq h cp) 0 in
    let a0 = (b0 >>^ 1ul) +%^ (c0 >>^ 1ul) in
    let rb = a0 &^ (mpfr_LIMB_ONE <<^ (int64_to_uint32 I64.(sh -^ 1L))) in
    let sb = 0uL in
    rb_def r p = (v rb <> 0) /\ sb_def r p = (v sb <> 0)))
    
let mpfr_add1sp1_eq_rb_sb_lemma h a b c sh =
    let p = I64.v a.mpfr_prec in
    let r = add1sp_exact (as_reg_fp_ h b) (as_reg_fp_ h c) in
    let bp = b.mpfr_d in
    let cp = c.mpfr_d in
    let b0 = Seq.index (as_seq h bp) 0 in
    let c0 = Seq.index (as_seq h cp) 0 in
    let a0 = (b0 >>^ 1ul) +%^ (c0 >>^ 1ul) in
    lemma_pow2_mod_mod_zero (v b0) (I64.v sh) 1;
    lemma_div_distr (v b0) (v c0) (pow2 1);
    //! assert(v a0 = r.limb / pow2 (r.len - 64));
    UInt.slice_left_lemma (UInt.to_vec #r.len r.limb) 64;
    //! assert(UInt.nth (v a0) p = UInt.nth #r.len r.limb p);
    let rb = a0 &^ (mpfr_LIMB_ONE <<^ (int64_to_uint32 I64.(sh -^ 1L))) in
    lemma_pow2_small_mod (I64.v sh - 1) 64;
    //! assert(v (mpfr_LIMB_ONE <<^ I64.(sh -^ 1ul)) = pow2 (I64.v sh - 1));
    lemma_bit_mask_value a0 (mpfr_LIMB_ONE <<^ (int64_to_uint32 I64.(sh -^ 1L))) p


(* Rounding lemmas *)
val mpfr_add1sp1_is_even_lemma: a0:mp_limb_t -> sh:mpfr_prec_t{I64.v sh > 0 /\ I64.v sh < 64} ->
    high:normal_fp{high.len >= 64 /\ high.prec = 64 - I64.v sh} -> Lemma
    (requires (v a0 * pow2 (high.len - 64) = high.limb))
    (ensures  (is_even high = ((a0 &^ (mpfr_LIMB_ONE <<^ (int64_to_uint32 sh))) =^ 0uL)))

let mpfr_add1sp1_is_even_lemma a0 sh high =
    let p = 64 - I64.v sh in
    lemma_multiple_div (v a0) (pow2 (high.len - 64));
    assert(v a0 = high.limb / pow2 (high.len - 64));
    lemma_pow2_div_range high.limb (high.len - 64) high.len;
    slice_left_nth_lemma #high.len high.limb 64;
    assert(UInt.nth (v a0) p = UInt.nth #high.len high.limb p);
    let gb = a0 &^ (mpfr_LIMB_ONE <<^ (int64_to_uint32 sh)) in
    lemma_pow2_small_mod (I64.v sh) 64;
    //! assert(v (mpfr_LIMB_ONE <<^ sh) = pow2 (I64.v sh));
    lemma_bit_mask_value a0 (mpfr_LIMB_ONE <<^ (int64_to_uint32 sh)) (p - 1)

(* perform rounding with high part of significand, rounding/sticky bit *)
let mpfr_add1sp1_round_spec (high:normal_fp) (rb:bool) (sb:bool) (rnd_mode:mpfr_rnd_t):
    Tot (r:normal_fp{r.prec = high.prec}) =
    if rb = false && sb = false then high
    else if MPFR_RNDN? rnd_mode then begin
	if rb = false || (sb = false && is_even high)
	then high
	else add_one_ulp high
    end else if mpfr_IS_LIKE_RNDZ rnd_mode (high.sign < 0) then high
    else add_one_ulp high

val mpfr_round_rb_sb_lemma: a:normal_fp -> p:pos ->
    high:normal_fp{high.prec = p /\ eval high =. eval (high_mant a p)} ->
    rb:bool{rb = rb_def a p} -> sb:bool{sb = sb_def a p} -> rnd_mode:mpfr_rnd_t -> Lemma
    (eval (mpfr_add1sp1_round_spec high rb sb rnd_mode) =. eval (round_def a p rnd_mode))

#set-options "--z3rlimit 200"

let mpfr_round_rb_sb_lemma a p high rb sb rnd_mode =
    match rnd_mode with |_ -> (*Tells F* to consider each rounding mode separately*)
    if (p<a.prec) then begin
      rb_sb_lemma a p;
      eval_eq_reveal_lemma high (high_mant a p);
      eval_eq_intro_lemma (add_one_ulp high) (add_one_ulp (high_mant a p))
    end 

#set-options "--z3rlimit 100"

val eval_eq_round2_cond: a:normal_fp -> h:normal_fp -> rnd_mode:mpfr_rnd_t -> r:mpfr_fp -> p:pos{mpfr_PREC_COND p} -> Lemma
  (requires (a.sign=h.sign /\ a.prec=p /\ h.prec=p /\ r.prec=p /\ eval_abs a=.eval_abs h /\  mpfr_round2_cond a rnd_mode r))
  (ensures (mpfr_round2_cond h rnd_mode r))

let eval_eq_round2_cond a h rnd_mode r p= 
  if eval_abs a >. mpfr_overflow_bound a.prec then
     dyadic_gt_trans_lemma (eval_abs a) (eval_abs h) (mpfr_overflow_bound p)
  else if eval_abs a <. mpfr_underflow_bound a.prec then
     dyadic_lt_trans_lemma  (eval_abs a) (eval_abs h) (mpfr_underflow_bound p)
  else
     eval_eq_intro_lemma a h

val mpfr_round_cond_lemma: a:normal_fp -> p:pos{mpfr_PREC_COND p} ->
    high:normal_fp{high.prec = p /\ high.sign = (high_mant a p).sign /\
                   high.exp = (high_mant a p).exp /\
		   high.limb * pow2 (high_mant a p).len = (high_mant a p).limb * pow2 high.len} ->
    rb:bool{rb = rb_def a p} -> sb:bool{sb = sb_def a p} -> rnd_mode:mpfr_rnd_t ->
    r:mpfr_fp{r.prec = p} -> Lemma
    (requires (mpfr_round2_cond (mpfr_add1sp1_round_spec high rb sb rnd_mode) rnd_mode r))
    (ensures  (mpfr_round_cond a p rnd_mode r))

let mpfr_round_cond_lemma a p high rb sb rnd_mode r =
    if (a.len>=high.len) then begin
       lemma_pow2_sub high.limb (high_mant a p).limb (high_mant a p).len high.len
    end else begin 
       lemma_pow2_sub (high_mant a p).limb high.limb high.len (high_mant a p).len
    end;
    assert(eval_abs high =. eval_abs (high_mant a p));
    eval_eq_intro_lemma high (high_mant a p);
    mpfr_round_rb_sb_lemma a p high rb sb rnd_mode;
    eval_eq_reveal_lemma (mpfr_add1sp1_round_spec high rb sb rnd_mode) (round_def a p rnd_mode);
    eval_eq_round2_cond (mpfr_add1sp1_round_spec high rb sb rnd_mode) (round_def a p rnd_mode) rnd_mode r p

(* lemmas about ternary value *)
val mpfr_truncate_ternary_cond_lemma: a:normal_fp{mpfr_EXP_COND a.exp} ->
    p:pos{mpfr_PREC_COND p} ->
    high:normal_fp{high.prec = p /\ eval high =. eval (high_mant a p)} ->
    rb:bool{rb = rb_def a p} -> sb:bool{sb = sb_def a p} -> rnd_mode:mpfr_rnd_t ->
    t:int -> r:mpfr_fp{r.prec = p} -> Lemma
    (requires (mpfr_round2_cond high rnd_mode r /\
               t = (if rb = false && sb = false then 0 else -a.sign)))
    (ensures  (mpfr_ternary_cond t a r))

let mpfr_truncate_ternary_cond_lemma a p high rb sb rnd_mode t r =
    eval_eq_reveal_lemma high (high_mant a p);
    mpfr_round2_cond_in_range_lemma (high_mant a p) rnd_mode r;
    rb_sb_lemma a p;
    if rb = false && sb = false then eval_eq_intro_lemma a (high_mant a p)
    else if a.sign > 0 then eval_lt_intro_lemma (high_mant a p) a
    else eval_lt_intro_lemma a (high_mant a p)

let mpfr_add1sp1_add_one_ulp_ternary_spec 
    (high:normal_fp{mpfr_PREC_COND high.prec})
    (rnd_mode:mpfr_rnd_t): Tot int =
    if eval_abs high <. mpfr_overflow_bound high.prec then high.sign
    else if mpfr_IS_LIKE_RNDZ rnd_mode (high.sign < 0) then -high.sign else high.sign

val mpfr_add_one_ulp_ternary_cond_lemma: a:normal_fp{mpfr_EXP_COND a.exp} ->
    p:pos{mpfr_PREC_COND p} ->
    high:normal_fp{high.prec = p /\ eval high =. eval (high_mant a p) /\
                   eval_abs (high_mant a p) <. eval_abs a} ->
    rnd_mode:mpfr_rnd_t -> t:int -> r:mpfr_fp{r.prec = p} -> Lemma
    (requires (mpfr_round2_cond (add_one_ulp high) rnd_mode r /\
               t = mpfr_add1sp1_add_one_ulp_ternary_spec high rnd_mode))
    (ensures  (mpfr_ternary_cond t a r))

let mpfr_add_one_ulp_ternary_cond_lemma a p high rnd_mode t r =
    eval_eq_reveal_lemma high (high_mant a p);
    exp_impl_no_overflow_lemma high;
    exp_impl_no_underflow_lemma high;
    if eval_abs high <. mpfr_overflow_bound p then begin
        add_one_ulp_lt_lemma high (mpfr_max_value 1 p);
	no_overflow_impl_exp_lemma (add_one_ulp high);
	mpfr_round2_cond_in_range_lemma (add_one_ulp high) rnd_mode r;
	if a.sign > 0 then eval_lt_intro_lemma a (add_one_ulp high)
	else eval_lt_intro_lemma (add_one_ulp high) a
    end else begin
        assert(mpfr_overflow_bound p =. eval_abs high);
	if mpfr_IS_LIKE_RNDZ rnd_mode (high.sign < 0) then
	    if high.sign > 0 then eval_lt_intro_lemma (mpfr_max_value high.sign high.prec) a
	    else eval_lt_intro_lemma a (mpfr_max_value high.sign high.prec)
	else ()
    end

let mpfr_add1sp1_ternary_spec 
    (high:normal_fp{mpfr_PREC_COND high.prec}) 
    (rb:bool) (sb:bool) (rnd_mode:mpfr_rnd_t): Tot int =
    if rb = false && sb = false then 0
    else if MPFR_RNDN? rnd_mode then begin
	if rb = false || (sb = false && is_even high)
	then -high.sign
	else mpfr_add1sp1_add_one_ulp_ternary_spec high rnd_mode
    end else if mpfr_IS_LIKE_RNDZ rnd_mode (high.sign < 0) then -high.sign
    else mpfr_add1sp1_add_one_ulp_ternary_spec high rnd_mode

val mpfr_ternary_cond_lemma: a:normal_fp{mpfr_EXP_COND a.exp} ->
    p:pos{mpfr_PREC_COND p} ->
    high:normal_fp{high.prec = p /\ high.sign = (high_mant a p).sign /\
                   high.exp = (high_mant a p).exp /\
		   high.limb * pow2 (high_mant a p).len = (high_mant a p).limb * pow2 high.len} ->
    rb:bool{rb = rb_def a p} -> sb:bool{sb = sb_def a p} -> rnd_mode:mpfr_rnd_t ->
    t:int -> r:mpfr_fp{r.prec = p} -> Lemma
    (requires (mpfr_round2_cond (mpfr_add1sp1_round_spec high rb sb rnd_mode) rnd_mode r /\
               t = mpfr_add1sp1_ternary_spec high rb sb rnd_mode))
    (ensures  (mpfr_ternary_cond t a r))

let mpfr_ternary_cond_lemma a p high rb sb rnd_mode t r =
    if ((high_mant a p).len>=high.len) then begin
       lemma_pow2_sub high.limb (high_mant a p).limb (high_mant a p).len high.len
    end else begin 
       lemma_pow2_sub (high_mant a p).limb high.limb high.len (high_mant a p).len
    end;
    assert(eval_abs high =. eval_abs (high_mant a p));
    if rb = false && sb = false then
        mpfr_truncate_ternary_cond_lemma a p high rb sb rnd_mode t r
    else if MPFR_RNDN? rnd_mode then begin
	if rb = false || (sb = false && is_even high)
	then mpfr_truncate_ternary_cond_lemma a p high rb sb rnd_mode t r
	else begin
            rb_sb_lemma a p;
            mpfr_add_one_ulp_ternary_cond_lemma a p high rnd_mode t r
	end
    end else if mpfr_IS_LIKE_RNDZ rnd_mode (high.sign < 0) then
        mpfr_truncate_ternary_cond_lemma a p high rb sb rnd_mode t r
    else begin
        rb_sb_lemma a p;
        mpfr_add_one_ulp_ternary_cond_lemma a p high rnd_mode t r;admit() (*How is this non-obvious ?*)
    end

val mpfr_add1sp1_round_post_cond_lemma: a:normal_fp{mpfr_EXP_COND a.exp} ->
    p:pos{mpfr_PREC_COND p} ->
    high:normal_fp{high.prec = p /\ high.sign = (high_mant a p).sign  /\
                   high.exp = (high_mant a p).exp /\
		   high.limb * pow2 (high_mant a p).len = (high_mant a p).limb * pow2 high.len} ->
    rb:bool{rb = rb_def a p} -> sb:bool{sb = sb_def a p} -> rnd_mode:mpfr_rnd_t ->
    t:int -> r:mpfr_fp{r.prec = p} -> Lemma
    (requires (mpfr_round2_cond (mpfr_add1sp1_round_spec high rb sb rnd_mode) rnd_mode r /\
               t = mpfr_add1sp1_ternary_spec high rb sb rnd_mode))
    (ensures  (mpfr_round_cond a p rnd_mode r /\
               mpfr_ternary_cond t a r))
               
let mpfr_add1sp1_round_post_cond_lemma a p high rb sb rnd_mode t r =
    mpfr_round_cond_lemma a p high rb sb rnd_mode r;
    mpfr_ternary_cond_lemma a p high rb sb rnd_mode t r
