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
open MPFR.Add1.Spec
open MPFR.Round.Spec
open MPFR.Maths

module I64 = FStar.Int64
module I32 = FStar.Int32
module U32 = FStar.UInt32

#set-options "--z3refresh --z3rlimit 100 --max_fuel 1 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 0"

(* specifications for mpfr_add1sp1 *)
val mpfr_add1sp1_pre_cond: a:mpfr_ptr -> b:mpfr_ptr -> c:mpfr_ptr ->
                           p:mpfr_prec_t -> h:mem -> GTot Type0
    
let mpfr_add1sp1_pre_cond a b c p h =
    (* Memory safety *)
    mpfr_live h a /\ mpfr_live h b /\ mpfr_live h c /\
    mpfr_disjoint_or_equal h a b /\ mpfr_disjoint_or_equal h a c /\
    mpfr_disjoint_or_equal h b c /\
    length (as_struct h a).mpfr_d = 1 /\
    length (as_struct h b).mpfr_d = 1 /\ length (as_struct h c).mpfr_d = 1 /\
    (* Functional correctness *)
    U32.v p > 0 /\ U32.v p < 64 /\ p = (as_struct h a).mpfr_prec /\
    p = (as_struct h b).mpfr_prec /\ p = (as_struct h c).mpfr_prec /\
    (as_struct h a).mpfr_sign = (as_struct h b).mpfr_sign /\
    mpfr_valid_cond h a /\ mpfr_reg_cond h b /\ mpfr_reg_cond h c

val mpfr_add1sp1_post_cond: a:mpfr_ptr -> b:mpfr_ptr -> c:mpfr_ptr ->
                            rnd_mode:mpfr_rnd_t -> p:mpfr_reg_prec_t ->
			    h0:mem{mpfr_add1sp1_pre_cond a b c p h0} ->
			    f:i32 -> h1:mem -> GTot Type0

let mpfr_add1sp1_post_cond a b c rnd_mode p h0 f h1 =
    let exact = add1sp_exact (as_fp h0 b) (as_fp h0 c) in
    (* Memory safety *)
    mpfr_live h1 a /\ mpfr_live h1 b /\ mpfr_live h1 c /\
    mpfr_disjoint_or_equal h1 a b /\ mpfr_disjoint_or_equal h1 a c /\
    mpfr_disjoint_or_equal h1 b c /\ mpfr_modifies a h0 h1 /\
    (* Functional correctness *)
    mpfr_valid_cond h1 a /\ 
    (*mpfr_round_cond exact (U32.v p) rnd_mode (as_fp h1 a) /\*)
    mpfr_ternary_cond (I32.v f) exact (as_fp h1 a)

val mpfr_add1sp1: a:mpfr_ptr -> b:mpfr_ptr -> c:mpfr_ptr ->
                  rnd_mode:mpfr_rnd_t -> p:mpfr_reg_prec_t -> Stack i32
    (requires (fun h -> mpfr_add1sp1_pre_cond a b c p h))
    (ensures  (fun h0 f h1 -> mpfr_add1sp1_post_cond a b c rnd_mode p h0 f h1))

(* implementations *)

(* intermediate results *)
private type mpfr_tmp_exp_t = x:mpfr_exp_t{I32.(x >=^ mpfr_EMIN /\ x <=^ mpfr_EMAX +^ 1l)}

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

(* pre/post-condition for mpfr_add1sp1_any *)
let mpfr_add1sp1_common_pre_cond a b c (p:mpfr_reg_prec_t) h =
    mpfr_reg_cond_ h b /\ mpfr_reg_cond_ h c /\
    U32.v p < U32.v gmp_NUMB_BITS /\
    a.mpfr_prec = p /\ b.mpfr_prec = p /\ c.mpfr_prec = p /\
    live h a.mpfr_d /\ live h b.mpfr_d /\ live h c.mpfr_d /\
    length a.mpfr_d = 1 /\ length b.mpfr_d = 1 /\ length c.mpfr_d = 1

let mpfr_add1sp1_any_pre_cond a b c (p:mpfr_reg_prec_t) h =
    a.mpfr_sign = b.mpfr_sign /\
    mpfr_add1sp1_common_pre_cond a b c p h
    
let mpfr_add1sp1_any_post_cond a b c h0 s h1 =
    let p = U32.v a.mpfr_prec in
    live h1 a.mpfr_d /\ live h1 b.mpfr_d /\ live h1 c.mpfr_d /\
    length a.mpfr_d = 1 /\ length b.mpfr_d = 1 /\ length c.mpfr_d = 1 /\
    modifies_1 a.mpfr_d h0 h1 /\ normal_cond_ h1 a /\
    U32.v a.mpfr_prec = U32.v b.mpfr_prec /\
    U32.v a.mpfr_prec = U32.v c.mpfr_prec /\
    mpfr_reg_cond_ h0 b /\ mpfr_reg_cond_ h0 c /\
    (let r = add1sp_exact (as_reg_fp_ h0 b) (as_reg_fp_ h0 c) in
    as_val h1 a.mpfr_d * pow2 (r.len - 64) = (high_mant r p).limb /\
    U32.v s.sh = U32.v gmp_NUMB_BITS - p /\
    I32.v s.bx = (high_mant r p).exp /\
    (v s.rb <> 0 <==> rb_def r p) /\
    (v s.sb <> 0 <==> sb_def r p))

val mpfr_add1sp1_any_post_cond_comm_lemma:
    a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct -> h0:mem -> s:state -> h1:mem -> Lemma
    (requires (mpfr_add1sp1_any_post_cond a b c h0 s h1))
    (ensures  (mpfr_add1sp1_any_post_cond a c b h0 s h1))

let mpfr_add1sp1_any_post_cond_comm_lemma a b c h0 s h1 = ()

(* pre-condition for mpfr_add1sp1_gt where b.exp > c.exp *)
let mpfr_add1sp1_gt_pre_cond a b c sh h =
    I32.v b.mpfr_exp > I32.v c.mpfr_exp /\
    U32.v sh = U32.v gmp_NUMB_BITS - U32.v a.mpfr_prec /\
    mpfr_add1sp1_common_pre_cond a b c U32.(gmp_NUMB_BITS -^ sh) h

(* lemmas and implementation for mpfr_add1sp1_gt_branch1 where d < sh *)
let mpfr_add1sp1_gt_branch1_pre_cond a b c sh d mask h =
    mpfr_add1sp1_gt_pre_cond a b c sh h /\
    U32.v d = I32.v b.mpfr_exp - I32.v c.mpfr_exp /\
    v mask = pow2 (U32.v sh) - 1 /\
    U32.v d < U32.v sh
    
val mpfr_add1sp1_gt_branch1_a0_bx_lemma:
    h:mem -> a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
    sh:mpfr_reg_prec_t -> d:u32 -> mask:mp_limb_t -> Lemma
    (requires (mpfr_add1sp1_gt_branch1_pre_cond a b c sh d mask h))
    (ensures  (
    let r = add1sp_exact (as_reg_fp_ h b) (as_reg_fp_ h c) in
    let bx = b.mpfr_exp in
    let b0 = Seq.index (as_seq h b.mpfr_d) 0 in
    let c0 = Seq.index (as_seq h c.mpfr_d) 0 in
    let a0 = b0 +%^ (c0 >>^ d) in
    let a0, bx = if a0 <^ b0 then mpfr_LIMB_HIGHBIT |^ (a0 >>^ 1ul), I32.(bx +^ 1l) else a0, bx in
    v a0 * pow2 (r.len - 64) = r.limb /\ I32.v bx = r.exp))

let mpfr_add1sp1_gt_branch1_a0_bx_lemma h a b c sh d mask =
    let r = add1sp_exact (as_reg_fp_ h b) (as_reg_fp_ h c) in
    let bx = b.mpfr_exp in
    let b0 = Seq.index (as_seq h b.mpfr_d) 0 in
    let c0 = Seq.index (as_seq h c.mpfr_d) 0 in
    let a0 = b0 +%^ (c0 >>^ d) in
    let t0 = v b0 + v c0 / pow2 (U32.v d) in
    //! assert(v a0 = t0 % pow2 64);
    let a0, bx =
        if a0 <^ b0 then begin
	    //! assert(pow2 64 + v a0 = t0);
	    lemma_div_distr (pow2 64) (v a0) 2;
	    //! assert(pow2 63 + v a0 / 2 = t0 / pow2 1);
	    let a0' = mpfr_LIMB_HIGHBIT |^ (a0 >>^ 1ul) in
	    let bx' = I32.(bx +^ 1l) in
	    lemma_logor_disjoint mpfr_LIMB_HIGHBIT (a0 >>^ 1ul) 63;
	    //! assert(v a0' = t0 / pow2 1);
            lemma_pow2_mod_mod_zero (v b0) (U32.v sh) 1;
            //! assert(v b0 % pow2 1 = 0);
            lemma_pow2_mod_mod_zero (v c0) (U32.v sh) (U32.v d + 1);
            lemma_pow2_mod_div (v c0) (U32.v d + 1) (U32.v d);
	    //! assert(v c0 / pow2 (U32.v d) % pow2 1 = 0);
	    lemma_mod_distr_zero (v b0) (v c0 / pow2 (U32.v d)) (pow2 1);
	    //! assert(t0 / pow2 1 * pow2 1 = t0);
	    lemma_pow2_div_mul t0 1 1;
	    //! assert(v a0' * pow2 1 = t0);
	    a0', bx'
	end else begin
	    //! assert(v a0 * pow2 0 = t0);
	    a0, bx
	end in
    //! assert(v a0 * pow2 (I32.v bx - I32.v b.mpfr_exp) = t0);
    lemma_pow2_mod_mod_zero (v c0) (U32.v sh) (U32.v d);
    lemma_pow2_div_mul (v c0) (U32.v d) (U32.v d);
    //! assert(v c0 / pow2 (U32.v d) * pow2 (U32.v d) = v c0);
    lemma_distr_add_left (v b0) (v c0 / pow2 (U32.v d)) (pow2 (U32.v d));
    //! assert(t0 * pow2 (U32.v d) = r.limb);
    lemma_paren_mul_right (v a0) (pow2 (I32.v bx - I32.v b.mpfr_exp)) (pow2 (U32.v d));
    lemma_pow2_mul (I32.v bx - I32.v b.mpfr_exp) (U32.v d);
    //! assert(v a0 * pow2 (I32.v bx - I32.v b.mpfr_exp + U32.v d) = r.limb);
    lemma_pow2_mul_range (v a0) (I32.v bx - I32.v b.mpfr_exp + U32.v d) 64;
    lemma_bit_length r.limb r.len (I32.v bx - I32.v b.mpfr_exp + U32.v d + 64);
    //! assert(I32.v bx = r.len + I32.v b.mpfr_exp - U32.v d - 64);
    ()
    
val mpfr_add1sp1_gt_branch1_value_lemma:
    h:mem -> a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
    sh:mpfr_reg_prec_t -> d:u32 -> mask:mp_limb_t -> Lemma
    (requires (mpfr_add1sp1_gt_branch1_pre_cond a b c sh d mask h))
    (ensures  (
    let p = 64 - U32.v sh in
    let r = add1sp_exact (as_reg_fp_ h b) (as_reg_fp_ h c) in
    let r = high_mant r p in
    let bp = b.mpfr_d in
    let cp = c.mpfr_d in
    let bx = b.mpfr_exp in
    let b0 = Seq.index (as_seq h bp) 0 in
    let c0 = Seq.index (as_seq h cp) 0 in
    let a0 = b0 +%^ (c0 >>^ d) in
    let a0, bx = if a0 <^ b0 then mpfr_LIMB_HIGHBIT |^ (a0 >>^ 1ul), I32.(bx +^ 1l) else a0, bx in
    let a0 = a0 &^ (lognot mask) in
    v a0 * pow2 (r.len - 64) = r.limb /\ I32.v bx = r.exp /\
    v a0 >= pow2 63 /\ v a0 % pow2 (64 - p) = 0))

let mpfr_add1sp1_gt_branch1_value_lemma h a b c sh d mask =
    let p = 64 - U32.v sh in
    let r = add1sp_exact (as_reg_fp_ h b) (as_reg_fp_ h c) in
    let bp = b.mpfr_d in
    let cp = c.mpfr_d in
    let bx = b.mpfr_exp in
    let b0 = Seq.index (as_seq h bp) 0 in
    let c0 = Seq.index (as_seq h cp) 0 in
    let a0 = b0 +%^ (c0 >>^ d) in
    let t0 = v b0 + v c0 / pow2 (U32.v d) in
    let a0, bx = if a0 <^ b0 then mpfr_LIMB_HIGHBIT |^ (a0 >>^ 1ul), I32.(bx +^ 1l) else a0, bx in
    mpfr_add1sp1_gt_branch1_a0_bx_lemma h a b c sh d mask;
    lemma_pow2_mul_div (v a0) (r.len - 64) (r.len - p);
    //! assert(v a0 / pow2 (64 - p) = r.limb / pow2 (r.len - p));
    UInt.nth_lemma #64 (UInt.shift_right #64 (v a0) (64 - p)) (UInt.shift_right #64 (UInt.logand (v a0) (UInt.lognot (v mask))) (64 - p));
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

val mpfr_add1sp1_gt_branch1_rb_lemma:
    h:mem -> a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
    sh:mpfr_reg_prec_t -> d:u32 -> mask:mp_limb_t -> Lemma
    (requires (mpfr_add1sp1_gt_branch1_pre_cond a b c sh d mask h))
    (ensures  (
    let p = U32.v a.mpfr_prec in
    let r = add1sp_exact (as_reg_fp_ h b) (as_reg_fp_ h c) in
    let bp = b.mpfr_d in
    let cp = c.mpfr_d in
    let bx = b.mpfr_exp in
    let b0 = Seq.index (as_seq h bp) 0 in
    let c0 = Seq.index (as_seq h cp) 0 in
    let a0 = b0 +%^ (c0 >>^ d) in
    let a0, bx = if a0 <^ b0 then mpfr_LIMB_HIGHBIT |^ (a0 >>^ 1ul), I32.(bx +^ 1l) else a0, bx in
    let rb = a0 &^ (mpfr_LIMB_ONE <<^ U32.(sh -^ 1ul)) in
    v rb <> 0 <==> rb_def r p))

let mpfr_add1sp1_gt_branch1_rb_lemma h a b c sh d mask = 
    let p = U32.v a.mpfr_prec in
    let r = add1sp_exact (as_reg_fp_ h b) (as_reg_fp_ h c) in
    let bp = b.mpfr_d in
    let cp = c.mpfr_d in
    let bx = b.mpfr_exp in
    let b0 = Seq.index (as_seq h bp) 0 in
    let c0 = Seq.index (as_seq h cp) 0 in
    let a0 = b0 +%^ (c0 >>^ d) in
    let a0, bx = if a0 <^ b0 then mpfr_LIMB_HIGHBIT |^ (a0 >>^ 1ul), I32.(bx +^ 1l) else a0, bx in
    mpfr_add1sp1_gt_branch1_a0_bx_lemma h a b c sh d mask;
    //! assert(v a0 * pow2 (r.len - 64) = r.limb);
    lemma_multiple_div (v a0) (pow2 (r.len - 64));
    UInt.slice_left_lemma (UInt.to_vec #r.len r.limb) 64;
    //! assert(UInt.nth (v a0) p = UInt.nth #r.len r.limb p);
    let rb = a0 &^ (mpfr_LIMB_ONE <<^ U32.(sh -^ 1ul)) in
    lemma_pow2_small_mod (U32.v sh - 1) 64;
    //! assert(v (mpfr_LIMB_ONE <<^ U32.(sh -^ 1ul)) = pow2 (U32.v sh - 1));
    lemma_bit_mask_value a0 (mpfr_LIMB_ONE <<^ U32.(sh -^ 1ul)) p;
    if rb_def r p then assert(v rb <> 0) else assert(v rb = 0)
    
val mpfr_add1sp1_gt_branch1_sb_lemma:
    h:mem -> a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
    sh:mpfr_reg_prec_t -> d:u32 -> mask:mp_limb_t -> Lemma
    (requires (mpfr_add1sp1_gt_branch1_pre_cond a b c sh d mask h))
    (ensures  (
    let p = U32.v a.mpfr_prec in
    let r = add1sp_exact (as_reg_fp_ h b) (as_reg_fp_ h c) in
    let bp = b.mpfr_d in
    let cp = c.mpfr_d in
    let bx = b.mpfr_exp in
    let b0 = Seq.index (as_seq h bp) 0 in
    let c0 = Seq.index (as_seq h cp) 0 in
    let a0 = b0 +%^ (c0 >>^ d) in
    let a0, bx = if a0 <^ b0 then mpfr_LIMB_HIGHBIT |^ (a0 >>^ 1ul), I32.(bx +^ 1l) else a0, bx in
    let rb = a0 &^ (mpfr_LIMB_ONE <<^ U32.(sh -^ 1ul)) in
    let sb = (a0 &^ mask) ^^ rb in
    v sb <> 0 <==> sb_def r p))

let mpfr_add1sp1_gt_branch1_sb_lemma h a b c sh d mask =
    let p = U32.v a.mpfr_prec in
    let r = add1sp_exact (as_reg_fp_ h b) (as_reg_fp_ h c) in
    let bp = b.mpfr_d in
    let cp = c.mpfr_d in
    let bx = b.mpfr_exp in
    let b0 = Seq.index (as_seq h bp) 0 in
    let c0 = Seq.index (as_seq h cp) 0 in
    let a0 = b0 +%^ (c0 >>^ d) in
    let a0, bx = if a0 <^ b0 then mpfr_LIMB_HIGHBIT |^ (a0 >>^ 1ul), I32.(bx +^ 1l) else a0, bx in
    let rb = a0 &^ (mpfr_LIMB_ONE <<^ U32.(sh -^ 1ul)) in
    let sb = (a0 &^ mask) ^^ rb in
    lemma_pow2_small_mod (U32.v sh - 1) 64;
    //! assert(v (mpfr_LIMB_ONE <<^ U32.(sh -^ 1ul)) = pow2 (U32.v sh - 1));
    lemma_bit_mask (mpfr_LIMB_ONE <<^ U32.(sh -^ 1ul)) (64 - U32.v sh);
    lemma_tail_mask mask (U32.v sh);
    let rmask = mpfr_LIMB_MASK U32.(sh -^ 1ul) in
    UInt.nth_lemma #64 (v (mask ^^ (mpfr_LIMB_ONE <<^ U32.(sh -^ 1ul)))) (v rmask);
    lemma_xor_and_distr a0 mask (mpfr_LIMB_ONE <<^ U32.(sh -^ 1ul));
    //! assert(sb = (a0 &^ rmask));
    lemma_tail_mask_value a0 rmask (U32.v sh - 1);
    //! assert(v sb = (v a0) % pow2 (U32.v sh - 1));
    lemma_mod_mul (v a0) (pow2 (U32.v sh - 1)) (pow2 (r.len - 64));
    lemma_pow2_mul (U32.v sh - 1) (r.len - 64);
    //! assert(v sb * pow2 (r.len - 64) = (v a0 * pow2 (r.len - 64)) % pow2 (r.len - p - 1));
    mpfr_add1sp1_gt_branch1_a0_bx_lemma h a b c sh d mask;
    //! assert(v sb * pow2 (r.len - 64) = r.limb % pow2 (r.len - p - 1));
    lemma_mul_zero (v sb) (pow2 (r.len - 64))

unfold val mpfr_add1sp1_gt_branch1:
    a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
    sh:mpfr_reg_prec_t -> d:u32 -> mask:mp_limb_t -> Stack state
    (requires (fun h -> mpfr_add1sp1_gt_branch1_pre_cond a b c sh d mask h))
    (ensures  (fun h0 s h1 -> mpfr_add1sp1_any_post_cond a b c h0 s h1))

let mpfr_add1sp1_gt_branch1 a b c sh d mask =
    let h = ST.get() in
    let ap = a.mpfr_d in
    let bp = b.mpfr_d in
    let cp = c.mpfr_d in
    let bx = b.mpfr_exp in
    let a0 = bp.(0ul) +%^ (cp.(0ul) >>^ d) in
    let a0, bx = if a0 <^ bp.(0ul) then mpfr_LIMB_HIGHBIT |^ (a0 >>^ 1ul), I32.(bx +^ 1l)
	         else a0, bx in
    let rb = a0 &^ (mpfr_LIMB_ONE <<^ U32.(sh -^ 1ul)) in
    let sb = (a0 &^ mask) ^^ rb in
    ap.(0ul) <- a0 &^ (lognot mask);
    mpfr_add1sp1_gt_branch1_value_lemma h a b c sh d mask;
    mpfr_add1sp1_gt_branch1_rb_lemma h a b c sh d mask;
    mpfr_add1sp1_gt_branch1_sb_lemma h a b c sh d mask;
    mk_state sh bx rb sb

(* lemmas and implementation for mpfr_add1sp1_gt_branch1 where sh <= d < 64 *)
let mpfr_add1sp1_gt_branch2_pre_cond a b c sh d mask h =
    mpfr_add1sp1_gt_pre_cond a b c sh h /\
    U32.v d = I32.v b.mpfr_exp - I32.v c.mpfr_exp /\
    v mask = pow2 (U32.v sh) - 1 /\
    U32.v d >= U32.v sh /\ U32.v d < U32.v gmp_NUMB_BITS

unfold val mpfr_add1sp1_gt_branch2:
    a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
    sh:mpfr_reg_prec_t -> d:u32 -> mask:mp_limb_t -> Stack state
    (requires (fun h -> mpfr_add1sp1_gt_branch2_pre_cond a b c sh d mask h))
    (ensures  (fun h0 s h1 -> mpfr_add1sp1_any_post_cond a b c h0 s h1))

let mpfr_add1sp1_gt_branch2 a b c sh d mask =
    let ap = a.mpfr_d in
    let bp = b.mpfr_d in
    let cp = c.mpfr_d in
    let bx = b.mpfr_exp in
    let sb = cp.(0ul) <<^ U32.(gmp_NUMB_BITS -^ d) in
    let a0 = bp.(0ul) +%^ (cp.(0ul) >>^ d) in
    let sb, a0, bx =
        if a0 <^ bp.(0ul) then
	    sb |^ (a0 &^ 1uL), mpfr_LIMB_HIGHBIT |^ (a0 >>^ 1ul), I32.(bx +^ 1l)
	else sb, a0, bx in
    let rb = a0 &^ (mpfr_LIMB_ONE <<^ U32.(sh -^ 1ul)) in
    let sb = sb |^ ((a0 &^ mask) ^^ rb) in
    ap.(0ul) <- a0 &^ (lognot mask);
    admit();
    mk_state sh bx rb sb

(* lemmas and implementation for mpfr_add1sp1_gt_branch1 where d >= 64 *)
let mpfr_add1sp1_gt_branch3_pre_cond a b c sh h =
    mpfr_add1sp1_gt_pre_cond a b c sh h /\
    I32.v b.mpfr_exp - I32.v c.mpfr_exp >= U32.v gmp_NUMB_BITS
    
unfold val mpfr_add1sp1_gt_branch3:
    a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
    sh:mpfr_reg_prec_t -> Stack state
    (requires (fun h -> mpfr_add1sp1_gt_branch3_pre_cond a b c sh h))
    (ensures  (fun h0 s h1 -> mpfr_add1sp1_any_post_cond a b c h0 s h1))

let mpfr_add1sp1_gt_branch3 a b _ sh =
    let ap = a.mpfr_d in
    let bp = a.mpfr_d in
    let bx = b.mpfr_exp in
    ap.(0ul) <- bp.(0ul);
    let rb = 0uL in
    let sb = 1uL in
    admit();
    mk_state sh bx rb sb

unfold val mpfr_add1sp1_gt:
    a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
    p:mpfr_reg_prec_t -> sh:mpfr_reg_prec_t -> Stack state
    (requires (fun h -> mpfr_add1sp1_gt_pre_cond a b c sh h))
    (ensures  (fun h0 s h1 -> mpfr_add1sp1_any_post_cond a b c h0 s h1 /\
                           mpfr_add1sp1_any_post_cond a c b h0 s h1))

let mpfr_add1sp1_gt a b c p sh =
    let h0 = ST.get() in
    let bx = b.mpfr_exp in
    let cx = c.mpfr_exp in
    let d = int32_to_uint32 I32.(bx -^ cx) in
    let mask = mpfr_LIMB_MASK sh in
    let s = (
    if U32.(d <^ sh) then mpfr_add1sp1_gt_branch1 a b c sh d mask
    else if U32.(d <^ gmp_NUMB_BITS) then mpfr_add1sp1_gt_branch2 a b c sh d mask
    else mpfr_add1sp1_gt_branch3 a b c sh) in
    let h1 = ST.get() in
    mpfr_add1sp1_any_post_cond_comm_lemma a b c h0 s h1;
    s

(* pre-condition for mpfr_add1sp1_eq where b.exp = c.exp *)
let mpfr_add1sp1_eq_pre_cond a b c sh h =
    I32.v b.mpfr_exp = I32.v c.mpfr_exp /\
    U32.v sh = U32.v gmp_NUMB_BITS - U32.v a.mpfr_prec /\
    mpfr_add1sp1_any_pre_cond a b c U32.(gmp_NUMB_BITS -^ sh) h
    
unfold val mpfr_add1sp1_eq:
    a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
    p:mpfr_reg_prec_t -> sh:mpfr_reg_prec_t -> Stack state
    (requires (fun h -> mpfr_add1sp1_eq_pre_cond a b c sh h))
    (ensures  (fun h0 s h1 -> mpfr_add1sp1_any_post_cond a b c h0 s h1))

let mpfr_add1sp1_eq a b c p sh =
   let ap = a.mpfr_d in
   let bp = b.mpfr_d in
   let cp = c.mpfr_d in
   let a0 = (bp.(0ul) >>^ 1ul) +^ (cp.(0ul) >>^ 1ul) in
   let bx = I32.(b.mpfr_exp +^ 1l) in
   let rb = a0 &^ (mpfr_LIMB_ONE <<^ U32.(sh -^ 1ul)) in
   ap.(0ul) <- a0 ^^ rb;
   let sb = 0uL in
   admit();
   mk_state sh bx rb sb

unfold val mpfr_add1sp1_any:
    a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
    p:mpfr_reg_prec_t -> Stack state
    (requires (fun h -> mpfr_add1sp1_any_pre_cond a b c p h))
    (ensures  (fun h0 s h1 -> mpfr_add1sp1_any_post_cond a b c h0 s h1))

let mpfr_add1sp1_any a b c p =
    let bx = b.mpfr_exp in
    let cx = c.mpfr_exp in
    let sh = U32.(gmp_NUMB_BITS -^ p) in
    if I32.(bx =^ cx) then mpfr_add1sp1_eq a b c p sh
    else if I32.(bx >^ cx) then mpfr_add1sp1_gt a b c p sh
    else mpfr_add1sp1_gt a c b p sh

(* rounding specifications *)
unfold val mpfr_truncate: a:mpfr_ptr -> Stack i32
    (requires (fun h -> mpfr_live h a /\ length (as_struct h a).mpfr_d = 1))
    (ensures  (fun h0 f h1 -> h0 == h1 /\ f = mpfr_NEG_SIGN (as_struct h1 a).mpfr_sign))

let mpfr_truncate a = mpfr_NEG_SIGN (mpfr_SIGN(a))

unfold val mpfr_add_one_ulp: a:mpfr_ptr -> rnd_mode:mpfr_rnd_t ->
                        sh:mpfr_reg_prec_t -> bx:mpfr_tmp_exp_t -> Stack i32
    (requires (fun h -> mpfr_live h a /\ length (as_struct h a).mpfr_d = 1 /\ normal_cond h a /\
		     U32.v sh = U32.v gmp_NUMB_BITS - U32.v (as_struct h a).mpfr_prec /\
		     I32.v bx = I32.v (as_struct h a).mpfr_exp))
    (ensures  (fun h0 f h1 -> mpfr_live h1 a /\ mpfr_modifies a h0 h1 /\ mpfr_valid_cond h1 a /\
                           normal_to_mpfr_cond (add_one_ulp (as_normal h0 a)) (as_fp h1 a) /\
                           f = (as_struct h1 a).mpfr_sign))

let mpfr_add_one_ulp a rnd_mode sh bx =
    admit();
    let h0 = ST.get() in
    let ap = mpfr_MANT a in
    ap.(0ul) <- ap.(0ul) +%^ (mpfr_LIMB_ONE <<^ sh);
    if ap.(0ul) =^ 0uL then begin
        ap.(0ul) <- mpfr_LIMB_HIGHBIT;
	if I32.(bx +^ 1l <=^ mpfr_EMAX) then begin
	    mpfr_SET_EXP a I32.(bx +^ 1l);
	    mpfr_SIGN a
	end else mpfr_overflow a rnd_mode (mpfr_SIGN a)
    end else begin
        let h1 = ST.get() in
	lemma_reveal_modifies_1 ap h0 h1;
	lemma_intro_modifies_2 a ap h0 h1;
        mpfr_SIGN a
    end
(*
let mpfr_add1sp1_round_pre_cond exact a st h =
    let p = U32.v (as_struct h a).mpfr_prec in
    mpfr_live h a /\ length (as_struct h a).mpfr_d = 1 /\ mpfr_valid_cond h a /\
    p < 64 /\ exact.len > 64 /\ exact.prec > p /\
    as_val h (as_struct h a).mpfr_d * pow2 (exact.len - 64) = (high_mant exact p).limb /\
    U32.v st.sh = U32.v gmp_NUMB_BITS - p /\
    I32.v st.bx = exact.exp /\
    (v st.rb <> 0 <==> rb_def exact p) /\
    (v st.sb <> 0 <==> sb_def exact p)

let mpfr_add1sp1_round_post_cond exact a b c rnd_mode p h0 f h1 =
    (* Memory safety *)
    mpfr_live h1 a /\ mpfr_live h1 b /\ mpfr_live h1 c /\
    mpfr_disjoint_or_equal h1 a b /\ mpfr_disjoint_or_equal h1 a c /\
    mpfr_disjoint_or_equal h1 b c /\ mpfr_modifies a h0 h1 /\
    (* Functional correctness *)
    mpfr_valid_cond h1 a /\ 
    mpfr_round_cond exact (U32.v p) rnd_mode (as_fp h1 a) /\
    mpfr_ternary_cond (I32.v f) exact (as_fp h1 a)
*)

unfold val mpfr_add1sp1_round: a:mpfr_ptr -> rnd_mode:mpfr_rnd_t -> st:state -> Stack i32
    (requires (fun h -> mpfr_live h a /\ length (as_struct h a).mpfr_d = 1 /\ normal_cond h a))
    (ensures  (fun h0 f h1 -> 
    mpfr_live h1 a /\ mpfr_modifies a h0 h1 /\ mpfr_valid_cond h1 a /\
    (let high = {as_normal h0 a with exp = I32.v st.bx} in
    normal_to_mpfr_cond (round_rb_sb_spec high (st.rb <> 0uL) (st.sb <> 0uL) rnd_mode) (as_fp h1 a) /\
    mpfr_ternary_cond (I32.v f) (round_rb_sb_spec high (st.rb <> 0uL) (st.sb <> 0uL) rnd_mode) (as_fp h1 a))))

let mpfr_add1sp1_round a rnd_mode st =
    admit();
    let ap = mpfr_MANT a in
    let a0 = ap.(0ul) in
    let h0 = ST.get() in
    mpfr_SET_EXP a st.bx; // Maybe set it later in truncate and add_one_ulp?
    let h1 = ST.get() in
    lemma_reveal_modifies_1 a h0 h1;
    lemma_intro_modifies_2 a ap h0 h1;
    if (st.rb =^ 0uL && st.sb =^ 0uL) then 0l
    else if (MPFR_RNDN? rnd_mode) then begin
        if (st.rb =^ 0uL || (st.sb =^ 0uL && ((a0 &^ (mpfr_LIMB_ONE <<^ st.sh)) =^ 0uL))) then
	    mpfr_truncate a
	else mpfr_add_one_ulp a rnd_mode st.sh st.bx
    end else if mpfr_IS_LIKE_RNDZ rnd_mode (mpfr_SIGN a = mpfr_SIGN_NEG) then mpfr_truncate a
    else mpfr_add_one_ulp a rnd_mode st.sh st.bx


let mpfr_add1sp1 a b c rnd_mode p =
    let h0 = ST.get() in
    let st = mpfr_add1sp1_any a.(0ul) b.(0ul) c.(0ul) p in
    let h1 = ST.get() in
    lemma_reveal_modifies_1 (mpfr_MANT a) h0 h1;
    lemma_intro_modifies_2 a (mpfr_MANT a) h0 h1;
    //round_rb_sb_lemma (add1sp_exact (as_reg_fp h0 b) (as_reg_fp h0 c)) (U32.v (as_struct h0 a).mpfr_prec) (as_normal_ h1 ({as_struct h1 a with mpfr_exp = st.bx})) (st.rb <> 0uL) (st.sb <> 0uL) rnd_mode;
    if I32.(st.bx >^ mpfr_EMAX) then begin
        admit();
        mpfr_overflow a rnd_mode (mpfr_SIGN a)
    end else begin
        let ret = mpfr_add1sp1_round a rnd_mode st in
	let h2 = ST.get() in
	mpfr_ternary_cond_lemma (add1sp_exact (as_reg_fp h0 b) (as_reg_fp h0 c)) (U32.v (as_struct h0 a).mpfr_prec) (as_normal_ h1 ({as_struct h1 a with mpfr_exp = st.bx})) (st.rb <> 0uL) (st.sb <> 0uL) rnd_mode (I32.v ret) (as_fp h2 a);
	ret
    end
