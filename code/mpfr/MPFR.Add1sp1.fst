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
open MPFR.Maths

module I64 = FStar.Int64
module I32 = FStar.Int32
module U32 = FStar.UInt32
module Spec = MPFR.Add1.Spec
module RND  = MPFR.Round.Spec

#set-options "--z3refresh --z3rlimit 60 --max_fuel 1 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 0"

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

(* lemmas and implementation for mpfr_add1sp1_gt_branch1 where
 * b.exp > c.exp && d < sh *)
let mpfr_add1sp1_gt_branch1_precond h a b c sh d mask =
    mpfr_reg_struct_cond h b /\ mpfr_reg_struct_cond h c /\
    U32.v a.mpfr_prec < U32.v gmp_NUMB_BITS - 1 /\
    U32.v a.mpfr_prec = U32.v b.mpfr_prec /\
    U32.v a.mpfr_prec = U32.v c.mpfr_prec /\
    U32.v sh = U32.v gmp_NUMB_BITS - U32.v a.mpfr_prec /\
    I32.v b.mpfr_exp > I32.v c.mpfr_exp /\
    U32.v d = I32.v b.mpfr_exp - I32.v c.mpfr_exp /\
    U32.v d < U32.v sh /\ v mask = pow2 (U32.v sh) - 1 /\
    (let am = a.mpfr_d in
    let bm = b.mpfr_d in
    let cm = c.mpfr_d in
    live h am /\ live h bm /\ live h cm /\
    length am = 1 /\ length bm = 1 /\ length cm = 1)
    
val mpfr_add1sp1_gt_branch1_a0_bx_lemma:
    h0:mem -> h1:mem ->
    a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
    sh:mpfr_reg_prec_t -> d:u32 -> mask:mp_limb_t -> Lemma
    (requires (mpfr_add1sp1_gt_branch1_precond h0 a b c sh d mask))
    (ensures  (
    let r = Spec.add_sp (as_reg_fp_ h0 b) (as_reg_fp_ h0 c) in
    let bp = b.mpfr_d in
    let cp = c.mpfr_d in
    let bx = b.mpfr_exp in
    let b0 = Seq.index (as_seq h0 bp) 0 in
    let c0 = Seq.index (as_seq h0 cp) 0 in
    let a0 = b0 +%^ (c0 >>^ d) in
    let a0, bx = if a0 <^ b0 then mpfr_LIMB_HIGHBIT |^ (a0 >>^ 1ul), I32.(bx +^ 1l) else a0, bx in
    v a0 * pow2 (I32.v bx - I32.v b.mpfr_exp + U32.v d) = r.limb /\
    I32.v bx = r.len + I32.v b.mpfr_exp - U32.v d - 64))

let mpfr_add1sp1_gt_branch1_a0_bx_lemma h0 h1 a b c sh d mask =
    let r = Spec.add_sp (as_reg_fp_ h0 b) (as_reg_fp_ h0 c) in
    let bp = b.mpfr_d in
    let cp = c.mpfr_d in
    let bx = b.mpfr_exp in
    let b0 = Seq.index (as_seq h0 bp) 0 in
    let c0 = Seq.index (as_seq h0 cp) 0 in
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
    h0:mem -> h1:mem ->
    a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
    sh:mpfr_reg_prec_t -> d:u32 -> mask:mp_limb_t -> Lemma
    (requires (mpfr_add1sp1_gt_branch1_precond h0 a b c sh d mask))
    (ensures  (
    let p = 64 - U32.v sh in
    let r = Spec.add_sp (as_reg_fp_ h0 b) (as_reg_fp_ h0 c) in
    let r = RND.high_mant r p in
    let bp = b.mpfr_d in
    let cp = c.mpfr_d in
    let bx = b.mpfr_exp in
    let b0 = Seq.index (as_seq h0 bp) 0 in
    let c0 = Seq.index (as_seq h0 cp) 0 in
    let a0 = b0 +%^ (c0 >>^ d) in
    let a0, bx = if a0 <^ b0 then mpfr_LIMB_HIGHBIT |^ (a0 >>^ 1ul), I32.(bx +^ 1l) else a0, bx in
    let a0 = a0 &^ (lognot mask) in
    v a0 * pow2 (I32.v bx - I32.v b.mpfr_exp + U32.v d) = r.limb /\
    I32.v bx = r.len + I32.v b.mpfr_exp - U32.v d - 64))

let mpfr_add1sp1_gt_branch1_value_lemma h0 h1 a b c sh d mask =
    let p = 64 - U32.v sh in
    let r = Spec.add_sp (as_reg_fp_ h0 b) (as_reg_fp_ h0 c) in
    let bp = b.mpfr_d in
    let cp = c.mpfr_d in
    let bx = b.mpfr_exp in
    let b0 = Seq.index (as_seq h0 bp) 0 in
    let c0 = Seq.index (as_seq h0 cp) 0 in
    let a0 = b0 +%^ (c0 >>^ d) in
    let t0 = v b0 + v c0 / pow2 (U32.v d) in
    let a0, bx = if a0 <^ b0 then mpfr_LIMB_HIGHBIT |^ (a0 >>^ 1ul), I32.(bx +^ 1l) else a0, bx in
    mpfr_add1sp1_gt_branch1_a0_bx_lemma h0 h1 a b c sh d mask;
    lemma_pow2_mul_div (v a0) (I32.v bx - I32.v b.mpfr_exp + U32.v d) (r.len - p);
    //! assert(v a0 / pow2 (64 - p) = r.limb / pow2 (r.len - p));
    UInt.nth_lemma #64 (UInt.shift_right #64 (v a0) (64 - p)) (UInt.shift_right #64 (UInt.logand (v a0) (UInt.lognot (v mask))) (64 - p));
    assert(v (a0 &^ lognot mask) / pow2 (64 - p) = r.limb / pow2 (r.len - p));
    lemma_lognot_mask_mod a0 mask (64 - p);
    //! assert(v (a0 &^ lognot mask) % pow2 (64 - p) = 0);
    let a0 = a0 &^ (lognot mask) in
    lemma_pow2_div_mul (v a0) (64 - p) (r.len - p);
    //! assert((v a0 / pow2 (64 - p)) * pow2 (r.len - p) = r.limb / pow2 (r.len - p) * pow2 (r.len - p));
    ()

val mpfr_add1sp1_gt_branch1_rb_lemma:
    h0:mem -> h1:mem ->
    a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
    sh:mpfr_reg_prec_t -> d:u32 -> mask:mp_limb_t -> Lemma
    (requires (mpfr_reg_struct_cond h0 b /\ mpfr_reg_struct_cond h0 c /\
               U32.v a.mpfr_prec < U32.v gmp_NUMB_BITS - 1 /\
               U32.v a.mpfr_prec = U32.v b.mpfr_prec /\
               U32.v a.mpfr_prec = U32.v c.mpfr_prec /\
               U32.v sh = U32.v gmp_NUMB_BITS - U32.v a.mpfr_prec /\
               U32.v d < U32.v sh /\ v mask = pow2 (U32.v sh) - 1 /\
               I32.v b.mpfr_exp > I32.v c.mpfr_exp /\
               (let am = a.mpfr_d in
               let bm = b.mpfr_d in
               let cm = c.mpfr_d in
               live h0 am /\ live h0 bm /\ live h0 cm /\
	       length am = 1 /\ length bm = 1 /\ length cm = 1)))
    (ensures  (let p = U32.v a.mpfr_prec in
               let bp = b.mpfr_d in
               let cp = c.mpfr_d in
	       let bx = b.mpfr_exp in
	       let b0 = Seq.index (as_seq h0 bp) 0 in
	       let c0 = Seq.index (as_seq h0 cp) 0 in
	       let a0 = b0 +%^ (c0 >>^ d) in
	       let a0, bx = if a0 <^ b0 then mpfr_LIMB_HIGHBIT |^ (a0 >>^ 1ul), I32.(bx +^ 1l) else a0, bx in
	       let rb = a0 &^ (mpfr_LIMB_ONE <<^ U32.(sh -^ 1ul)) in
	       let res = Spec.add_sp (as_reg_fp_ h0 b) (as_reg_fp_ h0 c) in
	       v rb <> 0 <==> RND.rb_def res p))

let mpfr_add1sp1_gt_branch1_rb_lemma h0 h1 a b c sh d mask = admit()

val mpfr_add1sp1_gt_branch1_sb_lemma:
    h0:mem -> h1:mem ->
    a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
    sh:mpfr_reg_prec_t -> d:u32 -> mask:mp_limb_t -> Lemma
    (requires (mpfr_reg_struct_cond h0 b /\ mpfr_reg_struct_cond h0 c /\
               U32.v a.mpfr_prec < U32.v gmp_NUMB_BITS - 1 /\
               U32.v a.mpfr_prec = U32.v b.mpfr_prec /\
               U32.v a.mpfr_prec = U32.v c.mpfr_prec /\
               U32.v sh = U32.v gmp_NUMB_BITS - U32.v a.mpfr_prec /\
               U32.v d < U32.v sh /\ v mask = pow2 (U32.v sh) - 1 /\
               I32.v b.mpfr_exp > I32.v c.mpfr_exp /\
               (let am = a.mpfr_d in
               let bm = b.mpfr_d in
               let cm = c.mpfr_d in
               live h0 am /\ live h0 bm /\ live h0 cm /\
	       length am = 1 /\ length bm = 1 /\ length cm = 1)))
    (ensures  (let p = U32.v a.mpfr_prec in
               let bp = b.mpfr_d in
               let cp = c.mpfr_d in
	       let bx = b.mpfr_exp in
	       let b0 = Seq.index (as_seq h0 bp) 0 in
	       let c0 = Seq.index (as_seq h0 cp) 0 in
	       let a0 = b0 +%^ (c0 >>^ d) in
	       let a0, bx = if a0 <^ b0 then mpfr_LIMB_HIGHBIT |^ (a0 >>^ 1ul), I32.(bx +^ 1l) else a0, bx in
	       let rb = a0 &^ (mpfr_LIMB_ONE <<^ U32.(sh -^ 1ul)) in
	       let sb = (a0 &^ mask) ^^ rb in
	       let res = Spec.add_sp (as_reg_fp_ h0 b) (as_reg_fp_ h0 c) in
	       v sb <> 0 <==> RND.sb_def res p))

let mpfr_add1sp1_gt_branch1_sb_lemma h0 h1 a b c sh d mask = admit()

unfold val mpfr_add1sp1_gt_branch1:
    a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
    sh:mpfr_reg_prec_t -> d:u32 -> mask:mp_limb_t -> Stack state
    (requires (fun h -> mpfr_add1sp1_gt_branch1_precond h a b c sh d mask))
    (ensures  (fun h0 s h1 ->
    let p = U32.v a.mpfr_prec in
    U32.v s.sh = U32.v gmp_NUMB_BITS - p /\
    (let am = a.mpfr_d in
    let bm = b.mpfr_d in
    let cm = c.mpfr_d in
    live h1 am /\ live h1 bm /\ live h1 cm /\
    modifies_1 am h0 h1 /\
    (let r = Spec.add_sp (as_reg_fp_ h0 b) (as_reg_fp_ h0 c) in
    I32.v s.bx >= I32.v b.mpfr_exp /\ I32.v s.bx <= I32.v b.mpfr_exp + 1 /\
    v (Seq.index (as_seq h1 am) 0) * pow2 (I32.v s.bx - I32.v b.mpfr_exp + U32.v d) = (RND.high_mant r p).limb /\
    (v s.rb <> 0 <==> RND.rb_def r p) /\
    (v s.sb <> 0 <==> RND.sb_def r p)))))

let mpfr_add1sp1_gt_branch1 a b c sh d mask =
    let h0 = ST.get() in
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
    let h1 = ST.get() in
    mpfr_add1sp1_gt_branch1_value_lemma h0 h1 a b c sh d mask;
    mpfr_add1sp1_gt_branch1_rb_lemma h0 h1 a b c sh d mask;
    mpfr_add1sp1_gt_branch1_sb_lemma h0 h1 a b c sh d mask;
    mk_state sh bx rb sb

unfold val mpfr_add1sp1_gt_branch2:
    a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
    sh:mpfr_reg_prec_t -> d:u32 -> mask:mp_limb_t -> Stack state
    (requires (fun h -> mpfr_reg_struct_cond h b /\ mpfr_reg_struct_cond h c /\
                     U32.v a.mpfr_prec < U32.v gmp_NUMB_BITS - 1 /\
		     U32.v a.mpfr_prec = U32.v b.mpfr_prec /\
		     U32.v a.mpfr_prec = U32.v c.mpfr_prec /\
		     U32.v sh = U32.v gmp_NUMB_BITS - U32.v a.mpfr_prec /\
		     U32.v d >= U32.v sh /\ U32.v d < U32.v gmp_NUMB_BITS /\
		     v mask = pow2 (U32.v sh) - 1 /\
		     I32.v b.mpfr_exp > I32.v c.mpfr_exp /\
		     (let am = a.mpfr_d in
		     let bm = b.mpfr_d in
		     let cm = c.mpfr_d in
		     live h am /\ live h bm /\ live h cm /\
		     length am = 1 /\ length bm = 1 /\ length cm = 1)))
    (ensures  (fun h0 r h1 -> U32.v r.sh = U32.v gmp_NUMB_BITS - U32.v a.mpfr_prec /\
                           (let am = a.mpfr_d in
		           let bm = b.mpfr_d in
		           let cm = c.mpfr_d in
			   live h1 am /\ live h1 bm /\ live h1 cm /\
		           modifies_1 am h0 h1)))

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
    mk_state sh bx rb sb

(* TODO: remove abundent inputs *)
unfold val mpfr_add1sp1_gt_branch3:
    a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct -> sh:mpfr_reg_prec_t -> Stack state
    (requires (fun h -> mpfr_reg_struct_cond h b /\ mpfr_reg_struct_cond h c /\
                     U32.v a.mpfr_prec < U32.v gmp_NUMB_BITS - 1 /\
		     U32.v a.mpfr_prec = U32.v b.mpfr_prec /\
		     U32.v a.mpfr_prec = U32.v c.mpfr_prec /\
		     U32.v sh = U32.v gmp_NUMB_BITS - U32.v a.mpfr_prec /\
		     I32.v b.mpfr_exp - I32.v c.mpfr_exp >= U32.v gmp_NUMB_BITS /\
		     (let am = a.mpfr_d in
		     let bm = b.mpfr_d in
		     let cm = c.mpfr_d in
		     live h am /\ live h bm /\ live h cm /\
		     length am = 1 /\ length bm = 1 /\ length cm = 1)))
    (ensures  (fun h0 r h1 -> U32.v r.sh = U32.v gmp_NUMB_BITS - U32.v a.mpfr_prec /\
                           (let am = a.mpfr_d in
		           let bm = b.mpfr_d in
			   let cm = c.mpfr_d in
			   live h1 am /\ live h1 bm /\ live h1 cm /\
		           modifies_1 am h0 h1)))

let mpfr_add1sp1_gt_branch3 a b _ sh =
    let ap = a.mpfr_d in
    let bp = a.mpfr_d in
    let bx = b.mpfr_exp in
    ap.(0ul) <- bp.(0ul);
    let rb = 0uL in
    let sb = 1uL in
    mk_state sh bx rb sb

unfold val mpfr_add1sp1_gt: a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
                       p:mpfr_reg_prec_t -> sh:mpfr_reg_prec_t -> Stack state
    (requires (fun h -> mpfr_reg_struct_cond h b /\ mpfr_reg_struct_cond h c /\
		     U32.v p < U32.v gmp_NUMB_BITS - 1 /\
		     U32.v p = U32.v a.mpfr_prec /\
		     U32.v p = U32.v b.mpfr_prec /\ U32.v p = U32.v c.mpfr_prec /\
		     U32.v sh = U32.v gmp_NUMB_BITS - U32.v p /\
		     I32.v b.mpfr_exp > I32.v c.mpfr_exp /\
		     (let am = a.mpfr_d in
		     let bm = b.mpfr_d in
		     let cm = c.mpfr_d in
		     live h am /\ live h bm /\ live h cm /\
		     length am = 1 /\ length bm = 1 /\ length cm = 1)))
    (ensures  (fun h0 r h1 -> U32.v r.sh = U32.v gmp_NUMB_BITS - U32.v a.mpfr_prec /\
                           (let am = a.mpfr_d in
		           let bm = b.mpfr_d in
		           let cm = c.mpfr_d in
			   live h1 am /\ live h1 bm /\ live h1 cm /\
		           modifies_1 am h0 h1)))

let mpfr_add1sp1_gt a b c p sh =
    let bx = b.mpfr_exp in
    let cx = c.mpfr_exp in
    let d = int32_to_uint32 I32.(bx -^ cx) in
    let mask = mpfr_LIMB_MASK sh in
    if U32.(d <^ sh) then mpfr_add1sp1_gt_branch1 a b c sh d mask
    else if U32.(d <^ gmp_NUMB_BITS) then mpfr_add1sp1_gt_branch2 a b c sh d mask
    else mpfr_add1sp1_gt_branch3 a b c sh

unfold val mpfr_add1sp1_eq: a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
                       p:mpfr_reg_prec_t -> sh:mpfr_reg_prec_t -> Stack state
    (requires (fun h -> mpfr_reg_struct_cond h b /\ mpfr_reg_struct_cond h c /\
		     U32.v p < U32.v gmp_NUMB_BITS - 1 /\
		     U32.v p = U32.v a.mpfr_prec /\
		     U32.v p = U32.v b.mpfr_prec /\ U32.v p = U32.v c.mpfr_prec /\
		     U32.v sh = U32.v gmp_NUMB_BITS - U32.v p /\
		     I32.v b.mpfr_exp = I32.v c.mpfr_exp /\
		     (let am = a.mpfr_d in
		     let bm = b.mpfr_d in
		     let cm = c.mpfr_d in
		     live h am /\ live h bm /\ live h cm /\
		     length am = 1 /\ length bm = 1 /\ length cm = 1)))
    (ensures  (fun h0 r h1 -> U32.v r.sh = U32.v gmp_NUMB_BITS - U32.v a.mpfr_prec /\
                           (let am = a.mpfr_d in
		           let bm = b.mpfr_d in
		           let cm = c.mpfr_d in
			   live h1 am /\ live h1 bm /\ live h1 cm /\
		           modifies_1 am h0 h1)))

let mpfr_add1sp1_eq a b c p sh =
   let ap = a.mpfr_d in
   let bp = b.mpfr_d in
   let cp = c.mpfr_d in
   let a0 = (bp.(0ul) >>^ 1ul) +^ (cp.(0ul) >>^ 1ul) in
   let bx = I32.(b.mpfr_exp +^ 1l) in
   let rb = a0 &^ (mpfr_LIMB_ONE <<^ U32.(sh -^ 1ul)) in
   ap.(0ul) <- a0 ^^ rb;
   let sb = 0uL in
   mk_state sh bx rb sb

unfold val mpfr_add1sp1_any : a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
                       p:mpfr_reg_prec_t -> Stack state
    (requires (fun h -> mpfr_reg_struct_cond h b /\ mpfr_reg_struct_cond h c /\
		     U32.v p < U32.v gmp_NUMB_BITS - 1 /\
		     U32.v p = U32.v a.mpfr_prec /\
		     U32.v p = U32.v b.mpfr_prec /\ U32.v p = U32.v c.mpfr_prec /\
		     (let am = a.mpfr_d in
		     let bm = b.mpfr_d in
		     let cm = c.mpfr_d in
		     live h am /\ live h bm /\ live h cm /\
		     length am = 1 /\ length bm = 1 /\ length cm = 1)))
    (ensures  (fun h0 r h1 -> U32.v r.sh = U32.v gmp_NUMB_BITS - U32.v a.mpfr_prec /\
                           (let am = a.mpfr_d in
		           let bm = b.mpfr_d in
		           let cm = c.mpfr_d in
			   live h1 am /\ live h1 bm /\ live h1 cm /\
		           modifies_1 am h0 h1)))

let mpfr_add1sp1_any a b c p =
    let bx = b.mpfr_exp in
    let cx = c.mpfr_exp in
    let sh = U32.(gmp_NUMB_BITS -^ p) in
    if I32.(bx =^ cx) then mpfr_add1sp1_eq a b c p sh
    else if I32.(bx >^ cx) then mpfr_add1sp1_gt a b c p sh
    else mpfr_add1sp1_gt a c b p sh

unfold val truncate: a:mpfr_ptr -> Stack i32
    (requires (fun h -> live h a /\ length a = 1 /\
                     (let as = Seq.index (as_seq h a) 0 in
		     let am = as.mpfr_d in
		     live h am /\ disjoint a am /\ length am = 1)))
    (ensures  (fun h0 r h1 -> h0 == h1))

let truncate a = mpfr_NEG_SIGN (mpfr_SIGN(a))

unfold val add_one_ulp: a:mpfr_ptr -> rnd_mode:mpfr_rnd_t ->
                        sh:mpfr_reg_prec_t -> bx:mpfr_tmp_exp_t -> Stack i32
    (requires (fun h -> live h a /\ length a = 1 /\
                     (let as = Seq.index (as_seq h a) 0 in
		     U32.v sh = U32.v gmp_NUMB_BITS - U32.v as.mpfr_prec /\
		     I32.v bx = I32.v as.mpfr_exp /\
		     (let am = as.mpfr_d in
		     live h am /\ disjoint a am /\ length am = 1))))
    (ensures  (fun h0 r h1 -> live h1 a /\
                           (let as0 = Seq.index (as_seq h0 a) 0 in
			   let as = Seq.index (as_seq h1 a) 0 in
			   let am = as.mpfr_d in
			   live h1 am /\ am == as0.mpfr_d /\
			   modifies_2 a am h0 h1)))

let add_one_ulp a rnd_mode sh bx =
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

unfold val mpfr_add1sp1_round: a:mpfr_ptr -> rnd_mode:mpfr_rnd_t -> st:state -> Stack i32
    (requires (fun h -> live h a /\ length a = 1 /\
                     (let as = Seq.index (as_seq h a) 0 in
		     U32.v st.sh = U32.v gmp_NUMB_BITS - U32.v as.mpfr_prec /\
		     (let am = as.mpfr_d in
		     live h am /\ disjoint a am /\ length am = 1))))
    (ensures  (fun h0 r h1 -> live h1 a /\
                           (let as0 = Seq.index (as_seq h0 a) 0 in
			   let as = Seq.index (as_seq h1 a) 0 in
			   let am = as.mpfr_d in
			   live h1 am /\ am == as0.mpfr_d /\
			   modifies_2 a am h0 h1)))

let mpfr_add1sp1_round a rnd_mode st =
    let sh = st.sh in
    let bx = st.bx in
    let rb = st.rb in
    let sb = st.sb in
    let ap = mpfr_MANT a in
    let a0 = ap.(0ul) in
    let h0 = ST.get() in
    mpfr_SET_EXP a bx; // Maybe set it later in truncate and add_one_ulp?
    let h1 = ST.get() in
    lemma_reveal_modifies_1 a h0 h1;
    lemma_intro_modifies_2 a ap h0 h1;
    if ((rb =^ 0uL && sb =^ 0uL) || (MPFR_RNDF? rnd_mode)) then 0l
    else if (MPFR_RNDN? rnd_mode) then begin
        if (rb =^ 0uL || (sb =^ 0uL && ((a0 &^ (mpfr_LIMB_ONE <<^ sh)) =^ 0uL))) then
	    truncate a
	else add_one_ulp a rnd_mode sh bx
    end else if (mpfr_IS_LIKE_RNDZ rnd_mode I32.((mpfr_SIGN a) =^ -1l)) then truncate a
    else add_one_ulp a rnd_mode sh bx

val mpfr_add1sp1: a:mpfr_ptr -> b:mpfr_ptr -> c:mpfr_ptr ->
                  rnd_mode:mpfr_rnd_t -> p:mpfr_reg_prec_t -> Stack i32
    (requires (fun h -> live h a /\ live h b /\ live h c /\ 
		     (let as = Seq.index (as_seq h a) 0 in
		     let bs = Seq.index (as_seq h b) 0 in
		     let cs = Seq.index (as_seq h c) 0 in
		     mpfr_reg_struct_cond h bs /\ mpfr_reg_struct_cond h cs /\
		     U32.v p < U32.v gmp_NUMB_BITS - 1 /\
		     U32.v p = U32.v as.mpfr_prec /\
		     U32.v p = U32.v bs.mpfr_prec /\ U32.v p = U32.v cs.mpfr_prec /\
		     (let am = as.mpfr_d in
		     let bm = bs.mpfr_d in
		     let cm = cs.mpfr_d in
		     live h am /\ live h bm /\ live h cm /\
		     disjoint a b /\ disjoint a c /\ disjoint b c /\
		     disjoint a am /\ disjoint a bm /\ disjoint a cm /\
		     disjoint b am /\ disjoint b bm /\ disjoint b cm /\
		     disjoint c am /\ disjoint c bm /\ disjoint c cm /\
		     disjoint am bm /\ disjoint am cm /\ disjoint bm cm /\
		     length am = 1 /\ length bm = 1 /\ length cm = 1))))
    (ensures  (fun h0 r h1 -> live h1 a /\ live h1 b /\ live h1 c /\
		           (let as0 = Seq.index (as_seq h0 a) 0 in
			   let as = Seq.index (as_seq h1 a) 0 in
		           let bs = Seq.index (as_seq h1 b) 0 in
		           let cs = Seq.index (as_seq h1 c) 0 in
		           let am = as.mpfr_d in
		           let bm = bs.mpfr_d in
		           let cm = cs.mpfr_d in
			   live h1 am /\ live h1 bm /\ live h1 cm /\
		           am == as0.mpfr_d /\ modifies_2 a am h0 h1)))

let mpfr_add1sp1 a b c rnd_mode p =
    let h0 = ST.get() in
    let st = mpfr_add1sp1_any a.(0ul) b.(0ul) c.(0ul) p in // Maybe include (1<<sh) in it too?
    let h1 = ST.get() in
    lemma_reveal_modifies_1 (mpfr_MANT a) h0 h1;
    lemma_intro_modifies_2 a (mpfr_MANT a) h0 h1;
    if I32.(st.bx >^ mpfr_EMAX) then begin
        mpfr_overflow a rnd_mode (mpfr_SIGN a)
    end else begin
        mpfr_add1sp1_round a rnd_mode st
    end
