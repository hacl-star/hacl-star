module MPFR.Sub1sp1

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Buffer
open FStar.UInt64
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

module ST = FStar.HyperStack.ST
module I32 = FStar.Int32
module I64 = FStar.Int64
module U32 = FStar.UInt32

#set-options "--z3refresh --z3rlimit 100 --max_fuel 1 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 0"

private type mpfr_tmp_exp_t = x:mpfr_exp_t{I64.(x >=^ mpfr_EMIN /\ x <=^ mpfr_EMAX +^ 1L)}

private noeq type state = {
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
        (as_struct h a).mpfr_sign = (as_struct h b).mpfr_sign /\
        mpfr_valid_cond h a /\ mpfr_reg_cond h b /\ mpfr_reg_cond h c

let mpfr_sub1sp1_pre_cond_2 h (a:mpfr_ptr) b c bx cx ap bp cp: GTot Type0=
 (as_struct h b).mpfr_exp=bx /\
 (as_struct h c).mpfr_exp=cx /\ 
 equal h (as_struct h a).mpfr_d h ap /\
 equal h (as_struct h b).mpfr_d h bp /\
 equal h (as_struct h c).mpfr_d h cp /\
 live h ap /\ live h bp /\ live h cp

let mpfr_sub1sp1_post_cond h0 t h1 (a:mpfr_ptr) b c (p:mpfr_reg_prec_t) rnd_mode exact: GTot Type0=
        (* Memory safety *)
        mpfr_live h1 a /\ mpfr_live h1 b /\ mpfr_live h1 c /\
        mpfr_disjoint_or_equal h1 a b /\ mpfr_disjoint_or_equal h1 a c /\
        mpfr_disjoint_or_equal h1 b c /\ mpfr_modifies a h0 h1 /\
        (* Functional correctness *)
        mpfr_valid_cond h1 a /\ 
        mpfr_round_cond exact (I64.v p) rnd_mode (as_fp h1 a) /\
        mpfr_ternary_cond (I32.v t) exact (as_fp h1 a)

let mpfr_sub1sp1_round_spec (high:normal_fp) (rb:bool) (sb:bool) (rnd_mode:mpfr_rnd_t):
    Tot (r:normal_fp{r.prec = high.prec}) =
    if rb = false && sb = false then high
    else if MPFR_RNDN? rnd_mode then begin
	if rb = false || (sb = false && is_even high)
	then high
	else add_one_ulp high
    end else if mpfr_IS_LIKE_RNDZ rnd_mode (high.sign < 0) then high
    else add_one_ulp high

inline_for_extraction val count_leading_zeros: a:u64{not (a=^0uL)}->Tot (cnt:u32{U32.v cnt<32})

let  count_leading_zeros a=admit()

inline_for_extraction val mpfr_sub1sp1_round:(*Warning : the ensure part is too copy-pasted to be correct*)
    a:mpfr_ptr -> ap:buffer mp_limb_t -> sh:mpfr_reg_prec_t -> bx:mpfr_reg_exp_t ->
    rb:mp_limb_t -> sb:mp_limb_t -> rnd_mode:mpfr_rnd_t ->Stack i32
    (requires (fun h->True))
    (ensures (fun h0 r h1-> mpfr_live h1 a /\ mpfr_modifies a h0 h1 /\ mpfr_valid_cond h1 a /\ True))

let mpfr_sub1sp1_round a ap bx rb sb rnd_mode=admit()

inline_for_extraction val mpfr_sub1sp1_eq_branch_1:
    a:mpfr_ptr -> b:mpfr_ptr -> c:mpfr_ptr ->
    ap:buffer mp_limb_t -> bp:buffer mp_limb_t -> cp:buffer mp_limb_t ->
    bx:mpfr_reg_exp_t ->cx:mpfr_reg_exp_t
    ->rnd_mode:mpfr_rnd_t->
    p:mpfr_reg_prec_t -> sh:mpfr_reg_prec_t -> Stack i32
    (requires (fun h->mpfr_sub1sp1_pre_cond h a b c p /\
    mpfr_sub1sp1_pre_cond_2 h a b c bx cx ap bp cp /\
    I64.(bx=^cx) /\ as_val h bp=as_val h cp 
    ))
 (ensures (fun h0 t h1 -> 
   let exact=sub1sp_exact (as_fp h0 b) (as_fp h0 c) in 
   mpfr_sub1sp1_post_cond h0 t h1 a b c p rnd_mode exact))

let mpfr_sub1sp1_eq_branch_1 a b c ap bp cp bx cx rnd_mode p sh=
    if rnd_mode=MPFR_RNDD then mpfr_SET_NEG a else mpfr_SET_POS a;
    mpfr_SET_ZERO a;
    mpfr_RET 0l

inline_for_extraction val mpfr_sub1sp1_eq:
    a:mpfr_ptr -> b:mpfr_ptr -> c:mpfr_ptr ->
    ap:buffer mp_limb_t -> bp:buffer mp_limb_t -> cp:buffer mp_limb_t ->
    bx:mpfr_reg_exp_t ->cx:mpfr_reg_exp_t
    ->rnd_mode:mpfr_rnd_t->
    p:mpfr_reg_prec_t -> sh:mpfr_reg_prec_t -> Stack i32
    (requires (fun h-> mpfr_sub1sp1_pre_cond h a b c p /\
    mpfr_sub1sp1_pre_cond_2 h a b c bx cx ap bp cp /\
    I64.(bx=^cx)
    ))
    (ensures (fun h0 t h1->
    let exact=sub1sp_exact (as_fp h0 b) (as_fp h0 c) in 
    mpfr_sub1sp1_post_cond h0 t h1 a b c p rnd_mode exact))

let mpfr_sub1sp1_eq a b c ap bp cp bx cx rnd_mode p sh =
    if (bp.(0ul)=cp.(0ul)) then mpfr_sub1sp1_eq_branch_1 a b c ap bp cp bx cx rnd_mode p sh
    else begin admit();
       if(cp.(0ul)>^bp.(0ul)) then begin
         //mpfr_SET_OPPOSITE_SIGN a b;
         let a0=cp.(0ul) -^ bp.(0ul) in
         let cnt=count_leading_zeros a0 in
         ap.(0ul) <- a0<<^cnt;
         mpfr_sub1sp1_round a ap bx 0uL 0uL rnd_mode
       end else begin 
         //mpfr_SET_SAME_SIGN a b;
         let a0=bp.(0ul) -^ cp.(0ul) in
         let cnt=count_leading_zeros a0 in
         ap.(0ul) <- a0<<^cnt;
         mpfr_sub1sp1_round a ap bx 0uL 0uL rnd_mode
       end
    end

inline_for_extraction val mpfr_sub1sp1_gt:
    a:mpfr_ptr -> b:mpfr_ptr -> c:mpfr_ptr ->
    ap:buffer mp_limb_t -> bp:buffer mp_limb_t -> cp:buffer mp_limb_t ->
    bx:mpfr_reg_exp_t ->cx:mpfr_reg_exp_t
    ->rnd_mode:mpfr_rnd_t->
    p:mpfr_reg_prec_t -> sh:mpfr_reg_prec_t -> Stack i32
    (requires (fun h-> mpfr_live h a /\ mpfr_live h b /\ mpfr_live h c /\ length ap>0 /\ length bp>0 /\ length cp>0 /\ live h ap /\ live h bp /\ live h cp /\ I64.v sh = I64.v gmp_NUMB_BITS - I64.v p))
    (ensures (fun h s h1->True))

let mpfr_sub1sp1_gt a b c ap bp cp bx cx rnd_mode p sh =
    let d = I64.(bx-^cx) in
    let mask = mpfr_LIMB_MASK (int64_to_uint32 sh) in
    admit()

(* specifications for mpfr_sub1sp1 *)
val mpfr_sub1sp1: a:mpfr_ptr -> b:mpfr_ptr -> c:mpfr_ptr ->
                  rnd_mode:mpfr_rnd_t -> p:mpfr_prec_t -> Stack i32
    (requires (fun h -> mpfr_sub1sp1_pre_cond h a b c p))
    (ensures  (fun h0 t h1 ->
    let exact=sub1sp_exact (as_fp h0 b) (as_fp h0 c) in
    mpfr_sub1sp1_post_cond h0 t h1 a b c p rnd_mode exact))

let mpfr_sub1sp1 a b c rnd_mode p =
    let bx=mpfr_GET_EXP b in
    let cx=mpfr_GET_EXP c in
    let ap=mpfr_MANT a in
    let bp=mpfr_MANT b in
    let cp=mpfr_MANT c in
    let sh=I64.(gmp_NUMB_BITS -^ p) in
    if I64.(bx =^ cx) then mpfr_sub1sp1_eq a b c ap bp cp bx cx rnd_mode p sh else begin admit();
   let bx,cx,bp,cp=(if I64.(bx >=^ cx) then (mpfr_SET_SAME_SIGN a b;bx,cx,bp,cp) else (mpfr_SET_OPPOSITE_SIGN a b;cx,bx,cp,bp)) in
    ignore (mpfr_sub1sp1_gt a b c ap bp cp bx cx rnd_mode p sh);0l
    end
  (*  let st = mpfr_sub1sp1_any a b c ap p in()*)
   (* let h1 = ST.get() in
    lemma_reveal_modifies_1 (mpfr_MANT a) h0 h1;
    lemma_intro_modifies_2 a (mpfr_MANT a) h0 h1;
    if I64.(st.bx >^ mpfr_EMAX) then begin
        let s = mpfr_SIGN a in
        let t = mpfr_overflow a rnd_mode (mpfr_SIGN a) in
	let h2 = ST.get() in
	mpfr_overflow_post_cond_lemma (add1sp_exact (as_reg_fp h0 b) (as_reg_fp h0 c)) (I64.v (as_struct h0 a).mpfr_prec) rnd_mode (I32.v t) (as_fp h2 a);
	mpfr_modifies_trans_lemma a h0 h1 h2;
	t
    end else begin
        let t = mpfr_add1sp1_round a ap rnd_mode st in
	let h2 = ST.get() in
	mpfr_add1sp1_round_post_cond_lemma (add1sp_exact (as_reg_fp h0 b) (as_reg_fp h0 c)) (I64.v (as_struct h0 a).mpfr_prec) (as_normal_ h1 ({as_struct h1 a with mpfr_exp = st.bx})) (st.rb <> 0uL) (st.sb <> 0uL) rnd_mode (I32.v t) (as_fp h2 a);
	mpfr_modifies_trans_lemma a h0 h1 h2;
	t
    end

On fait l'arrondi
*)
