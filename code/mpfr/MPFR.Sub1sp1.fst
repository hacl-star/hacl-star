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

inline_for_extraction val count_leading_zeros: a:u64{not (a=^0uL)}->Tot (cnt:u32{U32.v cnt<32 /\ v (a<<^cnt)>=pow2 63})

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
        modifies_1 (as_struct h1 a).mpfr_d h0 h1 /\ normal_cond h1 a /\ 
        I64.(v ((as_struct h0 a).mpfr_prec)=v p) /\
        I64.(v ((as_struct h0 b).mpfr_prec)=v p) /\
        I64.(v ((as_struct h0 c).mpfr_prec)=v p) /\
        mpfr_reg_cond h0 b /\ mpfr_reg_cond h0 c /\
        (let r = sub1sp_exact (as_reg_fp h0 b) (as_reg_fp h0 c) in
        normal_fp_cond r /\
        mpfr_EXP_COND (I64.v s.bx) /\
        as_val h1 (as_struct h1 a).mpfr_d * pow2 (high_mant r (I64.v p)).len = (high_mant r (I64.v p)).limb * (pow2 64) /\
        I64.v s.sh = I64.v gmp_NUMB_BITS - I64.v p /\
        I64.v s.bx = (high_mant r (I64.v p)).exp /\
        (rb_def r (I64.v p) = (v s.rb <> 0)) /\
        (sb_def r (I64.v p) = (v s.sb <> 0)) /\
        (high_mant r (I64.v p)).sign = (as_normal h1 a).sign)
        
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
     mpfr_live h1 a /\ mpfr_live h1 b /\ mpfr_live h1 c /\
        length (as_struct h1 a).mpfr_d = 1 /\
        length (as_struct h1 b).mpfr_d = 1 /\ length (as_struct h1 c).mpfr_d = 1 /\
       (* modifies_1 (as_struct h1 a).mpfr_d h0 h1 /\*)  normal_cond h1 a /\ 
        I64.(v ((as_struct h0 a).mpfr_prec)=v p) /\
        I64.(v ((as_struct h0 b).mpfr_prec)=v p) /\
        I64.(v ((as_struct h0 c).mpfr_prec)=v p) /\
        mpfr_reg_cond h0 b /\ mpfr_reg_cond h0 c /\
        (let r = sub1sp_exact (as_reg_fp h0 b) (as_reg_fp h0 c) in
        normal_fp_cond r /\
        mpfr_EXP_COND (I64.v s.bx)(* /\
        as_val h1 (as_struct h1 a).mpfr_d * pow2 (high_mant r (I64.v p)).len = (high_mant r (I64.v p)).limb * (pow2 64) *) /\
        I64.v s.sh = I64.v gmp_NUMB_BITS - I64.v p(* /\
        I64.v s.bx = (high_mant r (I64.v p)).exp*) /\
        I64.v p>=r.prec (*/\
        (rb_def r (I64.v p) = (v s.rb <> 0))*)(* /\
        (sb_def r (I64.v p) = (v s.sb <> 0))*) /\ 
        (high_mant r (I64.v p)).sign = (as_normal h1 a).sign(*)
    mpfr_sub1sp1_any_post_cond h0 t h1 a b c p rnd_mode exact*))))

val mpfr_sub1sp1_eq_prec_lemma:
    b:mpfr_reg_fp -> c:mpfr_reg_fp -> p:pos -> Lemma
    (requires (
    b.prec=p /\ c.prec=p /\
    b.exp=c.exp /\
    b.limb<>c.limb
    ))
    (ensures (let r = sub1sp_exact b c in p>=r.prec))
    
let mpfr_sub1sp1_eq_prec_lemma b c p=
let r=sub1sp_exact b c in
//assert(b.limb>=r.limb \/ c.limb>=r.limb);
assert(pow2 p>=b.limb);admit()

let mpfr_sub1sp1_eq a b c ap bp cp bx cx rnd_mode p sh =
    let h0=ST.get() in
    let vb= v bp.(0ul) in
    let vc= v cp.(0ul) in
    let vsh= I64.(v sh) in 
    if(cp.(0ul)>^bp.(0ul)) then begin admit();
      let a0=cp.(0ul) -^ bp.(0ul) in
      let cnt=count_leading_zeros a0 in
     // mpfr_SET_OPPOSITE_SIGN a b;
      ap.(0ul) <- a0<<^cnt;
      lemma_mod_distr_sub_zero vc vb (pow2 vsh);
      lemma_shift_left_mod_pow2 a0 cnt vsh;
      let h1=ST.get() in
      mk_state sh bx 0uL 0uL
    end else begin 
      let a0=bp.(0ul) -^ cp.(0ul) in
      let cnt=count_leading_zeros a0 in
      mpfr_SET_SAME_SIGN a b;
      ap.(0ul) <- a0<<^cnt;
      lemma_mod_distr_sub_zero vb vc (pow2 vsh);
      lemma_shift_left_mod_pow2 a0 cnt vsh;
      let t=mk_state sh bx 0uL 0uL in t
    end

inline_for_extraction val mpfr_sub1sp1_gt:
    a:mpfr_ptr -> b:mpfr_ptr -> c:mpfr_ptr ->
    ap:buffer mp_limb_t -> bp:buffer mp_limb_t -> cp:buffer mp_limb_t ->
    bx:mpfr_reg_exp_t ->cx:mpfr_reg_exp_t
    ->rnd_mode:mpfr_rnd_t->
    p:mpfr_reg_prec_t -> sh:mpfr_reg_prec_t -> Stack state
    (requires (fun h->
    mpfr_sub1sp1_pre_cond h a b c p /\
    mpfr_sub1sp1_pre_cond_2 h a b c bx cx ap bp cp p sh /\
    I64.(bx >^ cx)))
    (ensures (fun h0 t h1->
    let exact=sub1sp_exact (as_fp h0 b) (as_fp h0 c) in
    mpfr_sub1sp1_any_post_cond h0 t h1 a b c p rnd_mode exact))

let mpfr_sub1sp1_gt a b c ap bp cp bx cx rnd_mode p sh =admit()(*;
    let d = I64.(bx-^cx) in
    let mask = mpfr_LIMB_MASK (int64_to_uint32 sh) in
    if I64.(d <^ gmp_NUMB_BITS) then begin
      let sb=0uL -^ (cp.(0ul) <<^ (int64_to_uint32 I64.(gmp_NUMB_BITS -^ d))) in
      let a0_tmp = bp.(0ul) -^ (if v sb=0 then 0uL else 1uL) -^ (cp.(0ul)>>^(int64_to_uint32 d)) in
      assert(v a0_tmp>0);
      let cnt=count_leading_zeros a0_tmp in
      let a0=if U32.(v cnt)>0 then (a0_tmp<<^cnt) |^ (sb>>^U32.(int64_to_uint32 gmp_NUMB_BITS -^ cnt)) else a0_tmp in
      ap.(0ul)<-a0 &^ (lognot mask);
      mpfr_sub1sp1_round a ap sh bx 0uL 0uL rnd_mode
    end
    else mpfr_RET 0l
*)

(* specifications for mpfr_sub1sp1 *)
val mpfr_sub1sp1: a:mpfr_ptr -> b:mpfr_ptr -> c:mpfr_ptr ->
                  rnd_mode:mpfr_rnd_t -> p:mpfr_prec_t -> Stack i32
    (requires (fun h -> mpfr_sub1sp1_pre_cond h a b c p))
    (ensures  (fun h0 t h1 ->
    let exact=sub1sp_exact (as_fp h0 b) (as_fp h0 c) in
    mpfr_sub1sp1_post_cond h0 t h1 a b c p rnd_mode exact))
(*val mpfr_add1sp1_round_post_cond_lemma: a:normal_fp{mpfr_EXP_COND a.exp} ->
    p:pos{mpfr_PREC_COND p} ->
    high:normal_fp{high.prec = p /\ high.sign = (high_mant a p).sign  /\
                   high.exp = (high_mant a p).exp /\
		   high.limb * pow2 a.len = (high_mant a p).limb * pow2 high.len} ->
    rb:bool{rb = rb_def a p} -> sb:bool{sb = sb_def a p} -> rnd_mode:mpfr_rnd_t ->
    t:int -> r:mpfr_fp{r.prec = p} -> Lemma
    (requires (mpfr_round2_cond (mpfr_add1sp1_round_spec high rb sb rnd_mode) rnd_mode r /\
               t = mpfr_add1sp1_ternary_spec high rb sb rnd_mode))
    (ensures  (mpfr_round_cond a p rnd_mode r /\
               mpfr_ternary_cond t a r))

let mpfr_add1sp1_round_post_cond_lemma a p high rb sb rnd_mode t r =
    mpfr_round_cond_lemma a p high rb sb rnd_mode r;
    mpfr_ternary_cond_lemma a p high rb sb rnd_mode t r*)

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
        let t = mpfr_underflow a rnd_mode (mpfr_SIGN a) in
	let h2 = ST.get() in
	mpfr_underflow_post_cond_lemma (sub1sp_exact (as_reg_fp h0 b) (as_reg_fp h0 c)) (I64.v (as_struct h0 a).mpfr_prec) rnd_mode (I32.v t) (as_fp h2 a);
	t
    end else begin (*Rounding is the same as for add1sp1 (modulo an optimization), so this is copied from mpfr_add1sp1*)
        let t = mpfr_add1sp1_round a ap rnd_mode st in
	let h2 = ST.get() in
	mpfr_add1sp1_round_post_cond_lemma (sub1sp_exact (as_reg_fp h0 b) (as_reg_fp h0 c)) (I64.v (as_struct h0 a).mpfr_prec) (as_normal_ h1 ({as_struct h1 a with mpfr_exp = st.bx})) (st.rb <> 0uL) (st.sb <> 0uL) rnd_mode (I32.v t) (as_fp h2 a);
	t
    end
   end

(*
   (let r = sub1sp_exact (as_reg_fp h0 b) (as_reg_fp h0 c) in
        normal_fp_cond r /\
        mpfr_EXP_COND (I64.v s.bx) /\
        as_val h1 (as_struct h1 a).mpfr_d * pow2 (r.len) = (high_mant r (I64.v p)).limb * (pow2 64) /\
        I64.v s.sh = I64.v gmp_NUMB_BITS - I64.v p /\
        I64.v s.bx = (high_mant r (I64.v p)).exp /\
        (rb_def r (I64.v p) = (v s.rb <> 0)) /\
        (sb_def r (I64.v p) = (v s.sb <> 0)))
*)
