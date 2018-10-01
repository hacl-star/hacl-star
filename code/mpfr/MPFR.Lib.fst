module MPFR.Lib

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Buffer
open FStar.UInt64

module ST = FStar.HyperStack.ST
module I32 = FStar.Int32
module U32 = FStar.UInt32

open MPFR.Maths
open MPFR.Dyadic
open MPFR.Lib.Spec
open MPFR.Round.Spec

include MPFR.RoundingMode

#set-options "--z3refresh --z3rlimit 50 --max_fuel 1 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 0"

// GENERIC LIBRARY DEFINITIONS
type i32 = FStar.Int32.t
type u32 = FStar.UInt32.t
type u64 = FStar.UInt64.t

inline_for_extraction let mpfr_SIGN_POS = 1l
inline_for_extraction let mpfr_SIGN_NEG = -1l

type mpfr_sign_t = s:i32{s = mpfr_SIGN_NEG \/ s = mpfr_SIGN_POS}
type mpfr_prec_t = p:u32{U32.v p > 0}
type mpfr_exp_t  = i32
type mp_limb_t = u64

noeq type mpfr_struct = {
    mpfr_prec: mpfr_prec_t;
    mpfr_sign: mpfr_sign_t;
    mpfr_exp : mpfr_exp_t;
    mpfr_d: buffer mp_limb_t
}

type mpfr_ptr = b:buffer mpfr_struct{length b = 1}
type mpfr_srcptr = mpfr_ptr

inline_for_extraction let mk_mpfr_struct p s e d = {
    mpfr_prec = p;
    mpfr_sign = s;
    mpfr_exp = e;
    mpfr_d = d
}

(* range settings *)
(* precision *)
inline_for_extraction let gmp_NUMB_BITS = 64ul
inline_for_extraction val mpfr_PREC_MIN: p:u32{U32.v p = mpfr_PREC_MIN_spec}
inline_for_extraction let mpfr_PREC_MIN = 1ul
inline_for_extraction val mpfr_PREC_MAX: p:u32{U32.v p = mpfr_PREC_MAX_spec}
inline_for_extraction let mpfr_PREC_MAX = 0x7ffffffful // Note: 0x7ffffefful in original code

(* exponent *)
inline_for_extraction val mpfr_EXP_MIN: x:i32{I32.v x = -pow2 31}
inline_for_extraction let mpfr_EXP_MIN = assert_norm(-0x80000000 = -pow2 31); -0x80000000l
inline_for_extraction val mpfr_EXP_MAX: x:i32{I32.v x = pow2 31 - 1}
inline_for_extraction let mpfr_EXP_MAX = assert_norm(0x7fffffff = pow2 31 - 1); 0x7fffffffl
inline_for_extraction let mpfr_EXP_ZERO = I32.(mpfr_EXP_MIN +^ 1l)
inline_for_extraction let mpfr_EXP_NAN  = I32.(mpfr_EXP_MIN +^ 2l)
inline_for_extraction let mpfr_EXP_INF  = I32.(mpfr_EXP_MIN +^ 3l)

inline_for_extraction val mpfr_EXP_INVALID: x:i32{I32.v x = pow2 30}
inline_for_extraction let mpfr_EXP_INVALID = assert_norm(0x40000000 = pow2 30); 0x40000000l
inline_for_extraction val mpfr_EMIN: x:i32{I32.v x = mpfr_EMIN_spec}
inline_for_extraction let mpfr_EMIN = I32.(1l -^ mpfr_EXP_INVALID)
inline_for_extraction val mpfr_EMAX: x:i32{I32.v x = mpfr_EMAX_spec}
inline_for_extraction let mpfr_EMAX = I32.(mpfr_EXP_INVALID -^ 1l)

(* validity and regularity *)
type mpfr_reg_prec_t = p:u32{mpfr_PREC_COND (U32.v p)}
type mpfr_reg_exp_t  = x:i32{mpfr_EXP_COND (I32.v x)}

(* First bit is 1 *)
let mpfr_d_valn_cond (m:mp_limb_t): GTot Type0 =
    v m >= pow2 63

(* Ending bits are 0 *)
let mpfr_d_val0_cond (m:mp_limb_t) (p:mpfr_prec_t{U32.v p > 0}): GTot Type0 =
    v m % pow2 (prec_to_len (U32.v p) - U32.v p) = 0

let normal_cond_ h (s:mpfr_struct): GTot Type0 =
    prec_to_len (U32.v s.mpfr_prec) = length s.mpfr_d * 64 /\
    mpfr_d_valn_cond (get h s.mpfr_d (length s.mpfr_d - 1)) /\
    mpfr_d_val0_cond (get h s.mpfr_d 0) s.mpfr_prec

let normal_cond h (a:mpfr_ptr): GTot Type0 = normal_cond_ h (Seq.index (as_seq h a) 0)

let mpfr_reg_cond_ h (s:mpfr_struct): GTot Type0 =
    normal_cond_ h s /\
    mpfr_PREC_COND (U32.v s.mpfr_prec) /\ mpfr_EXP_COND (I32.v s.mpfr_exp)

let mpfr_reg_cond h (a:mpfr_ptr): GTot Type0 = mpfr_reg_cond_ h (Seq.index (as_seq h a) 0)

let mpfr_valid_cond_ h (s:mpfr_struct): GTot Type0 =
    mpfr_PREC_COND (U32.v s.mpfr_prec) /\ 
    prec_to_len (U32.v s.mpfr_prec) = length s.mpfr_d * 64 /\
    (s.mpfr_exp = mpfr_EXP_NAN \/ s.mpfr_exp = mpfr_EXP_INF \/
    s.mpfr_exp = mpfr_EXP_ZERO \/ mpfr_reg_cond_ h s)

let mpfr_valid_cond h (a:mpfr_ptr): GTot Type0 = mpfr_valid_cond_ h (Seq.index (as_seq h a) 0)


(* Conversion to pure struct *)
val to_val: s:Seq.seq u64 -> Tot (n:nat{n < pow2 (Seq.length s * 64)}) (decreases (Seq.length s))

let rec to_val (s:Seq.seq u64) = 
    if Seq.length s = 0 then 0
    else begin
        lemma_pow2_mul ((Seq.length s - 1) * 64) 64;
	lemma_distr_sub_left (pow2 ((Seq.length s - 1) * 64)) 1 (pow2 64);
        v (Seq.index s 0) + to_val (Seq.slice s 1 (Seq.length s)) * pow2 64
    end

val to_val_right_slice_lemma: s:Seq.seq u64{Seq.length s > 0} -> Lemma
    (to_val s = v (Seq.index s 0) + to_val (Seq.slice s 1 (Seq.length s)) * pow2 64)

let to_val_right_slice_lemma s = ()

val to_val_left_slice_lemma: s:Seq.seq u64{Seq.length s > 0} -> Lemma
    (ensures (to_val s = to_val (Seq.slice s 0 (Seq.length s - 1)) + v (Seq.index s (Seq.length s - 1)) * pow2 ((Seq.length s - 1) * 64)))
    (decreases (Seq.length s))

let rec to_val_left_slice_lemma s =
    if Seq.length s = 1 then () else begin
	let rs = Seq.slice s 1 (Seq.length s) in
        to_val_left_slice_lemma rs;
	lemma_distr_add_left (pow2 64) (v (Seq.index rs 0)) (to_val (Seq.slice rs 1 (Seq.length rs)));
	lemma_pow2_mul ((Seq.length s - 2) * 64) 64;
	to_val_right_slice_lemma (Seq.slice s 0 (Seq.length s - 1))
    end

val to_val1_lemma: s:Seq.seq u64{Seq.length s = 1} -> Lemma
    (to_val s = v (Seq.index s 0))
    [SMTPat (to_val s)]

let to_val1_lemma s = ()

val valn_cond_lemma: s:Seq.seq u64 -> Lemma
    (requires (Seq.length s > 0 /\ mpfr_d_valn_cond (Seq.index s (Seq.length s - 1))))
    (ensures  (to_val s >= pow2 (Seq.length s * 64 - 1)))
    (decreases (Seq.length s))

let rec valn_cond_lemma s =
    if Seq.length s = 1 then () else begin
        valn_cond_lemma (Seq.slice s 1 (Seq.length s));
        lemma_pow2_mul (Seq.length s * 64 - 65) 64
    end

val val0_cond_lemma: s:Seq.seq u64 -> p:mpfr_prec_t{U32.v p > 0} -> Lemma
    (requires  (prec_to_len (U32.v p) = Seq.length s * 64 /\
                mpfr_d_val0_cond (Seq.index s 0) p))
    (ensures   (to_val s % pow2 (Seq.length s * 64 - U32.v p) = 0))
    (decreases (U32.v p))
    
let val0_cond_lemma s p =
    lemma_pow2_mod 64 (Seq.length s * 64 - U32.v p);
    lemma_mul_mod_zero (to_val (Seq.slice s 1 (Seq.length s))) (pow2 64) (pow2 (Seq.length s * 64 - U32.v p));
    lemma_mod_distr_zero (v (Seq.index s 0)) (to_val (Seq.slice s 1 (Seq.length s)) * pow2 64) (pow2 (Seq.length s * 64 - U32.v p))

let as_val h (b:buffer mp_limb_t) = to_val (as_seq h b)

(* Convert valid mpfr_ptr to mpfr_fr *)
let as_struct h (a:mpfr_ptr) = Seq.index (as_seq h a) 0

val as_normal_: h:mem -> s:mpfr_struct{normal_cond_ h s} -> GTot normal_fp

let as_normal_ h s =
    let sign = I32.v s.mpfr_sign in
    let prec = U32.v s.mpfr_prec in
    let exp  = I32.v s.mpfr_exp  in
    let limb = as_val h s.mpfr_d in
    let l    = length s.mpfr_d in
    assert(prec_to_len prec = l * 64);
    valn_cond_lemma (as_seq h s.mpfr_d);
    val0_cond_lemma (as_seq h s.mpfr_d) s.mpfr_prec;
    mk_fp_struct sign prec exp limb (l * 64) MPFR_NUM

let as_normal h (a:mpfr_ptr{normal_cond h a}) = as_normal_ h (as_struct h a)

let as_reg_fp_ h (s:mpfr_struct{mpfr_reg_cond_ h s}): GTot mpfr_reg_fp = as_normal_ h s

let as_reg_fp h (a:mpfr_ptr{mpfr_reg_cond h a}) = as_reg_fp_ h (as_struct h a)

let as_fp_ h (s:mpfr_struct{mpfr_valid_cond_ h s}): GTot mpfr_fp =
    let init = mk_fp_struct (I32.v s.mpfr_sign) (U32.v s.mpfr_prec) 0 0 (length s.mpfr_d * 64) MPFR_NAN in
    if s.mpfr_exp = mpfr_EXP_NAN then init
    else if s.mpfr_exp = mpfr_EXP_INF then {init with flag = MPFR_INF}
    else if s.mpfr_exp = mpfr_EXP_ZERO then {init with flag = MPFR_ZERO}
    else as_reg_fp_ h s

let as_fp h (a:mpfr_ptr{mpfr_valid_cond_ h (as_struct h a)}) = as_fp_ h (as_struct h a)


(* Useful expression for specification *)
let mpfr_live h a = 
    live h a /\ live h (as_struct h a).mpfr_d /\
    disjoint a (as_struct h a).mpfr_d

let mpfr_disjoint_or_equal h a b = 
    disjoint a (as_struct h b).mpfr_d /\ disjoint b (as_struct h a).mpfr_d /\
    (a == b \/ (disjoint a b /\ disjoint (as_struct h a).mpfr_d (as_struct h b).mpfr_d))

let mpfr_modifies a h0 h1 =
    (as_struct h0 a).mpfr_prec = (as_struct h1 a).mpfr_prec /\
    (as_struct h0 a).mpfr_d == (as_struct h1 a).mpfr_d /\
    modifies_2 a (as_struct h1 a).mpfr_d h0 h1

val mpfr_modifies_trans_lemma: a:mpfr_ptr -> h0:mem -> h1:mem -> h2:mem -> Lemma
    (requires (mpfr_modifies a h0 h1 /\ mpfr_modifies a h1 h2))
    (ensures  (mpfr_modifies a h0 h2))
    [SMTPat (mpfr_modifies a h0 h1); SMTPat (mpfr_modifies a h1 h2)]

let mpfr_modifies_trans_lemma a h0 h1 h2 = ()

(* Access to entries *)
(* precision *)
val mpfr_PREC: x:mpfr_ptr -> Stack mpfr_prec_t 
    (requires (fun h -> mpfr_live h x))
    (ensures  (fun h0 r h1 -> mpfr_live h1 x /\ h0 == h1 /\
                          r = (as_struct h1 x).mpfr_prec))
let mpfr_PREC x = 
    let f = x.(0ul) in
    f.mpfr_prec
    
val mpfr_GET_PREC: x:mpfr_ptr -> Stack mpfr_reg_prec_t 
    (requires (fun h -> mpfr_live h x /\ mpfr_PREC_COND (U32.v (as_struct h x).mpfr_prec)))
    (ensures  (fun h0 r h1 -> mpfr_live h1 x /\ h0 == h1 /\
                          r = (as_struct h1 x).mpfr_prec))
let mpfr_GET_PREC x = 
    let f = x.(0ul) in
    f.mpfr_prec

(* exponent *)
val mpfr_EXP: x:mpfr_ptr -> Stack mpfr_exp_t 
    (requires (fun h -> mpfr_live h x))
    (ensures  (fun h0 r h1 -> mpfr_live h1 x /\ h0 == h1 /\
                          r = (as_struct h1 x).mpfr_exp))
let mpfr_EXP x = 
    let f = x.(0ul) in
    f.mpfr_exp

val mpfr_SET_EXP: x:mpfr_ptr -> e:mpfr_exp_t -> Stack unit
    (requires (fun h -> mpfr_live h x))
    (ensures  (fun h0 _ h1 -> mpfr_live h1 x /\ mpfr_modifies x h0 h1 /\
                           (as_struct h1 x).mpfr_exp = e /\
			   (as_struct h1 x).mpfr_sign = (as_struct h0 x).mpfr_sign /\
			   as_seq h1 (as_struct h1 x).mpfr_d == as_seq h0 (as_struct h0 x).mpfr_d))

let mpfr_SET_EXP x e = 
    let h0 = ST.get() in
    let f = x.(0ul) in
    x.(0ul) <- {f with mpfr_exp = e};
    let h1 = ST.get() in
    lemma_reveal_modifies_1 x h0 h1;
    lemma_intro_modifies_2 x (as_struct h1 x).mpfr_d h0 h1

let mpfr_IS_NAN   x = mpfr_EXP x = mpfr_EXP_NAN
let mpfr_SET_NAN  x = mpfr_SET_EXP x mpfr_EXP_NAN
let mpfr_IS_INF   x = mpfr_EXP x = mpfr_EXP_INF
let mpfr_SET_INF  x = mpfr_SET_EXP x mpfr_EXP_INF
let mpfr_IS_ZERO  x = mpfr_EXP x = mpfr_EXP_ZERO
let mpfr_SET_ZERO x = mpfr_SET_EXP x mpfr_EXP_ZERO
let mpfr_NOTZERO  x = not (mpfr_IS_ZERO x)

(* sign *)
val mpfr_SIGN: x:mpfr_ptr -> Stack mpfr_sign_t 
    (requires (fun h -> mpfr_live h x))
    (ensures  (fun h0 r h1 -> mpfr_live h1 x /\ h0 == h1 /\
                           r = (as_struct h1 x).mpfr_sign))
let mpfr_SIGN x = 
    let f = x.(0ul) in
    f.mpfr_sign

val mpfr_SET_SIGN: x:mpfr_ptr -> s:mpfr_sign_t -> Stack unit
    (requires (fun h -> mpfr_live h x))
    (ensures  (fun h0 _ h1 -> mpfr_live h1 x /\ mpfr_modifies x h0 h1 /\
                           (as_struct h1 x).mpfr_sign = s /\
			   (as_struct h1 x).mpfr_exp = (as_struct h0 x).mpfr_exp /\
			   as_seq h1 (as_struct h1 x).mpfr_d == as_seq h0 (as_struct h0 x).mpfr_d))
			   
let mpfr_SET_SIGN x s = 
    let h0 = ST.get() in
    let f = x.(0ul) in
    x.(0ul) <- {f with mpfr_sign = s};
    let h1 = ST.get() in
    lemma_reveal_modifies_1 x h0 h1;
    lemma_intro_modifies_2 x (as_struct h1 x).mpfr_d h0 h1

let mpfr_NEG_SIGN s = if s = mpfr_SIGN_POS then mpfr_SIGN_NEG else mpfr_SIGN_POS

let mpfr_IS_POS x = I32.(mpfr_SIGN x >^ 0l)
let mpfr_IS_NEG x = I32.(mpfr_SIGN x <^ 0l)

let mpfr_IS_STRICTPOS x = mpfr_NOTZERO x /\ mpfr_IS_POS x
let mpfr_IS_STRICTNEG x = mpfr_NOTZERO x /\ mpfr_IS_NEG x

let mpfr_SET_POS x = mpfr_SET_SIGN x mpfr_SIGN_POS
let mpfr_SET_NEG x = mpfr_SET_SIGN x mpfr_SIGN_NEG

let mpfr_CHANGE_SIGN x = mpfr_SET_SIGN x (mpfr_NEG_SIGN (mpfr_SIGN x))
let mpfr_SET_SAME_SIGN x y = mpfr_SET_SIGN x (mpfr_SIGN y)
let mpfr_SET_OPPOSITE_SIGN x y = mpfr_SET_SIGN x (mpfr_NEG_SIGN (mpfr_SIGN y))

let mpfr_IS_POS_SIGN s = I32.(s >^ 0l)
let mpfr_IS_NEG_SIGN s = I32.(s <^ 0l)
let mpfr_MULT_SIGN (s1:mpfr_sign_t) (s2:mpfr_sign_t): Tot mpfr_sign_t  = I32.(s1 *^ s2)

(* significand *)
val mpfr_MANT: x:mpfr_ptr -> Stack (buffer mp_limb_t)
    (requires (fun h -> mpfr_live h x))
    (ensures  (fun h0 r h1 -> mpfr_live h1 x /\ h0 == h1 /\
			   r == (as_struct h1 x).mpfr_d))

let mpfr_MANT x = 
    let f = x.(0ul) in
    f.mpfr_d

val mpn_ZERO: b:buffer mp_limb_t -> l:u32 -> Stack unit
    (requires (fun h -> live h b /\ length b >= U32.v l))
    (ensures  (fun h0 _ h1 ->
        live h1 b /\ modifies_1 b h0 h1 /\
        (forall (i:nat{i < U32.v l}). Seq.index (as_seq h1 b) i = 0uL) /\
        (forall (i:nat{i >= U32.v l /\ i < length b}). Seq.index (as_seq h1 b) i = Seq.index (as_seq h0 b) i) /\
        to_val (Seq.slice (as_seq h1 b) 0 (U32.v l)) = 0))

let rec mpn_ZERO b l =
    if U32.(l =^ 0ul) then () else begin
        b.(U32.(l -^ 1ul)) <- 0uL;
        mpn_ZERO b U32.(l -^ 1ul);
	let h = ST.get() in
	to_val_left_slice_lemma (Seq.slice (as_seq h b) 0 (U32.v l))
    end

(* useful functions *)
val mpfr_LAST_LIMB: x:mpfr_ptr -> Stack u32
    (requires (fun h -> mpfr_live h x /\ mpfr_PREC_COND (U32.v (as_struct h x).mpfr_prec)))
    (ensures  (fun h0 r h1 -> mpfr_live h1 x /\ h0 == h1 /\
                           (U32.v r + 1) * 64 = prec_to_len (U32.v (as_struct h1 x).mpfr_prec)))

let mpfr_LAST_LIMB x =
    U32.((mpfr_GET_PREC x -^ 1ul) /^ gmp_NUMB_BITS)

val mpfr_LIMB_SIZE: x:mpfr_ptr -> Stack u32
    (requires (fun h -> mpfr_live h x /\ mpfr_PREC_COND (U32.v (as_struct h x).mpfr_prec)))
    (ensures  (fun h0 r h1 -> mpfr_live h1 x /\ h0 == h1 /\
                           U32.v r * 64 = prec_to_len (U32.v (as_struct h1 x).mpfr_prec)))

let mpfr_LIMB_SIZE x = U32.(mpfr_LAST_LIMB x +^ 1ul)

(* special value *)
let mpfr_LIMB_ONE = 1uL

val mpfr_LIMB_MASK: s:u32{U32.v s < 64} ->
    Tot (r:u64{v r = pow2 (U32.v s) - 1})
let mpfr_LIMB_MASK s =
    let lsh = 1uL <<^ s in
    lemma_pow2_small_mod (U32.v s) 64;
    lsh -^ 1uL
    
val mpfr_LIMB_HIGHBIT: s:u64{v s = pow2 63}
let mpfr_LIMB_HIGHBIT =
    assert_norm(UInt.pow2_n #64 63 = v 0x8000000000000000uL);
    0x8000000000000000uL

val mpfr_LIMB_MAX: s:u64{v s = pow2 64 - 1}
let mpfr_LIMB_MAX =
    assert_norm(pow2 64 - 1 = v 0xffffffffffffffffuL);
    0xffffffffffffffffuL

(* set special value *)
val mpfr_setmax_rec: x:mpfr_ptr -> i:u32 -> Stack unit
    (requires (fun h -> 
        let p = (as_struct h x).mpfr_prec in
        mpfr_live h x /\ U32.v i < length (as_struct h x).mpfr_d /\ mpfr_PREC_COND (U32.v p)))
    (ensures  (fun h0 _ h1 -> 
        let p = (as_struct h0 x).mpfr_prec in
        mpfr_live h1 x /\ mpfr_modifies x h0 h1 /\
        (as_struct h1 x).mpfr_sign = (as_struct h0 x).mpfr_sign /\
        (as_struct h1 x).mpfr_exp = (as_struct h0 x).mpfr_exp /\
        (let xm = as_seq h1 (as_struct h1 x).mpfr_d in
        v (Seq.index xm 0) = pow2 64 - pow2 (prec_to_len (U32.v p) - U32.v p) /\
        (forall (j:nat{j > 0 /\ j <= U32.v i}). v (Seq.index xm j) = pow2 64 - 1))))

let rec mpfr_setmax_rec x i =
    let mant = mpfr_MANT x in
    if i = 0ul then begin
        let p = mpfr_GET_PREC x in
	let l = mpfr_LIMB_SIZE x in
	let h0 = ST.get() in
	mant.(i) <- mpfr_LIMB_MAX <<^ U32.(l *^ gmp_NUMB_BITS -^ p);
	lemma_distr_sub_left (pow2 (prec_to_len (U32.v p) - U32.v p)) (pow2 64) 1;
	lemma_pow2_mul 64 (prec_to_len (U32.v p) - U32.v p);
	lemma_mod_distr_sub (pow2 (64 + prec_to_len (U32.v p) - U32.v p)) (pow2 (prec_to_len (U32.v p) - U32.v p)) (pow2 64);
	lemma_pow2_mod (64 + prec_to_len (U32.v p) - U32.v p) 64;
	lemma_pow2_lt (prec_to_len (U32.v p) - U32.v p) 64;
	lemma_small_mod (pow2 (prec_to_len (U32.v p) - U32.v p)) (pow2 64);
	//! assert(v mant.(i) = pow2 64 - pow2 (prec_to_len (U32.v p) - U32.v p));
	let h1 = ST.get() in
	lemma_reveal_modifies_1 (mpfr_MANT x) h0 h1;
	lemma_intro_modifies_2 x (mpfr_MANT x) h0 h1
    end else begin
	mpfr_setmax_rec x U32.(i -^ 1ul);
        mant.(i) <- mpfr_LIMB_MAX
    end

val to_val_setmax_lemma: s:Seq.seq u64{Seq.length s > 0} -> sh:nat{sh < 64} -> Lemma
    (requires (v (Seq.index s 0) = pow2 64 - pow2 sh /\
              (forall (i:pos{i < Seq.length s}). v (Seq.index s i) = pow2 64 - 1)))
    (ensures  (to_val s = pow2 (Seq.length s * 64) - pow2 sh))
    (decreases (Seq.length s))

let rec to_val_setmax_lemma s sh =
    if Seq.length s = 1 then () else begin
        to_val_left_slice_lemma s;
	lemma_distr_sub_left (pow2 (Seq.length s - 1) * 64) (pow2 64) 1;
	lemma_pow2_mul 64 ((Seq.length s - 1) * 64);
	to_val_setmax_lemma (Seq.slice s 0 (Seq.length s - 1)) sh
    end

val mpfr_setmax: x:mpfr_ptr -> Stack unit
    (requires (fun h -> 
        let p = (as_struct h x).mpfr_prec in
        let l = U32.((p -^ 1ul) /^ 64ul +^ 1ul) in
        mpfr_live h x /\ mpfr_PREC_COND (U32.v p) /\ length (as_struct h x).mpfr_d = U32.v l))
    (ensures  (fun h0 _ h1 -> 
        mpfr_live h1 x /\ mpfr_modifies x h0 h1 /\
        (as_struct h1 x).mpfr_sign = (as_struct h0 x).mpfr_sign /\
	mpfr_reg_cond h1 x /\
	as_reg_fp h1 x == mpfr_max_value (as_reg_fp h1 x).sign (as_reg_fp h1 x).prec /\
	eval_abs (as_reg_fp h1 x) =. mpfr_overflow_bound (as_reg_fp h1 x).prec))

let mpfr_setmax x =
    mpfr_SET_EXP x mpfr_EMAX;
    mpfr_setmax_rec x (mpfr_LAST_LIMB x);
    let h = ST.get() in
    let p = mpfr_GET_PREC x in
    let l = mpfr_LIMB_SIZE x in
    let sh = prec_to_len (U32.v p) - U32.v p in
    lemma_pow2_double 63;
    lemma_pow2_le sh 63;
    //! assert(pow2 64 - pow2 sh >= pow2 63);
    lemma_pow2_mod 64 sh;
    lemma_mod_distr_sub_zero (pow2 64) (pow2 sh) (pow2 sh);
    //! assert((pow2 64 - pow2 sh) % (pow2 sh) = 0);
    valn_cond_lemma (as_seq h (as_struct h x).mpfr_d);
    val0_cond_lemma (as_seq h (as_struct h x).mpfr_d) (as_struct h x).mpfr_prec;
    to_val_setmax_lemma (as_seq h (as_struct h x).mpfr_d) sh

val to_val_setmin_lemma: s:Seq.seq u64{Seq.length s > 0} -> Lemma
    (requires (v (Seq.index s (Seq.length s - 1)) = pow2 63 /\
              (forall (i:nat{i < Seq.length s - 1}). v (Seq.index s i) = 0)))
    (ensures  (to_val s = pow2 (Seq.length s * 64 - 1)))
    (decreases (Seq.length s))

let rec to_val_setmin_lemma s =
    if Seq.length s = 1 then () else begin
        to_val_right_slice_lemma s;
	lemma_pow2_mul 63 ((Seq.length s - 1) * 64);
	to_val_setmin_lemma (Seq.slice s 1 (Seq.length s))
    end

val mpfr_setmin: x:mpfr_ptr -> Stack unit
    (requires (fun h -> 
        let p = (as_struct h x).mpfr_prec in
        let l = U32.((p -^ 1ul) /^ 64ul +^ 1ul) in
        mpfr_live h x /\ mpfr_PREC_COND (U32.v p) /\ length (as_struct h x).mpfr_d = U32.v l))
    (ensures  (fun h0 _ h1 -> 
        mpfr_live h1 x /\ mpfr_modifies x h0 h1 /\
        (as_struct h1 x).mpfr_sign = (as_struct h0 x).mpfr_sign /\
	mpfr_reg_cond h1 x /\
	as_reg_fp h1 x == mpfr_min_value (as_reg_fp h1 x).sign (as_reg_fp h1 x).prec /\
	eval_abs (as_reg_fp h1 x) =. mpfr_underflow_bound (as_reg_fp h1 x).prec))

let mpfr_setmin x =
    mpfr_SET_EXP x mpfr_EMIN;
    let xn = mpfr_LAST_LIMB x in
    let xp = mpfr_MANT x in
    xp.(xn) <- mpfr_LIMB_HIGHBIT;
    mpn_ZERO xp xn;
    let h = ST.get() in
    lemma_pow2_mod 63 (prec_to_len (U32.v ((as_struct h x).mpfr_prec)) - U32.v ((as_struct h x).mpfr_prec));
    //! assert((pow2 63) % (pow2 sh) = 0);
    valn_cond_lemma (as_seq h (as_struct h x).mpfr_d);
    val0_cond_lemma (as_seq h (as_struct h x).mpfr_d) (as_struct h x).mpfr_prec;
    to_val_setmin_lemma (as_seq h (as_struct h x).mpfr_d)
