module MPFR.Lib
open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Buffer
open FStar.UInt64

module I32 = FStar.Int32
module U32 = FStar.UInt32

open MPFR.Lemmas
open MPFR.Lib.Spec

// GENERIC LIBRARY DEFINITIONS
type i32 = FStar.Int32.t
type u32 = FStar.UInt32.t
type u64 = FStar.UInt64.t

let gmp_NUMB_BITS = 64ul
let mpfr_PREC_MIN = 1ul
let mpfr_PREC_MAX = U32.(gmp_NUMB_BITS -^ 1ul)
let mpfr_PREC_COND (p:u32) = U32.(mpfr_PREC_MIN <=^ p /\ p <=^ mpfr_PREC_MAX)

val mpfr_EXP_INVALID: x:i32{I32.v x = pow2 30}
let mpfr_EXP_INVALID = assert_norm(0x40000000 = pow2 30); 0x40000000l
let mpfr_EMIN = I32.(1l -^ mpfr_EXP_INVALID)
let mpfr_EMAX = I32.(mpfr_EXP_INVALID -^ 1l)
let mpfr_EXP_COND (x:i32) = I32.(mpfr_EMIN <=^ x /\ x <=^ mpfr_EMAX)

let mpfr_SIGN_POS = 1l
let mpfr_SIGN_NEG = -1l
let mpfr_SIGN_COND (s:i32) = I32.(s =^ mpfr_SIGN_POS \/ s =^ mpfr_SIGN_NEG)

type mpfr_prec_t = p:u32{mpfr_PREC_COND p}
type mpfr_sign_t = s:i32{mpfr_SIGN_COND s}
type mpfr_exp_t  = x:i32{mpfr_EXP_COND  x}
type mpfr_uexp_t = u32
type mp_limb_t = u64

let neg (x:mpfr_sign_t) = if x = 1l then -1l else 1l

noeq type mpfr_struct = {
    mpfr_prec: mpfr_prec_t;
    mpfr_sign: mpfr_sign_t;
    mpfr_exp : mpfr_exp_t;
    mpfr_d: buffer mp_limb_t
}

(* First bit is 1 *)
let mpfr_d_val0_cond (m:mp_limb_t) = v m >= pow2 63
(* Ending bits are 0 *)
let mpfr_d_valn_cond (m:mp_limb_t) (p:mpfr_prec_t) = v m % pow2 (64 - U32.v p) = 0

let valid_struct h (s:mpfr_struct) =
    let l = length s.mpfr_d in
    l >= 1 /\ (l - 1) * 64 < U32.v s.mpfr_prec /\ U32.v s.mpfr_prec <= l * 64 /\
    mpfr_d_val0_cond (get h s.mpfr_d 0) /\
    mpfr_d_valn_cond (get h s.mpfr_d (l - 1)) s.mpfr_prec

(* Conversion to pure struct *)
val to_val: s:Seq.seq u64 -> Tot nat (decreases (Seq.length s))
let rec to_val (s:Seq.seq u64) = 
    if Seq.length s = 0 then 0
    else (v (Seq.index s 0)) * pow2 ((Seq.length s - 1) * 64) + to_val (Seq.slice s 1 (Seq.length s))

let as_val h (b:buffer mp_limb_t) = to_val (as_seq h b)

val as_pure: h:mem -> s:mpfr_struct{valid_struct h s} ->
    GTot (ps:floating_point{
             I32.v s.mpfr_sign = ps.sign /\
	     U32.v s.mpfr_prec = ps.prec /\
	     I32.v s.mpfr_exp  = ps.exp + ps.prec /\
             as_val h s.mpfr_d = ps.mant * pow2 (length s.mpfr_d * 64 - U32.v s.mpfr_prec)})
let as_pure h s =
    let p = U32.v s.mpfr_prec in
    let l = length s.mpfr_d in
    let m = as_val h s.mpfr_d / pow2 (l * 64 - p) in
    lemma_pow2_div_lt (as_val h s.mpfr_d) (l * 64) (l * 64 - p);
    lemma_div_le (pow2 (l * 64 - 1)) (as_val h s.mpfr_d) (pow2 (l * 64 - p));
    lemma_pow2_div (l * 64 - 1) (l * 64 - p);
    {sign = I32.v s.mpfr_sign;
     prec = p;
     mant = as_val h s.mpfr_d / pow2 (length s.mpfr_d * 64 - U32.v s.mpfr_prec);
     exp  = I32.v s.mpfr_exp - U32.v s.mpfr_prec}

(* Struct functions *)
type mpfr_ptr = b:buffer mpfr_struct{length b = 1}

val mk_mpfr_struct: mpfr_prec_t -> mpfr_sign_t -> mpfr_exp_t -> buffer mp_limb_t -> Tot mpfr_struct
let mk_mpfr_struct p s e d = {
    mpfr_prec = p;
    mpfr_sign = s;
    mpfr_exp = e;
    mpfr_d = d
}

val mpfr_SIGN: x:mpfr_ptr -> Stack mpfr_sign_t 
		(requires (fun h -> live h x))
		(ensures (fun h0 r h1 -> live h1 x /\ modifies_0 h0 h1 /\
		            (let xm = Seq.index (as_seq h0 x) 0 in
			     r == xm.mpfr_sign)))
let mpfr_SIGN x = 
    let f = x.(0ul) in
    f.mpfr_sign

val mpfr_EXP: x:mpfr_ptr -> Stack mpfr_exp_t 
		(requires (fun h -> live h x))
		(ensures (fun h0 r h1 -> live h1 x /\ modifies_0 h0 h1 /\
			    (let xm = Seq.index (as_seq h0 x) 0 in
			     r == xm.mpfr_exp)))
let mpfr_EXP x = 
    let f = x.(0ul) in
    f.mpfr_exp

let mpfr_GET_EXP x = mpfr_EXP x

val mpfr_SET_EXP: x:mpfr_ptr -> e:mpfr_exp_t -> Stack unit
		(requires (fun h -> live h x))
		(ensures (fun h0 _ h1 -> live h1 x /\ modifies_1 x h0 h1 /\
			    (let xm = Seq.index (as_seq h1 x) 0 in
			     e == xm.mpfr_exp)))
let mpfr_SET_EXP x e = 
    let f = x.(0ul) in
    x.(0ul) <- {f with mpfr_exp = e}


val mpfr_MANT: x:mpfr_ptr -> Stack (buffer mp_limb_t)
		(requires (fun h -> live h x))
		(ensures (fun h0 r h1 -> live h1 x /\ modifies_0 h0 h1 /\
			    (let xm = Seq.index (as_seq h0 x) 0 in
			     r == xm.mpfr_d)))
let mpfr_MANT x = 
    let f = x.(0ul) in
    f.mpfr_d


type mpfr_srcptr = mpfr_ptr

type mpfr_rnd_t = 
   | MPFR_RNDN 
   | MPFR_RNDZ
   | MPFR_RNDU
   | MPFR_RNDD
   | MPFR_RNDA
   | MPFR_RNDF
   | MPFR_RNDNA

open FStar.UInt

let mpfr_LIMB_ONE = 1uL

val mpfr_LIMB_MASK: s:u32{U32.v s < 64} ->
    Tot (r:u64{forall (i:nat{0 <= i /\ i < 64}). i >= 64 - U32.v s <==> nth (v r) i == true})
let mpfr_LIMB_MASK s =
    let lsh = 1uL <<^ s in
    lemma_pow2_small_mod (U32.v s) 64;
    lsh -^ 1uL

val mpfr_LIMB_HIGHBIT: s:u64{forall (i:nat{0 <= i /\ i < 64}). i == 0 <==> nth (v s) i == true}
let mpfr_LIMB_HIGHBIT =
    assert_norm(pow2_n #64 63 == v 0x8000000000000000uL);
    0x8000000000000000uL

assume val gmpfr_emax: mpfr_exp_t
assume val gmpfr_flags: i32

let mpfr_FLAGS_INEXACT = 8ul

assume val mpfr_RET: i32 -> Tot i32

assume val mpfr_IS_RNDUTEST_OR_RNDDNOTTEST: mpfr_rnd_t -> i32 -> Tot bool

assume val mpfr_IS_LIKE_RNDZ: mpfr_rnd_t -> i32 -> Tot bool

let mpfr_IS_NEG x = I32.(mpfr_SIGN x <^ 0l)
