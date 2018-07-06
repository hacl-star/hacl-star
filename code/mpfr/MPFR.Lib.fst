module MPFR.Lib
open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Buffer
open FStar.UInt64

module I32 = FStar.Int32
module U32 = FStar.UInt32

open MPFR.Maths
open MPFR.Lib.Spec

#set-options "--z3refresh --z3rlimit 5 --max_fuel 1 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 0"

// GENERIC LIBRARY DEFINITIONS
type i32 = FStar.Int32.t
type u32 = FStar.UInt32.t
type u64 = FStar.UInt64.t

let mpfr_SIGN_POS = 1l
let mpfr_SIGN_NEG = -1l

let gmp_NUMB_BITS = 64ul
let mpfr_PREC_MIN = 1ul
val mpfr_PREC_MAX: p:u32{U32.v p = pow2 31 - 1}
let mpfr_PREC_MAX = 0x7ffffffful // Note: 0x7ffffefful in original code

val mpfr_EXP_INVALID: x:i32{I32.v x = pow2 30}
let mpfr_EXP_INVALID = assert_norm(0x40000000 = pow2 30); 0x40000000l
let mpfr_EMIN = I32.(1l -^ mpfr_EXP_INVALID)
let mpfr_EMAX = I32.(mpfr_EXP_INVALID -^ 1l)

type mpfr_sign_t = s:i32{s = mpfr_SIGN_NEG \/ s = mpfr_SIGN_POS}
type mp_limb_t = u64
type mpfr_prec_t = u32
type mpfr_exp_t  = i32
type mpfr_prec_vt = p:mpfr_prec_t{mpfr_PREC_COND (U32.v p)}
type mpfr_exp_vt  = x:mpfr_exp_t{mpfr_EXP_COND (I32.v x)}

let neg_sign (x:mpfr_sign_t) = if x = 1l then -1l else 1l


noeq type mpfr_struct = {
    mpfr_prec: mpfr_prec_t;
    mpfr_sign: mpfr_sign_t;
    mpfr_exp : mpfr_exp_t;
    mpfr_d: buffer mp_limb_t
}

(* First bit is 1 *)
let mpfr_d_val0_cond (m:mp_limb_t): Type =
    v m >= pow2 63
(* Ending bits are 0 *)
let mpfr_d_valn_cond (m:mp_limb_t) (p:mpfr_prec_vt): Type =
    v m % pow2 (prec_to_len (U32.v p) - U32.v p) = 0

let valid_mpfr_struct h (s:mpfr_struct): Type =
    mpfr_PREC_COND (U32.v s.mpfr_prec) /\ mpfr_EXP_COND (I32.v s.mpfr_exp) /\
    (let l = length s.mpfr_d in
    l >= 1 /\ (l - 1) * 64 < U32.v s.mpfr_prec /\ U32.v s.mpfr_prec <= l * 64 /\
    mpfr_d_val0_cond (get h s.mpfr_d 0) /\
    mpfr_d_valn_cond (get h s.mpfr_d (l - 1)) s.mpfr_prec)

(* Conversion to pure struct *)
val to_val: s:Seq.seq u64 -> Tot (n:nat{n < pow2 (Seq.length s * 64)}) (decreases (Seq.length s))
let rec to_val (s:Seq.seq u64) = 
    if Seq.length s = 0 then 0
    else begin
        lemma_pow2_mul 64 ((Seq.length s - 1) * 64);
	lemma_distr_sub_left (pow2 64) 1 (pow2 ((Seq.length s - 1) * 64));
        v (Seq.index s 0) * pow2 ((Seq.length s - 1) * 64) + to_val (Seq.slice s 1 (Seq.length s))
    end

val to_val_rec_lemma: s:Seq.seq u64{Seq.length s > 0} -> Lemma
    (to_val s = v (Seq.index s 0) * pow2 ((Seq.length s - 1) * 64) + to_val (Seq.slice s 1 (Seq.length s)))
let to_val_rec_lemma s = ()

val val0_cond_lemma: s:Seq.seq u64{Seq.length s > 0 /\ mpfr_d_val0_cond (Seq.index s 0)} -> Lemma
    (to_val s >= pow2 (Seq.length s * 64 - 1))
let val0_cond_lemma s =
    to_val_rec_lemma s;
    lemma_pow2_mul 63 ((Seq.length s - 1) * 64);
    lemma_pow2_le (Seq.length s * 64 - 1) (63 + (Seq.length s - 1) * 64)

val valn_cond_lemma: s:Seq.seq u64 -> p:mpfr_prec_vt{prec_to_len (U32.v p) = Seq.length s * 64} -> Lemma
    (requires  (Seq.length s > 0 /\ mpfr_d_valn_cond (Seq.index s (Seq.length s - 1)) p))
    (ensures   (to_val s % pow2 (Seq.length s * 64 - U32.v p) = 0))
    (decreases (U32.v p))
    
let rec valn_cond_lemma s p = 
    admit(); (* It takes very long to go throught, need more robust proof *)
    if U32.v p <= 64 then prec_to_len_lemma (U32.v p) 64 else begin
        lemma_pow2_mul ((Seq.length s - 1) * 64 - (Seq.length s) * 64 + U32.v p) ((Seq.length s) * 64 - U32.v p);
        lemma_multiple_mod (v (Seq.index s 0) * pow2 ((Seq.length s - 1) * 64 - Seq.length s * 64 + U32.v p)) (pow2 (Seq.length s * 64 - U32.v p));
        assert((v (Seq.index s 0) * pow2 ((Seq.length s - 1) * 64)) % pow2 (Seq.length s * 64 - U32.v p) = 0);
	prec_to_len_lemma (U32.v p - 64) ((Seq.length s - 1) * 64);
	valn_cond_lemma (Seq.slice s 1 (Seq.length s)) (U32.(p -^ 64ul));
	assert(to_val (Seq.slice s 1 (Seq.length s)) % pow2 (Seq.length s * 64 - U32.v p) = 0);
        to_val_rec_lemma s;
	lemma_mod_distr (v (Seq.index s 0) * pow2 ((Seq.length s - 1) * 64)) (to_val (Seq.slice s 1 (Seq.length s))) (pow2 (Seq.length s * 64 - U32.v p))
    end

let as_val h (b:buffer mp_limb_t) = to_val (as_seq h b)

(* Convert valid mpfr_struct to mpfr_fr *)
val as_pure: h:mem -> s:mpfr_struct{valid_mpfr_struct h s} ->
    GTot (ps:mpfr_fp{ps.sign = I32.v s.mpfr_sign /\
	             ps.prec = U32.v s.mpfr_prec /\
	             ps.exp  = I32.v s.mpfr_exp  /\
                     ps.limb = as_val h s.mpfr_d /\
		     ps.len  = length s.mpfr_d * 64})
		     
let as_pure h s =
    let sign = I32.v s.mpfr_sign in
    let prec = U32.v s.mpfr_prec in
    let exp  = I32.v s.mpfr_exp  in
    let limb = as_val h s.mpfr_d in
    let l    = length s.mpfr_d in
    prec_to_len_lemma prec (l * 64);
    //! assert(arr_size prec = l * 64);
    val0_cond_lemma (as_seq h s.mpfr_d);
    //! assert(limb >= pow2 (l * 64 - 1));
    nb_of_bits_lemma limb (l * 64);
    //! assert(nb_of_bits limb = l * 64);
    valn_cond_lemma (as_seq h s.mpfr_d) s.mpfr_prec;
    mk_struct sign prec exp limb (l * 64)

(* Struct functions *)
type mpfr_ptr = b:buffer mpfr_struct{length b = 1}

let mk_mpfr_struct p s e d = {
    mpfr_prec = p;
    mpfr_sign = s;
    mpfr_exp = e;
    mpfr_d = d
}

val mpfr_SIGN: x:mpfr_ptr -> Stack mpfr_sign_t 
		(requires (fun h -> live h x))
		(ensures (fun h0 r h1 -> live h1 x /\ h0 == h1 /\
		            (let xm = Seq.index (as_seq h1 x) 0 in
			     r = xm.mpfr_sign)))
let mpfr_SIGN x = 
    let f = x.(0ul) in
    f.mpfr_sign

val mpfr_EXP: x:mpfr_ptr -> Stack mpfr_exp_t 
		(requires (fun h -> live h x))
		(ensures  (fun h0 r h1 -> live h1 x /\ h0 == h1 /\
			      (let xm = Seq.index (as_seq h1 x) 0 in
			      r = xm.mpfr_exp)))
let mpfr_EXP x = 
    let f = x.(0ul) in
    f.mpfr_exp

let mpfr_GET_EXP x = mpfr_EXP x

val mpfr_SET_EXP: x:mpfr_ptr -> e:mpfr_exp_t -> Stack unit
		(requires (fun h -> live h x))
		(ensures  (fun h0 _ h1 -> live h1 x /\ modifies_1 x h0 h1 /\
			      (let xm0 = Seq.index (as_seq h0 x) 0 in
			      let xm = Seq.index (as_seq h1 x) 0 in
			      xm0.mpfr_sign = xm.mpfr_sign /\
			      xm0.mpfr_prec = xm.mpfr_prec /\
			      xm0.mpfr_d == xm.mpfr_d /\ e = xm.mpfr_exp)))
let mpfr_SET_EXP x e = 
    let f = x.(0ul) in
    x.(0ul) <- {f with mpfr_exp = e}


val mpfr_MANT: x:mpfr_ptr -> Stack (buffer mp_limb_t)
		(requires (fun h -> live h x))
		(ensures (fun h0 r h1 -> live h1 x /\ h0 == h1 /\
			    (let xm = Seq.index (as_seq h1 x) 0 in
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
    Tot (r:u64{v r = pow2 (U32.v s) - 1})
let mpfr_LIMB_MASK s =
    let lsh = 1uL <<^ s in
    lemma_pow2_small_mod (U32.v s) 64;
    lsh -^ 1uL
    
val mpfr_LIMB_HIGHBIT: s:u64{v s = pow2 63}
let mpfr_LIMB_HIGHBIT =
    assert_norm(pow2_n #64 63 = v 0x8000000000000000uL);
    0x8000000000000000uL
    
assume val gmpfr_emax: mpfr_exp_t
assume val gmpfr_flags: i32

let mpfr_FLAGS_INEXACT = 8ul

assume val mpfr_RET: i32 -> Tot i32

assume val mpfr_IS_RNDUTEST_OR_RNDDNOTTEST: mpfr_rnd_t -> i32 -> Tot bool

assume val mpfr_IS_LIKE_RNDZ: mpfr_rnd_t -> bool -> Tot bool

let mpfr_IS_NEG x = I32.(mpfr_SIGN x <^ 0l)
