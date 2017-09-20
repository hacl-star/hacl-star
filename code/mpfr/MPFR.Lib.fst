module MPFR.Lib
open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Buffer
open FStar.UInt64

// GENERIC LIBRARY DEFINITIONS


type i32 = FStar.Int32.t
type u32 = FStar.UInt32.t
type u64 = FStar.UInt64.t

type mpfr_prec_t = u32
type mpfr_sign_t = i:i32{i = 1l \/ i = -1l}
type mpfr_exp_t = i:i32{FStar.Int32.v i < pow2 30 /\ FStar.Int32.v i > 1 - pow2 30}
type mpfr_uexp_t = u32
type mp_limb_t = u64

let neg (x:mpfr_sign_t) = if x = 1l then -1l else 1l

noeq type mpfr_struct = {
    mpfr_prec: mpfr_prec_t;
    mpfr_sign: mpfr_sign_t;
    mpfr_exp : mpfr_exp_t;
    mpfr_d: buffer mp_limb_t
}

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


let gmp_NUMB_BITS = 64ul

let mpfr_LIMB_ONE = 1uL

val mpfr_LIMB_MASK: s:u32{FStar.UInt32.v s < 64} -> Tot u64
#set-options "--z3refresh --z3rlimit 100 --log_queries"
let mpfr_LIMB_MASK s =
    let lsh = 1uL <<^ s in
    assume (lsh >^ 0uL);
    lsh -^ 1uL

let mpfr_LIMB_HIGHBIT = 0x8000000000000000uL



assume val gmpfr_emax: mpfr_exp_t
assume val gmpfr_flags: i32

let mpfr_FLAGS_INEXACT = 8ul

assume val mpfr_RET: i32 -> Tot i32

assume val mpfr_IS_RNDUTEST_OR_RNDDNOTTEST: mpfr_rnd_t -> i32 -> Tot bool

assume val mpfr_IS_LIKE_RNDZ: mpfr_rnd_t -> i32 -> Tot bool

let mpfr_IS_NEG x = FStar.Int32.(mpfr_SIGN x <^ 0l)
