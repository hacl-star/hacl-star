module MPFR.NG

module P = FStar.Pointer

let mpfr_prec_t : P.typ = P.TBase P.TUInt32
let mpfr_sign_t : P.typ = P.TBase P.TInt32
let mpfr_sign_t_prop (i: P.type_of_typ mpfr_sign_t) : GTot Type0 =
  i = 1l \/ i = -1l
let mpfr_exp_t  : P.typ = P.TBase P.TInt32
let mpfr_exp_t_prop (i: P.type_of_typ mpfr_exp_t) : GTot Type0 =
  Int32.v i < pow2 30 /\ Int32.v i > 1 - pow2 30
let mpfr_uexp_t : P.typ = P.TBase P.TUInt32
let mp_limb_t : P.typ = P.TBase P.TUInt64

let mpfr_struct : P.struct_typ = [
  "mpfr_prec", mpfr_prec_t;
  "mpfr_sign", mpfr_sign_t;
  "mpfr_exp", mpfr_exp_t;
  "mpfr_d", P.TBuffer mp_limb_t;
]

let mpfr_t : P.typ = P.TStruct mpfr_struct

let mpfr_ptr : Type0 = P.pointer mpfr_t

let mpfr_t_pure_inv
//(v: P.type_of_typ mpfr_t)
  (v: P.struct mpfr_struct)
: GTot Type0
= mpfr_sign_t_prop (P.struct_sel v "mpfr_sign") /\
  mpfr_exp_t_prop (P.struct_sel v "mpfr_exp") /\ (
  let b : P.buffer mp_limb_t = P.struct_sel v "mpfr_d" in (
  UInt32.v (P.buffer_length b) >= 1
  ))

module HS = FStar.HyperStack

let mpfr_ptr_st_inv
  (h: HS.mem)
  (p: mpfr_ptr)
: GTot Type0
= P.readable h p /\
  mpfr_t_pure_inv (P.gread h p) /\ (
  let b : P.buffer mp_limb_t = P.gread h (P.gfield p "mpfr_d") in (
  P.buffer_readable h b /\
  P.loc_disjoint (P.loc_pointer p) (P.loc_buffer b) /\ (
  let s = P.buffer_as_seq h b in
  let first = Seq.index s 0 in True (*
  FStar.UInt64.(first >>^ 63ul) == 1uL
  *))))

let loc_mpfr (h: HS.mem) (p: mpfr_ptr) : GTot P.loc =
  let b : P.buffer mp_limb_t = P.gread h (P.gfield p "mpfr_d") in
  P.loc_union (P.loc_pointer p) (P.loc_buffer b)

type mpfr_rnd_t = 
   | MPFR_RNDN 
   | MPFR_RNDZ
   | MPFR_RNDU
   | MPFR_RNDD
   | MPFR_RNDA
   | MPFR_RNDF
   | MPFR_RNDNA

let gmp_NUMB_BITS = 64ul

module HST = FStar.HyperStack.ST

val mpfr_EXP: x:mpfr_ptr -> HST.Stack (P.type_of_typ mpfr_exp_t)
		(requires (fun h -> mpfr_ptr_st_inv h x ))
		(ensures (fun h0 r h1 -> h1 == h0 /\
			    (let xm : P.struct mpfr_struct = P.gread h0 x in (
			     r == P.struct_sel xm "mpfr_exp" /\
			     mpfr_exp_t_prop r
	         ))))

let mpfr_EXP x = 
  P.read (P.field x "mpfr_exp")

val mpfr_SET_EXP: x:mpfr_ptr -> e:P.type_of_typ mpfr_exp_t -> HST.Stack unit
		(requires (fun h -> mpfr_ptr_st_inv h x /\ mpfr_exp_t_prop e ))
		(ensures (fun h0 _ h1 -> mpfr_ptr_st_inv h1 x /\
		  P.modifies (P.loc_pointer (P.gfield x "mpfr_exp")) h0 h1 /\
		  P.gread h1 (P.gfield x "mpfr_exp") == e
		))

let mpfr_SET_EXP x e = 
  P.write (P.field x "mpfr_exp") e

val mpfr_SIGN: x:mpfr_ptr -> HST.Stack (P.type_of_typ mpfr_sign_t)
		(requires (fun h -> mpfr_ptr_st_inv h x))
		(ensures (fun h0 r h1 -> h1 == h0 /\
		            (let xm : P.struct mpfr_struct = P.gread h0 x in
			     r == P.struct_sel xm "mpfr_sign" /\
			     mpfr_sign_t_prop r
			     )))
let mpfr_SIGN x = 
  P.read (P.field x "mpfr_sign")

val mpfr_MANT: x:mpfr_ptr -> HST.Stack (P.buffer mp_limb_t)
		(requires (fun h -> mpfr_ptr_st_inv h x))
		(ensures (fun h0 r h1 -> h1 == h0 /\
		            (let xm : P.struct mpfr_struct = P.gread h0 x in
			     r == P.struct_sel xm "mpfr_d"
			     )))
let mpfr_MANT x = 
  P.read (P.field x "mpfr_d")

type i32 = FStar.Int32.t
type u32 = FStar.UInt32.t
type u64 = FStar.UInt64.t

type state = {
  sign: i32;
  ax: i32;
  am: u64;
  rb: u64;
  sb: u64
}

  module I64 = FStar.Int64
  module I32 = FStar.Int32
  module U32 = FStar.UInt32

assume
val mpfr_add1sp1_ : bx:i32{I32.v bx < pow2 31 - 1} -> bm:u64 -> 
	            cx:i32{I32.v cx < pow2 31 - 1 /\ 
			     I32.v bx - I32.v cx < pow2 31 /\
			     I32.v cx - I32.v bx < pow2 31} -> cm:u64 -> 
		    rnd_mode:mpfr_rnd_t -> 
  		    p:P.type_of_typ mpfr_prec_t{U32.v gmp_NUMB_BITS - U32.v p > 1 /\ 
				    U32.v gmp_NUMB_BITS - U32.v p < 32} -> 
   	            s: P.type_of_typ mpfr_sign_t ->
		    Pure state 
		    (requires True)
		    (ensures (fun x -> mpfr_exp_t_prop x.ax))

#set-options "--z3rlimit 16"

val mpfr_add1sp1: a:mpfr_ptr -> b:mpfr_ptr -> c:mpfr_ptr -> 
    		  rnd_mode:mpfr_rnd_t -> p:P.type_of_typ mpfr_prec_t -> HST.Stack Int32.t
		  (requires (fun h -> 
		    mpfr_ptr_st_inv h a /\
		    mpfr_ptr_st_inv h b /\
		    mpfr_ptr_st_inv h c /\
		    (P.loc_disjoint (loc_mpfr h a) (loc_mpfr h b) \/ a == b) /\
		    (P.loc_disjoint (loc_mpfr h a) (loc_mpfr h c) \/ a == c) /\
			     (let am : P.struct mpfr_struct = P.gread h a in
			     let bm : P.struct mpfr_struct = P.gread h b in
			     let cm : P.struct mpfr_struct = P.gread h c in
			     let a0 : P.buffer mp_limb_t = P.struct_sel am "mpfr_d" in
			     let b0 : P.buffer mp_limb_t = P.struct_sel bm "mpfr_d" in
			     let c0 : P.buffer mp_limb_t = P.struct_sel cm "mpfr_d" in
			     UInt32.v (P.buffer_length a0) == 1 /\
			     UInt32.v (P.buffer_length b0) == 1 /\
			     UInt32.v (P.buffer_length c0) == 1 /\
			     UInt32.v gmp_NUMB_BITS - UInt32.v p > 1 /\ 
   			     UInt32.v gmp_NUMB_BITS - UInt32.v p < 32)))
		  (ensures  (fun h0 r h1 -> 
		    mpfr_ptr_st_inv h1 a /\
		    mpfr_ptr_st_inv h1 b /\
		    mpfr_ptr_st_inv h1 c /\
		    P.modifies (loc_mpfr h0 a) h0 h1 /\ (
		    let b0 : P.buffer mp_limb_t = P.gread h0 (P.gfield a "mpfr_d") in
		    let b1 : P.buffer mp_limb_t = P.gread h1 (P.gfield a "mpfr_d") in (
		    b0 == b1
		  ))))

let mpfr_add1sp1 a b c rnd_mode p = 
    let sign = mpfr_SIGN a in
    let bx = mpfr_EXP b in
    let bm = mpfr_MANT b in
    let cx = mpfr_EXP c in
    let cm = mpfr_MANT c in
    let b0 = P.read_buffer bm 0ul in
    let c0 = P.read_buffer cm 0ul in
    let st = mpfr_add1sp1_ bx b0 cx c0 rnd_mode p sign in
    let a0 = st.am in
    let as = st.sign in
    let ax = st.ax in
    let am = mpfr_MANT a in
    P.write_buffer am 0ul a0;
    mpfr_SET_EXP a ax;
    as
