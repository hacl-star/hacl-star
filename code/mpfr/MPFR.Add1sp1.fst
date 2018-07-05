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

module I64 = FStar.Int64
module I32 = FStar.Int32
module U32 = FStar.UInt32
module Spec = MPFR.Add.Spec

(* TODO: Prove it *)
#set-options "--lax --z3refresh --z3rlimit 5 --max_fuel 1 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 0"

assume val mpfr_overflow: x:mpfr_ptr -> rnd_mode:mpfr_rnd_t -> sign:i32 ->
    Stack i32
    (requires (fun h -> live h x /\
                     (let xs = Seq.index (as_seq h x) 0 in
		     let xm = xs.mpfr_d in
		     live h xm /\ disjoint x xm)))
    (ensures  (fun h0 r h1 -> live h1 x /\
                           (let xs = Seq.index (as_seq h1 x) 0 in
			   let xm = xs.mpfr_d in
			   live h1 xm /\ modifies_2 x xm h0 h1)))

noeq type state = {
    sh:mpfr_prec_t;
    bx:i32;
    rb:mp_limb_t;
    sb:mp_limb_t
}

let mk_state sh bx rb sb = {
    sh = sh;
    bx = bx;
    rb = rb;
    sb = sb
}

(* TODO: remove abundent inputs *)
unfold val mpfr_add1sp1_gt_branch1:
    a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
    p:mpfr_prec_t -> sh:mpfr_prec_t -> d:u32 -> mask:mp_limb_t -> Stack state
    (requires (fun h -> valid_mpfr_struct h b /\ valid_mpfr_struct h c /\
		     U32.v p < U32.v gmp_NUMB_BITS - 1 /\
		     U32.v p = U32.v a.mpfr_prec /\
		     U32.v p = U32.v b.mpfr_prec /\ U32.v p = U32.v c.mpfr_prec /\
		     U32.v sh = U32.v gmp_NUMB_BITS - U32.v p /\
		     U32.v d < U32.v sh /\ v mask = pow2 (U32.v sh) - 1 /\
		     I32.v b.mpfr_exp > I32.v c.mpfr_exp /\
		     (let am = a.mpfr_d in
		     let bm = b.mpfr_d in
		     let cm = c.mpfr_d in
		     live h am /\ live h bm /\ live h cm /\
		     length am = 1 /\ length bm = 1 /\ length cm = 1)))
    (ensures  (fun h0 r h1 -> (let am = a.mpfr_d in
		           let bm = b.mpfr_d in
		           let cm = c.mpfr_d in
			   live h1 am /\ live h1 bm /\ live h1 cm /\
		           modifies_1 am h0 h1)))

let mpfr_add1sp1_gt_branch1 a b c p sh d mask =
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
    mk_state sh bx rb sb

unfold val mpfr_add1sp1_gt_branch2:
    a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
    p:mpfr_prec_t -> sh:mpfr_prec_t -> d:u32 -> mask:mp_limb_t -> Stack state
    (requires (fun h -> valid_mpfr_struct h b /\ valid_mpfr_struct h c /\
		     U32.v p < U32.v gmp_NUMB_BITS - 1 /\
		     U32.v p = U32.v a.mpfr_prec /\
		     U32.v p = U32.v b.mpfr_prec /\ U32.v p = U32.v c.mpfr_prec /\
		     U32.v sh = U32.v gmp_NUMB_BITS - U32.v p /\
		     U32.v d < U32.v gmp_NUMB_BITS /\ v mask = pow2 (U32.v sh) - 1 /\
		     I32.v b.mpfr_exp > I32.v c.mpfr_exp /\
		     (let am = a.mpfr_d in
		     let bm = b.mpfr_d in
		     let cm = c.mpfr_d in
		     live h am /\ live h bm /\ live h cm /\
		     length am = 1 /\ length bm = 1 /\ length cm = 1)))
    (ensures  (fun h0 r h1 -> (let am = a.mpfr_d in
		           let bm = b.mpfr_d in
		           let cm = c.mpfr_d in
			   live h1 am /\ live h1 bm /\ live h1 cm /\
		           modifies_1 am h0 h1)))

let mpfr_add1sp1_gt_branch2 a b c p sh d mask =
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

unfold val mpfr_add1sp1_gt_branch3:
    a:mpfr_struct -> b:mpfr_struct -> p:mpfr_prec_t -> sh:mpfr_prec_t -> Stack state
    (requires (fun h -> valid_mpfr_struct h b /\
		     U32.v p < U32.v gmp_NUMB_BITS - 1 /\
		     U32.v p = U32.v a.mpfr_prec /\
		     U32.v p = U32.v b.mpfr_prec /\
		     U32.v sh = U32.v gmp_NUMB_BITS - U32.v p /\
		     (let am = a.mpfr_d in
		     let bm = b.mpfr_d in
		     live h am /\ live h bm /\
		     length am = 1 /\ length bm = 1)))
    (ensures  (fun h0 r h1 -> (let am = a.mpfr_d in
		           let bm = b.mpfr_d in
			   live h1 am /\ live h1 bm /\
		           modifies_1 am h0 h1)))

let mpfr_add1sp1_gt_branch3 a b p sh =
    let ap = a.mpfr_d in
    let bp = a.mpfr_d in
    let bx = b.mpfr_exp in
    ap.(0ul) <- bp.(0ul);
    let rb = 0uL in
    let sb = 1uL in
    mk_state sh bx rb sb

unfold val mpfr_add1sp1_gt: a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
                       p:mpfr_prec_t -> sh:mpfr_prec_t -> Stack state
    (requires (fun h -> valid_mpfr_struct h b /\ valid_mpfr_struct h c /\
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
    (ensures  (fun h0 r h1 -> (let am = a.mpfr_d in
		           let bm = b.mpfr_d in
		           let cm = c.mpfr_d in
			   live h1 am /\ live h1 bm /\ live h1 cm /\
		           modifies_1 am h0 h1)))

let mpfr_add1sp1_gt a b c p sh =
    let bx = b.mpfr_exp in
    let cx = c.mpfr_exp in
    let d = int32_to_uint32 I32.(bx -^ cx) in
    let mask = mpfr_LIMB_MASK sh in
    if U32.(d <^ sh) then mpfr_add1sp1_gt_branch1 a b c p sh d mask
    else if U32.(d <^ gmp_NUMB_BITS) then mpfr_add1sp1_gt_branch2 a b c p sh d mask
    else mpfr_add1sp1_gt_branch3 a b p sh

unfold val mpfr_add1sp1_eq: a:mpfr_struct -> b:mpfr_struct -> c:mpfr_struct ->
                       p:mpfr_prec_t -> sh:mpfr_prec_t -> Stack state
    (requires (fun h -> valid_mpfr_struct h b /\ valid_mpfr_struct h c /\
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
    (ensures  (fun h0 r h1 -> (let am = a.mpfr_d in
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
                       p:mpfr_prec_t -> Stack state
    (requires (fun h -> valid_mpfr_struct h b /\ valid_mpfr_struct h c /\
		     U32.v p < U32.v gmp_NUMB_BITS - 1 /\
		     U32.v p = U32.v a.mpfr_prec /\
		     U32.v p = U32.v b.mpfr_prec /\ U32.v p = U32.v c.mpfr_prec /\
		     (let am = a.mpfr_d in
		     let bm = b.mpfr_d in
		     let cm = c.mpfr_d in
		     live h am /\ live h bm /\ live h cm /\
		     length am = 1 /\ length bm = 1 /\ length cm = 1)))
    (ensures  (fun h0 r h1 -> (let am = a.mpfr_d in
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
    (requires (fun h -> live h a /\
                     (let as = Seq.index (as_seq h a) 0 in
		     let am = as.mpfr_d in
		     live h am /\ disjoint a am)))
    (ensures  (fun h0 r h1 -> h0 == h1))

let truncate a = I32.(0l -^ mpfr_SIGN(a))
    
unfold val add_one_ulp: a:mpfr_ptr -> rnd_mode:mpfr_rnd_t -> st:state -> Stack i32
    (requires (fun h -> live h a /\
                     (let as = Seq.index (as_seq h a) 0 in
		     let am = as.mpfr_d in
		     live h am /\ disjoint a am)))
    (ensures  (fun h0 r h1 -> live h1 a /\
                           (let as = Seq.index (as_seq h1 a) 0 in
			   let am = as.mpfr_d in
			   live h1 am /\ modifies_2 a am h0 h1)))

let add_one_ulp a rnd_mode st =
    let sh = st.sh in
    let bx = st.bx in
    let rb = st.rb in
    let sb = st.sb in
    let ap = mpfr_MANT a in
    ap.(0ul) <- ap.(0ul) +^ (mpfr_LIMB_ONE <<^ sh);
    if ap.(0ul) =^ 0uL then begin
        ap.(0ul) <- mpfr_LIMB_HIGHBIT;
	if I32.(bx +^ 1l <=^ mpfr_EMAX) then begin
	    mpfr_SET_EXP a I32.(bx +^ 1l);
	    mpfr_SIGN a
	end else mpfr_overflow a rnd_mode (mpfr_SIGN a)
    end else mpfr_SIGN a

unfold val mpfr_add1sp1_round: a:mpfr_ptr -> rnd_mode:mpfr_rnd_t -> st:state -> Stack i32
    (requires (fun h -> live h a /\
                     (let as = Seq.index (as_seq h a) 0 in
		     let am = as.mpfr_d in
		     live h am /\ disjoint a am /\ length am = 1)))
    (ensures  (fun h0 r h1 -> live h1 a /\
                           (let as = Seq.index (as_seq h1 a) 0 in
			   let am = as.mpfr_d in
			   live h1 am /\ modifies_2 a am h0 h1)))

let mpfr_add1sp1_round a rnd_mode st =
    let sh = st.sh in
    let bx = st.bx in
    let rb = st.rb in
    let sb = st.sb in
    mpfr_SET_EXP a bx;
    if ((rb =^ 0uL && sb =^ 0uL) || (MPFR_RNDF? rnd_mode)) then 0l
    else if (MPFR_RNDN? rnd_mode) then begin
        let ap = mpfr_MANT a in
        let a0 = ap.(0ul) in
        if (rb =^ 0uL || (sb =^ 0uL && ((a0 &^ (mpfr_LIMB_ONE <<^ sh)) =^ 0uL))) then
	    truncate a
	else add_one_ulp a rnd_mode st
    end else if (mpfr_IS_LIKE_RNDZ rnd_mode I32.((mpfr_SIGN a) =^ -1l)) then truncate a
    else add_one_ulp a rnd_mode st

val mpfr_add1sp1: a:mpfr_ptr -> b:mpfr_ptr -> c:mpfr_ptr ->
                  rnd_mode:mpfr_rnd_t -> p:mpfr_prec_t -> Stack i32
    (requires (fun h -> live h a /\ live h b /\ live h c /\ 
		     (let as = Seq.index (as_seq h a) 0 in
		     let bs = Seq.index (as_seq h b) 0 in
		     let cs = Seq.index (as_seq h c) 0 in
		     valid_mpfr_struct h bs /\ valid_mpfr_struct h cs /\
		     U32.v p < U32.v gmp_NUMB_BITS - 1 /\
		     U32.v p = U32.v as.mpfr_prec /\
		     U32.v p = U32.v bs.mpfr_prec /\ U32.v p = U32.v cs.mpfr_prec /\
		     (let am = as.mpfr_d in
		     let bm = bs.mpfr_d in
		     let cm = cs.mpfr_d in
		     live h am /\ live h bm /\ live h cm /\
		     disjoint a am /\ disjoint a bm /\ disjoint a cm /\
		     disjoint b am /\ disjoint b bm /\ disjoint b cm /\
		     disjoint c am /\ disjoint c bm /\ disjoint c cm /\
		     length am = 1 /\ length bm = 1 /\ length cm = 1))))
    (ensures  (fun h0 r h1 -> live h1 a /\ live h1 b /\ live h1 c /\
		           (let as = Seq.index (as_seq h1 a) 0 in
		           let bs = Seq.index (as_seq h1 b) 0 in
		           let cs = Seq.index (as_seq h1 c) 0 in
		           let am = as.mpfr_d in
		           let bm = bs.mpfr_d in
		           let cm = cs.mpfr_d in
			   live h1 am /\ live h1 bm /\ live h1 cm /\
		           modifies_2 a am h0 h1)))

let mpfr_add1sp1 a b c rnd_mode p =
    let st = mpfr_add1sp1_any a.(0ul) b.(0ul) c.(0ul) p in
    if I32.(st.bx >^ mpfr_EMAX) then begin
        mpfr_overflow a rnd_mode (mpfr_SIGN a)
    end else begin
        mpfr_add1sp1_round a rnd_mode st
    end
