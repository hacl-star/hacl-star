  module MPFR.Add1sp1
  module ST = FStar.HyperStack.ST

  open FStar.HyperStack.All
  open FStar.HyperStack
  open FStar.HyperStack.ST
  open FStar.Buffer
  open MPFR.Lib
  open FStar.UInt64
  open FStar.Int.Cast
  module I64 = FStar.Int64
  module I32 = FStar.Int32
  module U32 = FStar.UInt32
  type u64 = FStar.UInt64.t
  type i64 = FStar.Int64.t

type state = {
  sign: i32;
  ax: i32;
  am: u64;
  rb: u64;
  sb: u64
}

let mk_state s ax am rb sb = {
  sign = s;
  ax = ax;
  am = am;
  rb = rb;
  sb = sb
}

private let mpfr_overflow (rnd:mpfr_rnd_t) (sign:i32) = mk_state sign 0l 0uL 0uL 0uL



val mpfr_add1sp1_gt: bx:i32 -> bm:u64 -> 
	              cx:i32{I32.v bx < pow2 31 - 1 /\ I32.v bx > I32.v cx /\ (I32.v bx - I32.v cx) < pow2 31} -> cm:u64 -> 
		      rnd_mode:mpfr_rnd_t -> 
		      p:mpfr_prec_t{U32.v gmp_NUMB_BITS - U32.v p > 1 /\ 
				    U32.v gmp_NUMB_BITS - U32.v p < 32} -> 
		      Tot state
#set-options "--z3refresh --z3rlimit 20"	      
let mpfr_add1sp1_gt bx bm cx cm rnd_mode p =
  let sh = U32.(gmp_NUMB_BITS -^ p) in
  let sh_high = mpfr_LIMB_ONE <<^ U32.(sh -^ 1ul) in
  let mask = mpfr_LIMB_MASK sh in
  let di = I32.(bx -^ cx) in
  let d = int32_to_uint32 di in
          if U32.(d <^ sh) then 
             let am = bm +%^ (cm >>^ d) in
	     let (am,bx) =  if (am <^ bm)  then 
   		            let bx = I32.(bx +^ 1l) in
			    let am = mpfr_LIMB_HIGHBIT |^ (am >>^ 1ul)  in
			    (am,bx)
	    	       else (am,bx) in
             let rb = am &^ sh_high in
	     let sb = (am &^ mask) ^^ rb in
	     let am = am &^ (lognot mask) in
	      mk_state 0l bx am rb sb
	  else if U32.(d <^ gmp_NUMB_BITS) then
	     let sh = U32.(gmp_NUMB_BITS -^ d) in
	     let sb = cm <<^ sh in
	     let am = bm +%^ (cm >>^ d) in
	     let st = if (am <^ bm) then 
                            let sb = sb |^ (am &^ 1uL) in
                            let am = mpfr_LIMB_HIGHBIT |^ (am >>^ 1ul) in
  			    let bx = I32.(bx +^ 1l) in
  			    mk_state 0l bx am 0uL sb
                      else  mk_state 0l bx am 0uL sb in
	     let ax = st.ax in
	     let am = st.am in
	     let sb = st.sb in
	     let rb = am &^ sh_high in
	     let sb = sb |^ ((am &^ mask) ^^ rb) in
	     let am = am &^ (lognot mask) in
             mk_state 0l ax am rb sb
	  else 
             mk_state 0l bx bm 0uL 1uL


val mpfr_add1sp1_any: bx:i32{I32.v bx < pow2 31 - 1} -> bm:u64 -> 
	              cx:i32{I32.v cx < pow2 31 - 1 /\ 
			     I32.v bx - I32.v cx < pow2 31 /\
			     I32.v cx - I32.v bx < pow2 31} -> cm:u64 -> 
		      rnd_mode:mpfr_rnd_t -> 
		      p:mpfr_prec_t{U32.v gmp_NUMB_BITS - U32.v p > 1 /\ 
				    U32.v gmp_NUMB_BITS - U32.v p < 32} -> 
		      Tot state
let mpfr_add1sp1_any bx bm cx cm rnd_mode p = 
  let sh = U32.(gmp_NUMB_BITS -^ p) in
  let sh_high = mpfr_LIMB_ONE <<^ U32.(sh -^ 1ul) in
    if I32.(bx =^ cx) then
      let am = (bm >>^ 1ul) +^ (cm >>^ 1ul) in
      let rb = am &^ sh_high in
      let am = am ^^ rb in
      let bx = I32.(bx +^ 1l) in
      mk_state 0l bx am rb 0uL
    else if I32.(bx >^ cx) then
	mpfr_add1sp1_gt bx bm cx cm rnd_mode p
    else mpfr_add1sp1_gt cx cm bx bm rnd_mode p

val add_one_ulp: sign:i32 -> ax:i32{I32.v ax < pow2 31 - 1} -> am:u64 -> rnd_mode:mpfr_rnd_t -> sh:u32{U32.v sh < 32} ->
		 Tot state
let add_one_ulp sign ax am rnd_mode sh = 
	 let am = am +%^ (mpfr_LIMB_ONE <<^ sh) in
         if (am =^ 0uL) then
            let am = mpfr_LIMB_HIGHBIT in
            if I32.(ax +^ 1l >^ gmpfr_emax) then
  	        mpfr_overflow rnd_mode sign
            else 
                mk_state sign I32.(ax +^ 1l) am 0uL 0uL
         else mk_state sign ax am 0uL 0uL

assume val neg: i32 -> Tot i32

val mpfr_add1sp1_ : bx:i32{I32.v bx < pow2 31 - 1} -> bm:u64 -> 
	            cx:i32{I32.v cx < pow2 31 - 1 /\ 
			     I32.v bx - I32.v cx < pow2 31 /\
			     I32.v cx - I32.v bx < pow2 31} -> cm:u64 -> 
		    rnd_mode:mpfr_rnd_t -> 
  		    p:mpfr_prec_t{U32.v gmp_NUMB_BITS - U32.v p > 1 /\ 
				    U32.v gmp_NUMB_BITS - U32.v p < 32} -> 
   	            s: mpfr_sign_t ->
		    Tot state 
#set-options "--z3refresh --z3rlimit 100"	      
let mpfr_add1sp1_ bx bm cx cm rnd_mode p sign =
  let sh = U32.(gmp_NUMB_BITS -^ p) in
  let sh_high = mpfr_LIMB_ONE <<^ U32.(sh -^ 1ul) in
  let st = mpfr_add1sp1_any bx bm cx cm rnd_mode p in
  let am = st.am in
  let ax = st.ax in
  let rb = st.rb in
  let sb = st.sb in
  if I32.(ax >^ gmpfr_emax) then
	     mpfr_overflow rnd_mode sign
  else if ((rb =^ 0uL && sb =^ 0uL) || (MPFR_RNDF? rnd_mode)) then
        mk_state sign ax am 0uL 0uL
  else if (MPFR_RNDN? rnd_mode) then
	 if ((rb =^ 0uL || (sb =^ 0uL && (am &^ (mpfr_LIMB_ONE <<^ sh)) =^ 0uL))) then (
	     let ns = neg sign in
             mk_state ns ax am 0uL 0uL)
          else (add_one_ulp sign ax am rnd_mode sh)
  else if (mpfr_IS_LIKE_RNDZ rnd_mode sign) then (
             let ns = neg sign in
             mk_state ns ax am 0uL 0uL)
  else (add_one_ulp sign ax am rnd_mode sh)
  

val mpfr_add1sp1: a:mpfr_ptr -> b:mpfr_ptr -> c:mpfr_ptr -> 
    		  rnd_mode:mpfr_rnd_t -> p:mpfr_prec_t -> Stack i32 
		  (requires (fun h -> live h a /\ live h b /\ live h c /\ 
			     U32.(p <^ gmp_NUMB_BITS)))
		  (ensures  (fun h0 r h1 -> live h1 a /\ live h1 b /\ live h1 c /\ modifies_1 a h1 h1))
let mpfr_add1sp1 a b c rnd_mode p = 
    let sign = mpfr_SIGN a in
    let bx = mpfr_GET_EXP b in
    let bm = mpfr_MANT b in
    let cx = mpfr_GET_EXP c in
    let cm = mpfr_MANT c in
    let b0 = bm.(0ul) in
    let c0 = cm.(0ul) in
    let st = mpfr_add1sp1_ bx b0 cx c0 rnd_mode p sign in
    let a0 = st.am in
    let as = st.sign in
    let ax = st.ax in
    let am = mpfr_MANT a in
    am.(0ul) <- a0;
    let ap = mk_mpfr_struct p as ax am in
    a.(0ul) <- ap;
    as
    

