module Hacl.Impl.Poly1305.Field32xN

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.IntVector

let lanes = w:width{w == 1 \/ w == 2 \/ w == 4}
let uint64xN (w:lanes) = vec_t U64 w
inline_for_extraction
let zero (w:lanes) = vec_zero U64 w
let felem (w:lanes) = lbuffer (uint64xN w) 5ul
let felem_wide (w:lanes) = lbuffer (uint64xN w) 5ul
let precomp_r (w:lanes) = lbuffer (uint64xN w) 20ul


inline_for_extraction
let mask26 (w:lanes) = vec_load (u64 0x3ffffff) w
inline_for_extraction
let mask14 (w:lanes) = vec_load (u64 0x3fff) w

inline_for_extraction
val create_felem: (w:lanes) -> StackInline (felem w)
		       (requires (fun h -> True))
		       (ensures (fun h0 b h1 -> live h1 b /\ stack_allocated b h0 h1 (Lib.Sequence.create 5 (zero w))))
inline_for_extraction
let create_felem w = create (size 5) (zero w)

inline_for_extraction
val create_wide: (w:lanes) -> StackInline (felem_wide w)
		       (requires (fun h -> True))
		       (ensures (fun h0 b h1 -> live h1 b /\ stack_allocated b h0 h1 (Lib.Sequence.create 5 (zero w))))
inline_for_extraction
let create_wide w = create (size 5) (zero w)


inline_for_extraction
val set_bit: #w:lanes -> f:felem w -> i:size_t{size_v i < 130} -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let set_bit #w f i = 
  let b = u64 1 <<. (i %. size 26) in
  let mask = vec_load b w in
  let fi = f.(i /. size 26) in
  f.(i /. size 26) <- vec_or fi mask

inline_for_extraction
val set_bit128: #w:lanes -> f:felem w -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let set_bit128 #w f = 
  let b = u64 0x1000000 in
  let mask = vec_load  b w in
  let f4 = f.(4ul) in
  f.(size 4) <- vec_or f4 mask

inline_for_extraction
val set_zero: #w:lanes -> f:felem w -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let set_zero #w f = 
    f.(size 0) <- zero w;
    f.(size 1) <- zero w;
    f.(size 2) <- zero w;
    f.(size 3) <- zero w;
    f.(size 4) <- zero w

inline_for_extraction
val copy_felem: #w:lanes -> f1:felem w -> f2:felem w -> Stack unit
                   (requires (fun h -> live h f1 /\ live h f2))
		   (ensures (fun h0 _ h1 -> modifies (loc f1) h0 h1))
let copy_felem #w f1 f2 = 
    f1.(size 0) <- f2.(size 0);
    f1.(size 1) <- f2.(size 1);
    f1.(size 2) <- f2.(size 2);
    f1.(size 3) <- f2.(size 3);
    f1.(size 4) <- f2.(size 4)


#reset-options "--z3rlimit 50"

//[@ CInline]
inline_for_extraction
val fadd: #w:lanes -> out:felem w -> f1:felem w -> f2:felem w -> Stack unit
                   (requires (fun h -> live h f1 /\ live h f2 /\ live h out))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
[@ CInline]
let fadd #w out f1 f2 = 
  let f10 = f1.(size 0) in
  let f11 = f1.(size 1) in
  let f12 = f1.(size 2) in
  let f13 = f1.(size 3) in
  let f14 = f1.(size 4) in
  let f20 = f2.(size 0) in
  let f21 = f2.(size 1) in
  let f22 = f2.(size 2) in
  let f23 = f2.(size 3) in
  let f24 = f2.(size 4) in
  out.(size 0) <- vec_add_mod f10 f20;
  out.(size 1) <- vec_add_mod f11 f21;
  out.(size 2) <- vec_add_mod f12 f22;
  out.(size 3) <- vec_add_mod f13 f23;
  out.(size 4) <- vec_add_mod f14 f24


//[@ CInline]
inline_for_extraction
val smul_felem: #w:lanes -> out:felem_wide w -> u1:uint64xN w -> f2:felem w -> Stack unit
                   (requires (fun h -> live h out /\ live h f2))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
[@ CInline]
let smul_felem #w out u1 f2 = 
  let f20 = f2.(size 0) in
  let f21 = f2.(size 1) in
  let f22 = f2.(size 2) in
  let f23 = f2.(size 3) in
  let f24 = f2.(size 4) in
  out.(size 0) <- vec_mul_mod f20 u1;
  out.(size 1) <- vec_mul_mod f21 u1;
  out.(size 2) <- vec_mul_mod f22 u1;
  out.(size 3) <- vec_mul_mod f23 u1;
  out.(size 4) <- vec_mul_mod f24 u1


//[@ CInline]
inline_for_extraction
val smul_add_felem: #w:lanes -> out:felem_wide w -> u1:uint64xN w -> f2:felem w -> Stack unit
                   (requires (fun h -> live h out /\ live h f2))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
[@ CInline]
let smul_add_felem #w out u1 f2 = 
  let f20 = f2.(size 0) in
  let f21 = f2.(size 1) in
  let f22 = f2.(size 2) in
  let f23 = f2.(size 3) in
  let f24 = f2.(size 4) in
  let o0 = out.(size 0) in
  let o1 = out.(size 1) in
  let o2 = out.(size 2) in
  let o3 = out.(size 3) in
  let o4 = out.(size 4) in
  out.(size 0) <- vec_add_mod o0 (vec_mul_mod f20 u1);
  out.(size 1) <- vec_add_mod o1 (vec_mul_mod f21 u1);
  out.(size 2) <- vec_add_mod o2 (vec_mul_mod f22 u1);
  out.(size 3) <- vec_add_mod o3 (vec_mul_mod f23 u1);
  out.(size 4) <- vec_add_mod o4 (vec_mul_mod f24 u1)

inline_for_extraction
val mul_felem: #w:lanes -> out:felem_wide w -> f1:felem w -> r:felem w -> r5:felem w -> Stack unit
                   (requires (fun h -> live h out /\ live h f1 /\ live h r /\ live h r5))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
[@ CInline]
let mul_felem #w out f1 r r5 = 
  push_frame();
  let tmp = create_felem w in
  smul_felem out f1.(size 0) r;
  tmp.(size 0) <- r5.(size 4);
  tmp.(size 1) <- r.(size 0);
  tmp.(size 2) <- r.(size 1);
  tmp.(size 3) <- r.(size 2);
  tmp.(size 4) <- r.(size 3);
  admit();
  smul_add_felem out f1.(size 1) tmp;
  tmp.(size 0) <- r5.(size 3);
  tmp.(size 1) <- r5.(size 4);
  tmp.(size 2) <- r.(size 0);
  tmp.(size 3) <- r.(size 1);
  tmp.(size 4) <- r.(size 2);
  smul_add_felem out f1.(size 2) tmp;
  tmp.(size 0) <- r5.(size 2);
  tmp.(size 1) <- r5.(size 3);
  tmp.(size 2) <- r5.(size 4);
  tmp.(size 3) <- r.(size 0);
  tmp.(size 4) <- r.(size 1);
  smul_add_felem out f1.(size 3) tmp;
  tmp.(size 0) <- r5.(size 1);
  tmp.(size 1) <- r5.(size 2);
  tmp.(size 2) <- r5.(size 3);
  tmp.(size 3) <- r5.(size 4);
  tmp.(size 4) <- r.(size 0);
  smul_add_felem out f1.(size 4) tmp;
  pop_frame()


inline_for_extraction
val carry26: #w:lanes -> l:uint64xN w -> cin:uint64xN w ->  (r:uint64xN w  * cout:uint64xN w)
let carry26 #w l cin = 
    let l = vec_add_mod l cin in
    (vec_and l (mask26 w), vec_shift_right l (size 26))

inline_for_extraction
val carry26_wide: #w:lanes -> l:uint64xN w -> cin:uint64xN w ->  (r:uint64xN w * cout:uint64xN w)
let carry26_wide #w l cin = carry26 #w l cin

//[@ CInline]
inline_for_extraction
val carry_wide_felem: #w:lanes -> out:felem w -> inp:felem_wide w -> Stack unit
                   (requires (fun h -> live h out /\ live h inp))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
[@ CInline]
let carry_wide_felem #w out inp =
  let i0 = inp.(size 0) in
  let i1 = inp.(size 1) in
  let i2 = inp.(size 2) in
  let i3 = inp.(size 3) in
  let i4 = inp.(size 4) in
  let tmp0,carry = carry26_wide i0 (zero w) in
  let tmp1,carry = carry26_wide i1 carry in
  let tmp2,carry = carry26_wide i2 carry in
  let tmp3,carry = carry26_wide i3 carry in
  let tmp4,carry = carry26_wide i4 carry in
  let tmp0,carry = carry26 tmp0 (vec_smul_mod carry (u64 5)) in
  let tmp1 = vec_add_mod tmp1 carry in
  out.(size 0) <- tmp0;
  out.(size 1) <- tmp1;
  out.(size 2) <- tmp2;
  out.(size 3) <- tmp3; 
  out.(size 4) <- tmp4  

//[@ CInline]
inline_for_extraction
val carry_felem: #w:lanes -> f:felem w -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
[@ CInline]
let carry_felem #w f =
  let f0 = f.(size 0) in
  let f1 = f.(size 1) in
  let f2 = f.(size 2) in
  let f3 = f.(size 3) in
  let f4 = f.(size 4) in
  let tmp0,carry = carry26 f0 (zero w) in 
  let tmp1,carry = carry26 f1 carry in
  let tmp2,carry = carry26 f2 carry in
  let tmp3,carry = carry26 f3 carry in
  let tmp4 = vec_add_mod f4 carry in
  f.(size 0) <- tmp0;
  f.(size 1) <- tmp1;
  f.(size 2) <- tmp2;
  f.(size 3) <- tmp3; 
  f.(size 4) <- tmp4  

//[@ CInline]
inline_for_extraction
val carry_top_felem: #w:lanes -> f:felem w -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
[@ CInline]
let carry_top_felem #w f =
  let f0 = f.(size 0) in
  let f1 = f.(size 1) in
  let f2 = f.(size 2) in
  let f3 = f.(size 3) in
  let f4 = f.(size 4) in
  let tmp4,carry = carry26 f4 (zero w) in
  let tmp0,carry = carry26 f0 (vec_smul_mod carry (u64 5)) in
  let tmp1 = vec_add_mod f1 carry in
  f.(size 0) <- tmp0;
  f.(size 1) <- tmp1;
  f.(size 4) <- tmp4  

inline_for_extraction
val fmul_r: #w:lanes -> acc:felem w -> f1:felem w -> p:precomp_r w -> Stack unit
                   (requires (fun h -> live h acc /\ live h f1 /\ live h p))
		   (ensures (fun h0 _ h1 -> modifies (loc acc) h0 h1))
let fmul_r #w acc f1 p =
  push_frame();
  let r = sub p (size 0) (size 5) in
  let r5 = sub p (size 5) (size 5) in
  let tmp = create_felem w in
  admit();
  mul_felem tmp f1 r r5;
  carry_wide_felem acc tmp;
  pop_frame()

inline_for_extraction
val fadd_mul_r: #w:lanes -> acc:felem w -> f1:felem w -> p:precomp_r w -> Stack unit
                   (requires (fun h -> live h acc /\ live h f1 /\ live h p))
		   (ensures (fun h0 _ h1 -> modifies (loc acc) h0 h1))
let fadd_mul_r #w acc f1 p =
  push_frame();
  let r = sub p (size 0) (size 5) in
  let r5 = sub p (size 5) (size 5) in
  let tmp = create_felem w in
  admit();
  fadd acc acc f1;
  mul_felem tmp acc r r5;
  carry_wide_felem acc tmp;
  pop_frame()


inline_for_extraction
val fmul_rn: #w:lanes -> acc:felem w -> f1:felem w -> p:precomp_r w -> Stack unit
                   (requires (fun h -> live h acc /\ live h f1 /\ live h p))
		   (ensures (fun h0 _ h1 -> modifies (loc acc) h0 h1))
let fmul_rn #w acc f1 p =
  push_frame();
  let rn = sub p (size 10) (size 5) in
  let rn_5 = sub p (size 15) (size 5) in
  let tmp = create_felem w in
  admit();
  mul_felem tmp f1 rn rn_5;
  carry_wide_felem acc tmp;
  pop_frame()

inline_for_extraction
val precompute_shift_reduce: #w:lanes -> f1:felem w -> f2:felem w -> Stack unit
                   (requires (fun h -> live h f1 /\ live h f2))
		   (ensures (fun h0 _ h1 -> modifies (loc f1) h0 h1))
let precompute_shift_reduce #w f1 f2 = 
    let f20 = f2.(size 0) in
    let f21 = f2.(size 1) in
    let f22 = f2.(size 2) in
    let f23 = f2.(size 3) in
    let f24 = f2.(size 4) in
    f1.(size 0) <- vec_smul_mod f20 (u64 5);
    f1.(size 1) <- vec_smul_mod f21 (u64 5);
    f1.(size 2) <- vec_smul_mod f22 (u64 5);
    f1.(size 3) <- vec_smul_mod f23 (u64 5);
    f1.(size 4) <- vec_smul_mod f24 (u64 5)

inline_for_extraction
val fmul_r1_normalize: out:felem 1 -> p:precomp_r 1 -> Stack unit
                   (requires (fun h -> live h out /\ live h p))
		   (ensures (fun h0 _ h1 -> modifies (loc out |+| loc p) h0 h1))
[@ CInline]
let fmul_r1_normalize out p = 
    push_frame();
    admit();
    let tmp = create_felem 1 in
    let r = sub p (size 0) (size 5) in
    let r_5 = sub p (size 5) (size 5) in
    mul_felem tmp out r r_5;
    carry_wide_felem out tmp;
    pop_frame()

inline_for_extraction
val fmul_r2_normalize: out:felem 2 -> p:precomp_r 2 -> Stack unit
                   (requires (fun h -> live h out /\ live h p))
		   (ensures (fun h0 _ h1 -> modifies (loc out |+| loc p) h0 h1))
[@ CInline]
let fmul_r2_normalize out p = 
    push_frame();
    admit();
    let tmp = create_felem 2 in
    let r = sub p (size 0) (size 5) in
    let r2 = sub p (size 10) (size 5) in
    let r2_5 = sub p (size 15) (size 5) in
    r2.(size 0) <- vec_interleave_low r2.(size 0) r.(size 0);
    r2.(size 1) <- vec_interleave_low r2.(size 1) r.(size 1);
    r2.(size 2) <- vec_interleave_low r2.(size 2) r.(size 2);
    r2.(size 3) <- vec_interleave_low r2.(size 3) r.(size 3);
    r2.(size 4) <- vec_interleave_low r2.(size 4) r.(size 4);
    precompute_shift_reduce r2_5 r2;
    mul_felem tmp out r2 r2_5;
    carry_wide_felem out tmp;
    let o0 = out.(0ul) in
    let o1 = out.(1ul) in
    let o2 = out.(2ul) in
    let o3 = out.(3ul) in
    let o4 = out.(4ul) in
    out.(size 0) <- vec_add_mod o0 (vec_interleave_high o0 o0);
    out.(size 1) <- vec_add_mod o1 (vec_interleave_high o1 o1);
    out.(size 2) <- vec_add_mod o2 (vec_interleave_high o2 o2);
    out.(size 3) <- vec_add_mod o3 (vec_interleave_high o3 o3);
    out.(size 4) <- vec_add_mod o4 (vec_interleave_high o4 o4);
    carry_felem out;	 
    carry_top_felem out;	 
    pop_frame()

inline_for_extraction
val fmul_r4_normalize: out:felem 4 -> p:precomp_r 4 -> Stack unit
                   (requires (fun h -> live h out /\ live h p))
		   (ensures (fun h0 _ h1 -> modifies (loc out |+| loc p) h0 h1))
[@ CInline]
let fmul_r4_normalize out p = 
    push_frame();
    admit();
    let r = sub p (size 0) (size 5) in
    let r_5 = sub p (size 5) (size 5) in
    let r4 = sub p (size 10) (size 5) in
    let r4_5 = sub p (size 15) (size 5) in
    let r2 = create_felem 4 in
    let r3 = create_felem 4 in
    let tmp = create_felem 4 in
    mul_felem tmp r r r_5;
    carry_wide_felem r2 tmp;
    mul_felem tmp r2 r r_5;
    carry_wide_felem r3 tmp;
    let h0 = ST.get() in
    loop_nospec #h0 (size 5) r2 
      (fun i -> 
         let v1212 = vec_interleave_low r2.(i) r.(i) in
         let v3434 = vec_interleave_low r4.(i) r3.(i) in
	 let v1234 = vec_interleave_low (cast U128 2 v3434) (cast U128 2 v1212) in
	 r2.(i) <- cast U64 4 v1234);

    let r1234 = r2 in
    let r1234_5 = r3 in
    precompute_shift_reduce r1234_5 r1234;
    mul_felem tmp out r1234 r1234_5;
    carry_wide_felem out tmp;

    loop_nospec #h0 (size 5) out
      (fun i -> 
	 let oi = out.(i) in
	 let v0 = cast U64 4 (vec_interleave_high (cast U128 2 oi) (cast U128 2 oi)) in    
         let v1 = vec_add_mod oi v0 in
	 let v2 = 
	   vec_add_mod v1 (vec_permute4 v1 1ul 1ul 1ul 1ul) in
	 out.(i) <- v2);
    carry_felem out;	 
    carry_top_felem out;	 
    pop_frame()

inline_for_extraction
val fmul_rn_normalize: #w:lanes -> out:felem w -> p:precomp_r w -> Stack unit
                   (requires (fun h -> live h out /\ live h p))
		   (ensures (fun h0 _ h1 -> modifies (loc out |+| loc p) h0 h1))
[@ CInline]
let fmul_rn_normalize #w out p = 
  match w with
  | 1 -> fmul_r1_normalize out p
  | 2 -> fmul_r2_normalize out p
  | 4 -> fmul_r4_normalize out p
  


inline_for_extraction
val load_felem: #w:lanes -> f:felem w -> lo:uint64xN w -> hi:uint64xN w -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let load_felem #w f lo hi =
    f.(size 0) <- vec_and lo (mask26 w);
    f.(size 1) <- vec_and (vec_shift_right lo (size 26)) (mask26 w);
    f.(size 2) <- vec_or (vec_shift_right lo (size 52)) (vec_shift_left (vec_and hi (mask14 w)) (size 12));
    f.(size 3) <- vec_and (vec_shift_right hi (size 14)) (mask26 w);
    f.(size 4) <- vec_shift_right hi (size 40)


inline_for_extraction
val load_precompute_r1: p:precomp_r 1 -> r0:uint64 -> r1:uint64 -> Stack unit
                   (requires (fun h -> live h p))
		   (ensures (fun h0 _ h1 -> modifies (loc p) h0 h1))
let load_precompute_r1 p r0 r1 = 
    push_frame();
    admit();
    let r = sub p (size 0) (size 5) in
    let r5 = sub p (size 5) (size 5) in
    let rn = sub p (size 10) (size 5) in
    let rn_5 = sub p (size 15) (size 5) in
    let r_vec0 = vec_load r0 1 in
    let r_vec1 = vec_load r1 1 in
    load_felem r r_vec0 r_vec1;
    precompute_shift_reduce r5 r;
    copy_felem rn r;
    copy_felem rn_5 r5;
    pop_frame()

inline_for_extraction
val load_precompute_r2: p:precomp_r 2 -> r0:uint64 -> r1:uint64 -> Stack unit
                   (requires (fun h -> live h p))
		   (ensures (fun h0 _ h1 -> modifies (loc p) h0 h1))
let load_precompute_r2 p r0 r1 = 
    push_frame();
    admit();
    let r = sub p (size 0) (size 5) in
    let r5 = sub p (size 5) (size 5) in
    let rn = sub p (size 10) (size 5) in
    let rn_5 = sub p (size 15) (size 5) in
    let r_vec0 = vec_load r0 2 in
    let r_vec1 = vec_load r1 2 in
    load_felem r r_vec0 r_vec1;
    precompute_shift_reduce r5 r;
    let tmp = create_felem 2 in
    mul_felem tmp r r r5;
    carry_wide_felem rn tmp;
    precompute_shift_reduce rn_5 rn;
    pop_frame()

inline_for_extraction
val load_precompute_r4: p:precomp_r 4 -> r0:uint64 -> r1:uint64 -> Stack unit
                   (requires (fun h -> live h p))
		   (ensures (fun h0 _ h1 -> modifies (loc p) h0 h1))
let load_precompute_r4 p r0 r1 = 
    push_frame();
    admit();
    let r = sub p (size 0) (size 5) in
    let r5 = sub p (size 5) (size 5) in
    let rn = sub p (size 10) (size 5) in
    let rn_5 = sub p (size 15) (size 5) in
    let r_vec0 = vec_load r0 4 in
    let r_vec1 = vec_load r1 4 in
    load_felem r r_vec0 r_vec1;
    precompute_shift_reduce r5 r;
    let tmp = create_felem 4 in
    mul_felem tmp r r r5;
    carry_wide_felem rn tmp;
    precompute_shift_reduce rn_5 rn;
    mul_felem tmp rn rn rn_5;
    carry_wide_felem rn tmp;
    precompute_shift_reduce rn_5 rn;
    pop_frame()

inline_for_extraction
val load_precompute_r: #w:lanes -> p:precomp_r w -> r0:uint64 -> r1:uint64 -> Stack unit
                   (requires (fun h -> live h p))
		   (ensures (fun h0 _ h1 -> modifies (loc p) h0 h1))
let load_precompute_r #w p r0 r1 = 
  match w with
  | 1 -> load_precompute_r1 p r0 r1
  | 2 -> load_precompute_r2 p r0 r1
  | 4 -> load_precompute_r4 p r0 r1

inline_for_extraction
val subtract_p: #w:lanes -> f:felem w -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let subtract_p #w f =
  let f0 = f.(size 0) in
  let f1 = f.(size 1) in
  let f2 = f.(size 2) in
  let f3 = f.(size 3) in
  let f4 = f.(size 4) in
  let mh = vec_load (u64 0x3ffffff) w in
  let ml = vec_load (u64 0x3fffffb) w in
  let mask = vec_eq_mask f4 mh in
  let mask = vec_and mask (vec_eq_mask f3 mh) in
  let mask = vec_and mask (vec_eq_mask f2 mh) in
  let mask = vec_and mask (vec_eq_mask f1 mh) in
  let mask = vec_and mask (vec_gte_mask f0 ml) in
  let ph = vec_and mask mh in
  let pl = vec_and mask ml in 
  f.(size 0) <- vec_sub_mod f0 pl;
  f.(size 1) <- vec_sub_mod f1 ph;
  f.(size 2) <- vec_sub_mod f2 ph;
  f.(size 3) <- vec_sub_mod f3 ph;
  f.(size 4) <- vec_sub_mod f4 ph

inline_for_extraction
val reduce_felem: #w:lanes -> f:felem w -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let reduce_felem #w f =
    carry_felem f;
    carry_top_felem f;
    subtract_p f

inline_for_extraction
val load_felem1_le: f:felem 1 -> b:lbuffer uint8 16ul -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let load_felem1_le f b =
    let lo = vec_load_le U64 1 (sub b (size 0) (size 8)) in
    let hi = vec_load_le U64 1 (sub b (size 8) (size 8)) in
    load_felem f lo hi

inline_for_extraction
val load_felem2_le: f:felem 2 -> b:lbuffer uint8 32ul -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let load_felem2_le f b =
    let b1 = vec_load_le U64 2 (sub b (size 0) (size 16)) in
    let b2 = vec_load_le U64 2 (sub b (size 16) (size 16)) in
    let lo = vec_interleave_low b1 b2 in
    let hi = vec_interleave_high b1 b2 in
    load_felem f lo hi

inline_for_extraction
val load_felem4_le: f:felem 4 -> b:lbuffer uint8 64ul -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let load_felem4_le f b =
    let lo0 = vec_load_le U128 2 (sub b (size 0) (size 32)) in
    let hi0 = vec_load_le U128 2 (sub b (size 32) (size 32)) in
    let lo1 = vec_interleave_low lo0 hi0 in
    let hi1 = vec_interleave_high lo0 hi0 in
    let lo2 = cast U64 4 lo1 in
    let hi2 = cast U64 4 hi1 in
    let lo = vec_interleave_low lo2 hi2 in
    let hi = vec_interleave_high lo2 hi2 in
    load_felem f lo hi

inline_for_extraction
val load_felems_le: #w:lanes -> f:felem w -> b:lbuffer uint8 (size w *! 16ul) -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let load_felems_le #w f b = 
  match w with
  | 1 -> load_felem1_le f b
  | 2 -> load_felem2_le f b
  | 4 -> load_felem4_le f b


inline_for_extraction
val load_felem_le: #w:lanes -> f:felem w -> b:lbuffer uint8 16ul -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let load_felem_le #w f b = 
  let lo = uint_from_bytes_le #U64 (sub b 0ul 8ul) in
  let hi = uint_from_bytes_le #U64 (sub b 8ul 8ul) in
  let f0 = vec_load lo w in
  let f1 = vec_load hi w in
  load_felem f f0 f1
  
inline_for_extraction
val store_felem: #w:lanes -> f:felem w -> Stack (uint64xN w * uint64xN w)
                 (requires (fun h -> live h f))
		 (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let store_felem #w f =
    carry_felem f;
    let f0 = f.(0ul) in
    let f1 = f.(1ul) in
    let f2 = f.(2ul) in
    let f3 = f.(3ul) in
    let f4 = f.(4ul) in
    let f0 = vec_or (vec_or f0 (vec_shift_left f1 (size 26))) (vec_shift_left f2 (size 52)) in
    let f1 = vec_or (vec_or (vec_shift_right f2 (size 12)) (vec_shift_left f3 (size 14))) (vec_shift_left f4 (size 40)) in
    (f0,f1)

inline_for_extraction
val store_felem1_le: b:lbuffer uint8 16ul -> f:felem 1 -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc f |+| loc b) h0 h1))
let store_felem1_le b f = 
    let (r0,r1) = store_felem #1 f in
    vec_store_le (sub b (size 0) (size 8)) r0;
    vec_store_le (sub b (size 8) (size 8)) r1

inline_for_extraction
val store_felem2_le: b:lbuffer uint8 16ul -> f:felem 2 -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc f |+| loc b) h0 h1))
let store_felem2_le b f = 
    let (f0,f1) = store_felem #2 f in
    let r0 = vec_interleave_low f0 f1 in
    vec_store_le (sub b (size 0) (size 16)) r0

inline_for_extraction
val store_felem4_le: b:lbuffer uint8 16ul -> f:felem 4 -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc f |+| loc b) h0 h1))
let store_felem4_le b f = 
    push_frame ();
    let (f0,f1) = store_felem #4 f in
    let lo = vec_interleave_low f0 f1 in
    let hi = vec_interleave_high f0 f1 in
    let lo1 = cast U128 2 lo in
    let hi1 = cast U128 2 hi in
    let r0 = vec_interleave_low lo1 hi1 in
    let tmp = create (size 32) (u8 0) in
    vec_store_le (sub tmp (size 0) (size 32)) r0;
    copy b (sub tmp 0ul 16ul);
    pop_frame()

inline_for_extraction
val store_felem_le: #w:lanes -> b:lbuffer uint8 16ul -> f:felem w -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc f |+| loc b) h0 h1))
let store_felem_le #w b f = 
  match w with
  | 1 -> store_felem1_le b f
  | 2 -> store_felem2_le b f
  | 4 -> store_felem4_le b f


