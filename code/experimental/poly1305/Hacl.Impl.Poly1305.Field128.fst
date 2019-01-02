module Hacl.Impl.Poly1305.Field128

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.IntVector

let uint64x2 = vec_t U64 2
let zero = vec_zero U64 2
let felem = lbuffer uint64x2 5ul
let felem_wide = lbuffer uint64x2 5ul
let precomp_r = lbuffer uint64x2 20ul


inline_for_extraction
let mask26 = vec_load (u64 0x3ffffff) 2
inline_for_extraction
let mask14 = vec_load (u64 0x3fff) 2

inline_for_extraction
val create_felem: unit -> StackInline felem
		       (requires (fun h -> True))
		       (ensures (fun h0 b h1 -> live h1 b /\ stack_allocated b h0 h1 (Lib.Sequence.create 5 zero)))
inline_for_extraction
let create_felem () = create (size 5) zero

inline_for_extraction
val create_wide: unit -> StackInline felem_wide
		       (requires (fun h -> True))
		       (ensures (fun h0 b h1 -> live h1 b /\ stack_allocated b h0 h1 (Lib.Sequence.create 5 zero)))
inline_for_extraction
let create_wide () = create (size 5) zero


inline_for_extraction
val set_bit: f:felem -> i:size_t{size_v i < 130} -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let set_bit f i = 
  let b = u64 1 <<. (i %. size 26) in
  let mask = vec_load b 2 in
  let fi = f.(i /. size 26) in
  f.(i /. size 26) <- vec_or fi mask

inline_for_extraction
val set_bit128: f:felem -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let set_bit128 f = 
  let b = u64 0x1000000 in
  let mask = vec_load  b 2 in
  let f4 = f.(4ul) in
  f.(size 4) <- vec_or f4 mask

inline_for_extraction
val set_zero: f:felem -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let set_zero f = 
    f.(size 0) <- zero;
    f.(size 1) <- zero;
    f.(size 2) <- zero;
    f.(size 3) <- zero;
    f.(size 4) <- zero

inline_for_extraction
val copy_felem: f1:felem -> f2:felem -> Stack unit
                   (requires (fun h -> live h f1 /\ live h f2))
		   (ensures (fun h0 _ h1 -> modifies (loc f1) h0 h1))
let copy_felem f1 f2 = 
    f1.(size 0) <- f2.(size 0);
    f1.(size 1) <- f2.(size 1);
    f1.(size 2) <- f2.(size 2);
    f1.(size 3) <- f2.(size 3);
    f1.(size 4) <- f2.(size 4)

inline_for_extraction
val load_felem: f:felem -> lo:uint64x2 -> hi:uint64x2 -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let load_felem f b1 b2 =
    let lo = vec_interleave_low b1 b2 in
    let hi = vec_interleave_high b1 b2 in
    f.(size 0) <- vec_and lo mask26;
    f.(size 1) <- vec_and (vec_shift_right lo (size 26)) mask26;
    f.(size 2) <- vec_or (vec_shift_right lo (size 52)) (vec_shift_left (vec_and hi mask14) (size 12));
    f.(size 3) <- vec_and (vec_shift_right hi (size 14)) mask26;
    f.(size 4) <- vec_shift_right hi (size 40)


#reset-options "--z3rlimit 50"

//[@ CInline]
inline_for_extraction
val fadd: out:felem -> f1:felem  -> f2:felem  -> Stack unit
                   (requires (fun h -> live h f1 /\ live h f2 /\ live h out))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
[@ CInline]
let fadd out f1 f2 = 
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
val smul_felem: out:felem_wide -> u1:uint64x2 -> f2:felem -> Stack unit
                   (requires (fun h -> live h out /\ live h f2))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
[@ CInline]
let smul_felem out u1 f2 = 
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
val smul_add_felem: out:felem_wide -> u1:uint64x2 -> f2:felem -> Stack unit
                   (requires (fun h -> live h out /\ live h f2))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
[@ CInline]
let smul_add_felem out u1 f2 = 
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
val mul_felem: out:felem_wide -> f1:felem -> r:felem -> r5:felem  -> Stack unit
                   (requires (fun h -> live h out /\ live h f1 /\ live h r /\ live h r5))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
[@ CInline]
let mul_felem out f1 r r5 = 
  push_frame();
  let tmp = create_felem () in
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
val carry26: l:uint64x2 -> cin:uint64x2 ->  (r:uint64x2 * cout:uint64x2)
let carry26 l cin = 
    let l = vec_add_mod l cin in
    (vec_and l mask26, vec_shift_right l (size 26))

inline_for_extraction
val carry26_wide: l:uint64x2 -> cin:uint64x2 ->  (r:uint64x2 * cout:uint64x2)
let carry26_wide l cin = carry26 l cin

//[@ CInline]
inline_for_extraction
val carry_wide_felem: out:felem -> inp:felem_wide -> Stack unit
                   (requires (fun h -> live h out /\ live h inp))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
[@ CInline]
let carry_wide_felem out inp =
  let i0 = inp.(size 0) in
  let i1 = inp.(size 1) in
  let i2 = inp.(size 2) in
  let i3 = inp.(size 3) in
  let i4 = inp.(size 4) in
  let tmp0,carry = carry26_wide i0 zero in
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
val carry_felem: f:felem -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
[@ CInline]
let carry_felem f =
  let f0 = f.(size 0) in
  let f1 = f.(size 1) in
  let f2 = f.(size 2) in
  let f3 = f.(size 3) in
  let f4 = f.(size 4) in
  let tmp0,carry = carry26 f0 zero in
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
val carry_top_felem: f:felem -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
[@ CInline]
let carry_top_felem f =
  let f0 = f.(size 0) in
  let f1 = f.(size 1) in
  let f2 = f.(size 2) in
  let f3 = f.(size 3) in
  let f4 = f.(size 4) in
  let tmp4,carry = carry26 f4 zero in
  let tmp0,carry = carry26 f0 (vec_smul_mod carry (u64 5)) in
  let tmp1 = vec_add_mod f1 carry in
  f.(size 0) <- tmp0;
  f.(size 1) <- tmp1;
  f.(size 4) <- tmp4  

inline_for_extraction
val fmul_r: acc:felem -> f1:felem -> p:precomp_r -> Stack unit
                   (requires (fun h -> live h acc /\ live h f1 /\ live h p))
		   (ensures (fun h0 _ h1 -> modifies (loc acc) h0 h1))
let fmul_r acc f1 p =
  push_frame();
  let r = sub p (size 0) (size 5) in
  let r5 = sub p (size 5) (size 5) in
  let tmp = create_felem () in
  admit();
  mul_felem tmp f1 r r5;
  carry_wide_felem acc tmp;
  pop_frame()

inline_for_extraction
val fadd_mul_r: acc:felem -> f1:felem -> p:precomp_r -> Stack unit
                   (requires (fun h -> live h acc /\ live h f1 /\ live h p))
		   (ensures (fun h0 _ h1 -> modifies (loc acc) h0 h1))
let fadd_mul_r acc f1 p =
  push_frame();
  let r = sub p (size 0) (size 5) in
  let r5 = sub p (size 5) (size 5) in
  let tmp = create_felem () in
  admit();
  fadd acc acc f1;
  mul_felem tmp acc r r5;
  carry_wide_felem acc tmp;
  pop_frame()


inline_for_extraction
val fmul_rn: acc:felem -> f1:felem -> p:precomp_r -> Stack unit
                   (requires (fun h -> live h acc /\ live h f1 /\ live h p))
		   (ensures (fun h0 _ h1 -> modifies (loc acc) h0 h1))
let fmul_rn acc f1 p =
  push_frame();
  let r2 = sub p (size 10) (size 5) in
  let r2_5 = sub p (size 15) (size 5) in
  let tmp = create_felem () in
  admit();
  mul_felem tmp f1 r2 r2_5;
  carry_wide_felem acc tmp;
  pop_frame()

inline_for_extraction
val precompute_shift_reduce: f1:felem -> f2:felem -> Stack unit
                   (requires (fun h -> live h f1 /\ live h f2))
		   (ensures (fun h0 _ h1 -> modifies (loc f1) h0 h1))
let precompute_shift_reduce f1 f2 = 
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
val fmul_rn_normalize: out:felem -> p:precomp_r -> Stack unit
                   (requires (fun h -> live h out /\ live h p))
		   (ensures (fun h0 _ h1 -> modifies (loc out |+| loc p) h0 h1))
[@ CInline]
let fmul_rn_normalize out p = 
    push_frame();
    admit();
    let tmp = create_felem () in
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
val load_precompute_r: p:precomp_r -> r0:uint64 -> r1:uint64 -> Stack unit
                   (requires (fun h -> live h p))
		   (ensures (fun h0 _ h1 -> modifies (loc p) h0 h1))
let load_precompute_r p r0 r1 = 
    push_frame();
    let r = sub p (size 0) (size 5) in
    let r5 = sub p (size 5) (size 5) in
    let r2 = sub p (size 10) (size 5) in
    let r2_5 = sub p (size 15) (size 5) in
    let r_vec = vec_load2 r1 r0 in
    load_felem r r_vec r_vec;
    precompute_shift_reduce r5 r;
    let tmp = create_felem () in
    mul_felem tmp r r r5;
    carry_wide_felem r2 tmp;
    precompute_shift_reduce r2_5 r2;
    pop_frame()

inline_for_extraction
val subtract_p: f:felem -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let subtract_p f =
  let f0 = f.(size 0) in
  let f1 = f.(size 1) in
  let f2 = f.(size 2) in
  let f3 = f.(size 3) in
  let f4 = f.(size 4) in
  let mh = vec_load (u64 0x3ffffff) 2 in
  let ml = vec_load (u64 0x3fffffb) 2 in
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
val reduce_felem: f:felem -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let reduce_felem f =
    carry_felem f;
    carry_top_felem f;
    subtract_p f

inline_for_extraction
val load_felems_le: f:felem -> b:lbuffer uint8 32ul -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let load_felems_le f b =
    let b1 = vec_load_le U64 2 (sub b (size 0) (size 16)) in
    let b2 = vec_load_le U64 2 (sub b (size 16) (size 16)) in
    load_felem f b1 b2

inline_for_extraction
val load_felem_le: f:felem -> b:lbuffer uint8 16ul -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let load_felem_le f b = 
    let b = vec_load_le U64 2 b in
    load_felem f b b


inline_for_extraction
val store_felems_le: b:lbuffer uint8 32ul -> f:felem -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc b |+| loc f) h0 h1))
let store_felems_le b f = 
    carry_felem f;
    let f0 = f.(0ul) in
    let f1 = f.(1ul) in
    let f2 = f.(2ul) in
    let f3 = f.(3ul) in
    let f4 = f.(4ul) in
    let f0 = vec_or (vec_or f0 (vec_shift_left f1 (size 26))) (vec_shift_left f2 (size 52)) in
    let f1 = vec_or (vec_or (vec_shift_right f2 (size 12)) (vec_shift_left f3 (size 14))) (vec_shift_left f4 (size 40)) in
    let r0 = vec_interleave_low f0 f1 in
    let r1 = vec_interleave_high f0 f1 in
    vec_store_le (sub b (size 0) (size 16)) r0;
    vec_store_le (sub b (size 16) (size 16)) r1

inline_for_extraction
val store_felem_le: b:lbuffer uint8 16ul -> f:felem -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc b |+| loc f) h0 h1))
let store_felem_le b f = 
    carry_felem f;
    let f0 = f.(0ul) in
    let f1 = f.(1ul) in
    let f2 = f.(2ul) in
    let f3 = f.(3ul) in
    let f4 = f.(4ul) in
    let f0 = vec_or (vec_or f0 (vec_shift_left f1 (size 26))) (vec_shift_left f2 (size 52)) in
    let f1 = vec_or (vec_or (vec_shift_right f2 (size 12)) (vec_shift_left f3 (size 14))) (vec_shift_left f4 (size 40)) in
    let r0 = vec_interleave_low f0 f1 in
    vec_store_le b r0
    
