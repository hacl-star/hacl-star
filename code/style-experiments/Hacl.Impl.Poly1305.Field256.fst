module Hacl.Impl.Poly1305.Field256

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open LowStar.Buffer
open Lib.Utils
open Lib.Vec256

let felem = lbuffer vec256 5
let felem_wide = lbuffer vec256 5
let precomp_r = lbuffer vec256 20


inline_for_extraction
let mask26 = vec256_load64 (u64 0x3ffffff)
inline_for_extraction
let mask14 = vec256_load64 (u64 0x3fff)

(*
inline_for_extraction
val create_felem: unit -> StackInline felem 
                   (requires (fun h -> True))
		   (ensures (fun h0 f h1 -> live h1 f 
			    /\ as_nat h1 f == 0))	
*)
inline_for_extraction
let create_felem () = create vec256_zero (size 5)

inline_for_extraction
let create_wide () = create vec256_zero (size 5)


inline_for_extraction
val set_bit: f:felem -> i:size_t{size_v i < 130} -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1))
let set_bit f i = 
  let b = u64 1 <<. size_to_uint32 (i %. size 26) in
  let mask = vec256_load64 b in
  f.(i /. size 26) <- vec256_or f.(i /. size 26) mask

inline_for_extraction
val set_bit128: f:felem -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1))
let set_bit128 f = 
  let b = u64 0x1000000 in
  let mask = vec256_load64  b in
  f.(size 4) <- vec256_or f.(size 4) mask

inline_for_extraction
val set_zero: f:felem -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1))
let set_zero f = 
    f.(size 0) <- vec256_zero;
    f.(size 1) <- vec256_zero;
    f.(size 2) <- vec256_zero;
    f.(size 3) <- vec256_zero;
    f.(size 4) <- vec256_zero

inline_for_extraction
val copy_felem: f1:felem -> f2:felem -> Stack unit
                   (requires (fun h -> live h f1 /\ live h f2))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f1) h0 h1))
let copy_felem f1 f2 = 
    f1.(size 0) <- f2.(size 0);
    f1.(size 1) <- f2.(size 1);
    f1.(size 2) <- f2.(size 2);
    f1.(size 3) <- f2.(size 3);
    f1.(size 4) <- f2.(size 4)

inline_for_extraction
val load_felem: f:felem -> lo:vec256 -> hi:vec256 -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1))
let load_felem f lo0 hi0 =
    let lo1 = vec256_interleave_low128 lo0 hi0 in
    let hi1 = vec256_interleave_high128 lo0 hi0 in
    let lo = vec256_interleave_low64 lo1 hi1 in
    let hi = vec256_interleave_high64 lo1 hi1 in
    f.(size 0) <- vec256_and lo mask26;
    f.(size 1) <- vec256_and (vec256_shift_right64 lo (size 26)) mask26;
    f.(size 2) <- vec256_or (vec256_shift_right64 lo (size 52)) (vec256_shift_left64 (vec256_and hi mask14) (size 12));
    f.(size 3) <- vec256_and (vec256_shift_right64 hi (size 14)) mask26;
    f.(size 4) <- vec256_shift_right64 hi (size 40)



//[@ CInline]
inline_for_extraction
val fadd: out:felem -> f1:felem  -> f2:felem  -> Stack unit
                   (requires (fun h -> live h f1 /\ live h f2 /\ live h out))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer out) h0 h1))
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
  out.(size 0) <- vec256_add64 f10 f20;
  out.(size 1) <- vec256_add64 f11 f21;
  out.(size 2) <- vec256_add64 f12 f22;
  out.(size 3) <- vec256_add64 f13 f23;
  out.(size 4) <- vec256_add64 f14 f24

//[@ CInline]
inline_for_extraction
val smul_felem: out:felem_wide -> u1:vec256 -> f2:felem -> Stack unit
                   (requires (fun h -> live h out /\ live h f2))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer out) h0 h1))
[@ CInline]
let smul_felem out u1 f2 = 
  let f20 = f2.(size 0) in
  let f21 = f2.(size 1) in
  let f22 = f2.(size 2) in
  let f23 = f2.(size 3) in
  let f24 = f2.(size 4) in
  out.(size 0) <- vec256_mul64 f20 u1;
  out.(size 1) <- vec256_mul64 f21 u1;
  out.(size 2) <- vec256_mul64 f22 u1;
  out.(size 3) <- vec256_mul64 f23 u1;
  out.(size 4) <- vec256_mul64 f24 u1


//[@ CInline]
inline_for_extraction
val smul_add_felem: out:felem_wide -> u1:vec256 -> f2:felem -> Stack unit
                   (requires (fun h -> live h out /\ live h f2))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer out) h0 h1))
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
  out.(size 0) <- vec256_add64 o0 (vec256_mul64 f20 u1);
  out.(size 1) <- vec256_add64 o1 (vec256_mul64 f21 u1);
  out.(size 2) <- vec256_add64 o2 (vec256_mul64 f22 u1);
  out.(size 3) <- vec256_add64 o3 (vec256_mul64 f23 u1);
  out.(size 4) <- vec256_add64 o4 (vec256_mul64 f24 u1)

[@ CInline]
val mul_felem: out:felem_wide -> f1:felem -> r:felem -> r5:felem  -> Stack unit
                   (requires (fun h -> live h out /\ live h f1 /\ live h r /\ live h r5))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer out) h0 h1))
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
val carry26: l:vec256 -> cin:vec256 ->  (r:vec256 * cout:vec256)
let carry26 l cin = 
    let l = vec256_add64 l cin in
    (vec256_and l mask26, vec256_shift_right64 l (size 26))

inline_for_extraction
val carry26_wide: l:vec256 -> cin:vec256 ->  (r:vec256 * cout:vec256)
let carry26_wide l cin = carry26 l cin

//[@ CInline]
inline_for_extraction
val carry_wide_felem: out:felem -> inp:felem_wide -> Stack unit
                   (requires (fun h -> live h out /\ live h inp))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer out) h0 h1))
[@ CInline]
let carry_wide_felem out inp =
  let i0 = inp.(size 0) in
  let i1 = inp.(size 1) in
  let i2 = inp.(size 2) in
  let i3 = inp.(size 3) in
  let i4 = inp.(size 4) in
  let tmp0,carry = carry26_wide i0 vec256_zero in
  let tmp1,carry = carry26_wide i1 carry in
  let tmp2,carry = carry26_wide i2 carry in
  let tmp3,carry = carry26_wide i3 carry in
  let tmp4,carry = carry26_wide i4 carry in
  let tmp0,carry = carry26 tmp0 (vec256_smul64 carry (u64 5)) in
  let tmp1 = vec256_add64 tmp1 carry in
  out.(size 0) <- tmp0;
  out.(size 1) <- tmp1;
  out.(size 2) <- tmp2;
  out.(size 3) <- tmp3; 
  out.(size 4) <- tmp4  

//[@ CInline]
inline_for_extraction
val carry_felem: f:felem -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1))
[@ CInline]
let carry_felem f =
  let f0 = f.(size 0) in
  let f1 = f.(size 1) in
  let f2 = f.(size 2) in
  let f3 = f.(size 3) in
  let f4 = f.(size 4) in
  let tmp0,carry = carry26 f0 vec256_zero in
  let tmp1,carry = carry26 f1 carry in
  let tmp2,carry = carry26 f2 carry in
  let tmp3,carry = carry26 f3 carry in
  let tmp4 = vec256_add64 f4 carry in
  f.(size 0) <- tmp0;
  f.(size 1) <- tmp1;
  f.(size 2) <- tmp2;
  f.(size 3) <- tmp3; 
  f.(size 4) <- tmp4  

//[@ CInline]
inline_for_extraction
val carry_top_felem: f:felem -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1))
[@ CInline]
let carry_top_felem f =
  let f0 = f.(size 0) in
  let f1 = f.(size 1) in
  let f2 = f.(size 2) in
  let f3 = f.(size 3) in
  let f4 = f.(size 4) in
  let tmp4,carry = carry26 f4 vec256_zero in
  let tmp0,carry = carry26 f0 (vec256_smul64 carry (u64 5)) in
  let tmp1 = vec256_add64 f1 carry in
  f.(size 0) <- tmp0;
  f.(size 1) <- tmp1;
  f.(size 4) <- tmp4  

inline_for_extraction
val fmul_r: acc:felem -> f1:felem -> p:precomp_r -> Stack unit
                   (requires (fun h -> live h acc /\ live h f1 /\ live h p))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer acc) h0 h1))
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
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer acc) h0 h1))
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
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer acc) h0 h1))
let fmul_rn acc f1 p =
  push_frame();
  let rn = sub p (size 10) (size 5) in
  let rn_5 = sub p (size 15) (size 5) in
  let tmp = create_felem () in
  admit();
  mul_felem tmp f1 rn rn_5;
  carry_wide_felem acc tmp;
  pop_frame()



inline_for_extraction
val precompute_shift_reduce: f1:felem -> f2:felem -> Stack unit
                   (requires (fun h -> live h f1 /\ live h f2))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f1) h0 h1))
let precompute_shift_reduce f1 f2 = 
    f1.(size 0) <- vec256_smul64 f2.(size 0) (u64 5);
    f1.(size 1) <- vec256_smul64 f2.(size 1) (u64 5);
    f1.(size 2) <- vec256_smul64 f2.(size 2) (u64 5);
    f1.(size 3) <- vec256_smul64 f2.(size 3) (u64 5);
    f1.(size 4) <- vec256_smul64 f2.(size 4) (u64 5)


inline_for_extraction
val load_precompute_r: p:precomp_r -> r0:uint64 -> r1:uint64 -> Stack unit
                   (requires (fun h -> live h p))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer p) h0 h1))
let load_precompute_r p r0 r1 = 
    push_frame();
    let r = sub p (size 0) (size 5) in
    let r5 = sub p (size 5) (size 5) in
    let r4 = sub p (size 10) (size 5) in
    let r4_5 = sub p (size 15) (size 5) in
    let r_vec = vec256_load64s r1 r0 r1 r0 in
    load_felem r r_vec r_vec;
    precompute_shift_reduce r5 r;
    let tmp = create_felem () in
    mul_felem tmp r r r5;
    carry_wide_felem r4 tmp;
    precompute_shift_reduce r4_5 r4;
    mul_felem tmp r4 r4 r4_5;
    carry_wide_felem r4 tmp;
    precompute_shift_reduce r4_5 r4;
    pop_frame()

#reset-options "--z3rlimit 50"

inline_for_extraction
val fmul_rn_normalize: out:felem -> p:precomp_r -> Stack unit
                   (requires (fun h -> live h out /\ live h p))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer out) h0 h1))
[@ CInline]
let fmul_rn_normalize out p = 
    push_frame();
    let r = sub p (size 0) (size 5) in
    let r_5 = sub p (size 5) (size 5) in
    let r4 = sub p (size 10) (size 5) in
    let r4_5 = sub p (size 15) (size 5) in
    let r2 = create_felem () in
    let r3 = create_felem () in
    let tmp = create_felem () in
    mul_felem tmp r r r_5;
    carry_wide_felem r2 tmp;
    mul_felem tmp r2 r r_5;
    carry_wide_felem r3 tmp;
    let h0 = ST.get() in
    loop_nospec #h0 (size 5) r2 
      (fun i -> 
         let v1212 = Lib.Vec256.vec256_interleave_low64 r2.(i) r.(i) in
         let v3434 = Lib.Vec256.vec256_interleave_low64 r4.(i) r3.(i) in
	 let v1234 = Lib.Vec256.vec256_interleave_low128 v3434 v1212 in
	 r2.(i) <- v1234);

    let r1234 = r2 in
    let r1234_5 = r3 in
    precompute_shift_reduce r1234_5 r1234;
    mul_felem tmp out r1234 r1234_5;
    carry_wide_felem out tmp;

    loop_nospec #h0 (size 5) out
      (fun i -> 
         let v0 = 
	   Lib.Vec256.vec256_add64 out.(i) (Lib.Vec256.vec256_interleave_high128 out.(i) out.(i)) in    
	 let v1 = 
	   Lib.Vec256.vec256_add64 v0 (Lib.Vec256.vec256_shift_right v0 (size 64)) in
	 out.(i) <- v1);
    carry_felem out;	 
    carry_top_felem out;	 
    pop_frame()

let vec256_eq_mask (a:vec256) (b:vec256) : vec256 
  = Lib.Vec256.vec256_eq64 a b
  
(*  let x = vec256_xor a b in
    let one = vec256_load64 (u64 1) in
    let minus_x = vec256_add64 (vec256_lognot x) one in
    let x_or_minus_x = vec256_or x minus_x in
    let xnx = vec256_shift_right64 x_or_minus_x (size 63) in
    let c = vec256_sub64 xnx one in
    c
*)

let vec256_gte_mask (a:vec256) (b:vec256) : vec256
  = let x = a in
    let y = b in
    let one = vec256_load64 (u64 1) in
    let x_xor_y = vec256_xor x y in
    let x_sub_y = vec256_sub64 x y in
    let x_sub_y_xor_y = vec256_xor x_sub_y y in
    let q = vec256_or x_xor_y x_sub_y_xor_y in
    let x_xor_q = vec256_xor x q in
    let x_xor_q_ = vec256_shift_right64 x_xor_q (size 63) in
    let c = vec256_sub64 x_xor_q_ one in
    c

inline_for_extraction
val subtract_p: f:felem -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1))
let subtract_p f =
  let f0 = f.(size 0) in
  let f1 = f.(size 1) in
  let f2 = f.(size 2) in
  let f3 = f.(size 3) in
  let f4 = f.(size 4) in
  let mh = vec256_load64 (u64 0x3ffffff) in
  let ml = vec256_load64 (u64 0x3fffffb) in
  let mask = vec256_eq_mask f4 mh in
  let mask = vec256_and mask (vec256_eq_mask f3 mh) in
  let mask = vec256_and mask (vec256_eq_mask f2 mh) in
  let mask = vec256_and mask (vec256_eq_mask f1 mh) in
  let mask = vec256_and mask (vec256_gte_mask f0 ml) in
  let ph = vec256_and mask mh in
  let pl = vec256_and mask ml in 
  f.(size 0) <- vec256_sub64 f0 pl;
  f.(size 1) <- vec256_sub64 f1 ph;
  f.(size 2) <- vec256_sub64 f2 ph;
  f.(size 3) <- vec256_sub64 f3 ph;
  f.(size 4) <- vec256_sub64 f4 ph

inline_for_extraction
val reduce_felem: f:felem -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1))
let reduce_felem f =
    carry_felem f;
    carry_top_felem f;
    subtract_p f

inline_for_extraction
val load_felems_le: f:felem -> b:lbytes 64 -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1))
let load_felems_le f b =
    let lo0 = vec256_load_le (sub b (size 0) (size 32)) in
    let hi0 = vec256_load_le (sub b (size 32) (size 32)) in
    load_felem f lo0 hi0

inline_for_extraction
val load_felem_le: f:felem -> b:lbytes 16 -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1))
let load_felem_le f b = 
    let (lo,hi) = load64x2_le b in
    let lo0 = vec256_load64s hi lo hi lo in
    load_felem f lo0 lo0



inline_for_extraction
val store_felem_le: b:lbytes 16 -> f:felem -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer b) h0 h1))
let store_felem_le b f = 
    push_frame();
    carry_felem f;
    let f0 = vec256_or (vec256_or f.(size 0) (vec256_shift_left64 f.(size 1) (size 26))) (vec256_shift_left64 f.(size 2) (size 52)) in
    let f1 = vec256_or (vec256_or (vec256_shift_right64 f.(size 2) (size 12)) (vec256_shift_left64 f.(size 3) (size 14))) (vec256_shift_left64 f.(size 4) (size 40)) in
    let lo = vec256_interleave_low64 f0 f1 in
    let hi = vec256_interleave_high64 f0 f1 in
    let r0 = vec256_interleave_low128 lo hi in
    let tmp = create 0uy (size 32) in
    vec256_store_le tmp r0;
    blit tmp (size 0) b (size 0) (size 16);
    pop_frame()
    
inline_for_extraction
val store_felems_le: b:lbytes 64 -> f:felem -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer b) h0 h1))
let store_felems_le b f = 
    carry_felem f;
    let f0 = vec256_or (vec256_or f.(size 0) (vec256_shift_left64 f.(size 1) (size 26))) (vec256_shift_left64 f.(size 2) (size 52)) in
    let f1 = vec256_or (vec256_or (vec256_shift_right64 f.(size 2) (size 12)) (vec256_shift_left64 f.(size 3) (size 14))) (vec256_shift_left64 f.(size 4) (size 40)) in
    let lo = vec256_interleave_low64 f0 f1 in
    let hi = vec256_interleave_high64 f0 f1 in
    let r0 = vec256_interleave_low128 lo hi in
    let r1 = vec256_interleave_high128 lo hi in
    vec256_store_le (sub b (size 0) (size 32)) r0;
    vec256_store_le (sub b (size 32) (size 32)) r1
