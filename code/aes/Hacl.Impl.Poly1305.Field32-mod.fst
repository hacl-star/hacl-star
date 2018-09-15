module Hacl.Impl.Poly1305.Field32

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open LowStar.Buffer
open Lib.Utils

let felem = lbuffer uint32 5
let felem_wide = lbuffer uint64 5
let precomp_r = lbuffer uint32 10

noextract 
val as_nat: h:mem -> e:felem -> GTot nat 
let as_nat h e = 
    let s = as_seq h e in
    let s0 =  uint_v (s.[size 0]) in
    let s1 =  uint_v (s.[size 1]) in
    let s2 =  uint_v (s.[size 2]) in
    let s3 =  uint_v (s.[size 3]) in
    let s4 =  uint_v (s.[size 4]) in
    let ( * ) = op_Multiply in
    s0 + (s1 * pow2 26) + (s2 * pow2 52) + (s3 * pow2 78) + (s4 * pow2 104)

noextract 
val wide_as_nat: h:mem -> e:felem_wide -> GTot nat 
let wide_as_nat h e = 
    let s = as_seq h e in
    let s0 =  uint_v (s.[size 0]) in
    let s1 =  uint_v (s.[size 1]) in
    let s2 =  uint_v (s.[size 2]) in
    let s3 =  uint_v (s.[size 3]) in
    let s4 =  uint_v (s.[size 4]) in
    let ( * ) = op_Multiply in
    s0 + (s1 * pow2 26) + (s2 * pow2 52) + (s3 * pow2 78) + (s4 * pow2 104)


(*
inline_for_extraction
val create_felem: unit -> StackInline felem 
                   (requires (fun h -> True))
		   (ensures (fun h0 f h1 -> live h1 f 
			    /\ as_nat h1 f == 0))	
*)
inline_for_extraction
let create_felem () = create (u32 0) (size 5)

inline_for_extraction
let mask26 = u32 0x3ffffff

inline_for_extraction
val load_felem: f:felem -> lo:uint64 -> hi:uint64 -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1))
let load_felem f lo hi = 
    f.(size 0) <- (to_u32 lo) &. mask26;
    f.(size 1) <- (to_u32 (lo >>. u32 26)) &. mask26;
    f.(size 2) <- (to_u32 (lo >>. u32 52)) ^. (((to_u32 hi &. u32 0x3fff) <<. u32 12));
    f.(size 3) <- (to_u32 (hi >>. u32 14)) &. mask26;
    f.(size 4) <- to_u32 (hi >>. u32 40)


inline_for_extraction
val store_felem: f:felem -> Stack (uint64 * uint64)
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> h0 == h1))
let store_felem f = 
    let f0 = to_u64 f.(size 0) |. ((to_u64 f.(size 1)) <<. u32 26) |. ((to_u64 f.(size 2)) <<. u32 52) in
    let f1 = ((to_u64 f.(size 2)) >>. u32 12) |. ((to_u64 f.(size 3)) <<. u32 14) |. ((to_u64 f.(size 4)) <<. u32 40) in
    (f0,f1)


inline_for_extraction
val set_bit: f:felem -> i:size_t{size_v i < 130} -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1))
let set_bit f i = 
  f.(i /. size 26) <- f.(i /. size 26) |. (u32 1 <<. size_to_uint32 (i %. size 26))

inline_for_extraction
val set_bit128: f:felem -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1))
let set_bit128 f = 
    f.(size 4) <- f.(size 4) |. u32 0x1000000

inline_for_extraction
val set_zero: f:felem -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1))
let set_zero f = 
    f.(size 0) <- u32 0;
    f.(size 1) <- u32 0;
    f.(size 2) <- u32 0;
    f.(size 3) <- u32 0;
    f.(size 4) <- u32 0

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
val precompute_shift_reduce: f1:felem -> f2:felem -> Stack unit
                   (requires (fun h -> live h f1 /\ live h f2))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f1) h0 h1))
let precompute_shift_reduce f1 f2 = 
    f1.(size 0) <- f2.(size 0) *. u32 5;
    f1.(size 1) <- f2.(size 1) *. u32 5;
    f1.(size 2) <- f2.(size 2) *. u32 5;
    f1.(size 3) <- f2.(size 3) *. u32 5;
    f1.(size 4) <- f2.(size 4) *. u32 5


inline_for_extraction
val load_precompute_r: pre:precomp_r -> r0:uint64 -> r1:uint64 -> Stack unit
                   (requires (fun h -> live h pre))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer pre) h0 h1))
let load_precompute_r r0 r1 = 
    let r = sub pre (size 0) (size 5) in
    let r5 = sub pre (size 5) (size 5) in
    load_felem r r0 r1;
    r5.(size 0) <- r.(size 0) *. u32 5;
    r5.(size 1) <- r.(size 1) *. u32 5;
    r5.(size 2) <- r.(size 2) *. u32 5;
    r5.(size 3) <- r.(size 3) *. u32 5;
    r5.(size 4) <- r.(size 4) *. u32 5

#reset-options "--z3rlimit 50"

//inline_for_extraction
[@ CInline]
val fadd: out:felem -> f1:felem  -> f2:felem  -> Stack unit
                   (requires (fun h -> live h f1 /\ live h f2 /\ live h out /\
		    (let s1 = as_seq h f1 in
		     let s2 = as_seq h f2 in
		     uint_v s1.[size 0] + uint_v s2.[size 0] <= maxint U32 /\ 
		     uint_v s1.[size 1] + uint_v s2.[size 1] <= maxint U32 /\ 
		     uint_v s1.[size 2] + uint_v s2.[size 2] <= maxint U32 /\
		     uint_v s1.[size 3] + uint_v s2.[size 3] <= maxint U32 /\
		     uint_v s1.[size 4] + uint_v s2.[size 4] <= maxint U32 
		     )))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f1) h0 h1 /\
				         as_nat h1 out ==
					 as_nat h0 f1 +
					 as_nat h0 f2))		
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
  out.(size 0) <- f10 +. f20;
  out.(size 1) <- f11 +. f21;
  out.(size 2) <- f12 +. f22;
  out.(size 3) <- f13 +. f23;
  out.(size 4) <- f14 +. f24

//[@ CInline]
inline_for_extraction
val smul_felem: out:felem_wide -> u1:uint32 -> f2:felem -> Stack unit
                   (requires (fun h -> live h out /\ live h f2))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer out) h0 h1 /\
				         wide_as_nat h1 out ==
				         uint_v u1 `op_Multiply` as_nat h0 f2))
[@ CInline]
let smul_felem out u1 f2 = 
  let f20 = f2.(size 0) in
  let f21 = f2.(size 1) in
  let f22 = f2.(size 2) in
  let f23 = f2.(size 3) in
  let f24 = f2.(size 4) in
  out.(size 0) <- to_u64 u1 *. to_u64 f20;
  out.(size 1) <- to_u64 u1 *. to_u64 f21;
  out.(size 2) <- to_u64 u1 *. to_u64 f22;
  out.(size 3) <- to_u64 u1 *. to_u64 f23;
  out.(size 4) <- to_u64 u1 *. to_u64 f24


//[@ CInline]
inline_for_extraction
val smul_add_felem: out:felem_wide -> u1:uint32 -> f2:felem -> Stack unit
                   (requires (fun h -> live h out /\ live h f2))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer out) h0 h1 /\
				         wide_as_nat h1 out ==
				         wide_as_nat h0 out +
				         uint_v u1 `op_Multiply` as_nat h0 f2))		

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
  out.(size 0) <- o0 +. to_u64 u1 *. to_u64 f20;
  out.(size 1) <- o1 +. to_u64 u1 *. to_u64 f21;
  out.(size 2) <- o2 +. to_u64 u1 *. to_u64 f22;
  out.(size 3) <- o3 +. to_u64 u1 *. to_u64 f23;
  out.(size 4) <- o4 +. to_u64 u1 *. to_u64 f24

//inline_for_extraction
[@ CInline]
val mul_felem: out:felem_wide -> f1:felem -> f2:felem -> f2_20:felem  -> Stack unit
                   (requires (fun h -> live h out /\ live h f1 /\ live h f2 /\ live h f2_20))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer out) h0 h1))
[@ CInline]
let mul_felem out f1 f2 f2_20 = 
  push_frame();
  let tmp = create (u32 0) (size 5) in
  smul_felem out f1.(size 0) f2;
  tmp.(size 0) <- f2_20.(size 4);
  tmp.(size 1) <- f2.(size 0);
  tmp.(size 2) <- f2.(size 1);
  tmp.(size 3) <- f2.(size 2);
  tmp.(size 4) <- f2.(size 3);
  admit();
  smul_add_felem out f1.(size 1) tmp;
  tmp.(size 0) <- f2_20.(size 3);
  tmp.(size 1) <- f2_20.(size 4);
  tmp.(size 2) <- f2.(size 0);
  tmp.(size 3) <- f2.(size 1);
  tmp.(size 4) <- f2.(size 2);
  smul_add_felem out f1.(size 2) tmp;
  tmp.(size 0) <- f2_20.(size 2);
  tmp.(size 1) <- f2_20.(size 3);
  tmp.(size 2) <- f2_20.(size 4);
  tmp.(size 3) <- f2.(size 0);
  tmp.(size 4) <- f2.(size 1);
  smul_add_felem out f1.(size 3) tmp;
  tmp.(size 0) <- f2_20.(size 1);
  tmp.(size 1) <- f2_20.(size 2);
  tmp.(size 2) <- f2_20.(size 3);
  tmp.(size 3) <- f2_20.(size 4);
  tmp.(size 4) <- f2.(size 0);
  smul_add_felem out f1.(size 4) tmp;
  pop_frame()


inline_for_extraction
val carry26: l:uint32 -> cin:uint32 ->  (r:uint32 * cout:uint32)
let carry26 l cin = 
    let l = l +. cin in
    (l &. mask26, l >>. u32 26)

inline_for_extraction
val carry26_wide: l:uint64 -> cin:uint32 ->  (r:uint32 * cout:uint32)
let carry26_wide l cin = 
    let l = l +. to_u64 cin in
    (to_u32 l &. mask26, to_u32 (l >>. u32 26))

//[@ CInline]
inline_for_extraction
val carry_wide: out:felem -> inp:felem_wide -> Stack uint32
                   (requires (fun h -> live h out /\ live h inp))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer out) h0 h1))
[@ CInline]
let carry_wide out inp =
  let i0 = inp.(size 0) in
  let i1 = inp.(size 1) in
  let i2 = inp.(size 2) in
  let i3 = inp.(size 3) in
  let i4 = inp.(size 4) in
  let tmp0,carry = carry26_wide i0 (u32 0) in
  let tmp1,carry = carry26_wide i1 carry in
  let tmp2,carry = carry26_wide i2 carry in
  let tmp3,carry = carry26_wide i3 carry in
  let tmp4,carry = carry26_wide i4 carry in
  out.(size 0) <- tmp0;
  out.(size 1) <- tmp1;
  out.(size 2) <- tmp2;
  out.(size 3) <- tmp3; 
  out.(size 4) <- tmp4;
  carry

//[@ CInline]
inline_for_extraction
val carry0: out:felem -> carry:uint32 -> Stack unit
                   (requires (fun h -> live h out))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer out) h0 h1))
[@ CInline]
let carry0 out carry =
  let i0 = out.(size 0) in
  let tmp0 = i0 +. carry in
  out.(size 0) <- tmp0

//[@ CInline]
inline_for_extraction
val carry01: out:felem -> carry:uint32 -> Stack unit
                   (requires (fun h -> live h out))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer out) h0 h1))
[@ CInline]
let carry01 out carry =
  let i0 = out.(size 0) in
  let i1 = out.(size 1) in
  let tmp0,carry = carry26 i0 carry in
  let tmp1 = i1 +. carry in
  out.(size 0) <- tmp0;
  out.(size 1) <- tmp1


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
  let tmp0,carry = carry26 f0 (u32 0) in
  let tmp1,carry = carry26 f1 carry in
  let tmp2,carry = carry26 f2 carry in
  let tmp3,carry = carry26 f3 carry in
  let tmp4 = f4 +. carry in
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
  let tmp4,carry = carry26 f4 (u32 0) in
  let tmp0,carry = carry26 f0 (carry *. u32 5) in
  let tmp1 = f1 +. carry in
  f.(size 0) <- tmp0;
  f.(size 1) <- tmp1;
  f.(size 4) <- tmp4  

inline_for_extraction
val fmul_r: out:felem -> f1:felem -> pre:prf2:felem -> f2_20:felem -> Stack unit
                   (requires (fun h -> live h out /\ live h f1 /\ live h f2 /\ live h f2_20))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer out) h0 h1))
[@ CInline]
let fmul_r out f1 pre =
  push_frame();
  let r = sub pre (size 0) (size 5) in
  let r5 = sub pre (size 5) (size 5) in
  let tmp = create (u64 0) (size 5) in
  admit();
  mul_felem tmp f1 r r5;
  let carry = carry_wide out tmp in
  carry01 out carry;
  pop_frame()


inline_for_extraction
val fmul_r: out:felem -> f1:felem -> pre:precomp_r -> Stack unit
                   (requires (fun h -> live h out /\ live h f1 /\ live h pre))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer out) h0 h1))
[@ CInline]
let fmul_r out f1 pre =
  push_frame();
  let tmp = create (u64 0) (size 5) in
  
  admit();
  mul_felem tmp f1 f2 f2_20;
  let carry = carry_wide out tmp in
  carry01 out carry;
  pop_frame()

inline_for_extraction
val fadd_mul: out:felem -> f1:felem -> f2:felem -> f2_20:felem -> Stack unit
                   (requires (fun h -> live h out /\ live h f1 /\ live h f2 /\ live h f2_20))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer out) h0 h1))
let fadd_mul out f1 f2 f2_20 =
  push_frame();
  let tmp = create (u64 0) (size 5) in
  admit();
  fadd out out f1;
  mul_felem tmp out f2 f2_20;
  let carry = carry_wide out tmp in
  carry01 out carry;
  pop_frame()

inline_for_extraction
val fmul_add: out:felem -> f1:felem -> f2:felem -> f2_20:felem -> Stack unit
                   (requires (fun h -> live h out /\ live h f1 /\ live h f2 /\ live h f2_20))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer out) h0 h1))
let fmul_add out f1 f2 f2_20 =
  push_frame();
  let tmp = create (u64 0) (size 5) in
  admit();
  mul_felem tmp out f2 f2_20;
  let carry = carry_wide out tmp in
  carry01 out carry;
  fadd out out f1;
  pop_frame()

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
  let mask = uint32_eq_mask f4 (u32 0x3ffffff) in
  let mask = mask &. uint32_eq_mask f3 (u32 0x3ffffff) in
  let mask = mask &. uint32_eq_mask f2 (u32 0x3ffffff) in
  let mask = mask &. uint32_eq_mask f1 (u32 0x3ffffff) in
  let mask = mask &. uint32_gte_mask f0 (u32 0x3fffffb) in
  let p0 = mask &. u32 0x3fffffb in
  let p1 = mask &. u32 0x3ffffff in
  let p2 = mask &. u32 0x3ffffff in
  let p3 = mask &. u32 0x3ffffff in
  let p4 = mask &. u32 0x3ffffff in
  f.(size 0) <- f0 -. p0;
  f.(size 1) <- f1 -. p1;
  f.(size 2) <- f2 -. p2;
  f.(size 3) <- f3 -. p3;
  f.(size 4) <- f4 -. p4


inline_for_extraction
val reduce_felem: f:felem -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1))
let reduce_felem f =
    carry_felem f;
    carry_top_felem f;
    subtract_p f



inline_for_extraction
val load_felem_le: f:felem -> b:lbytes 16 -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1))
let load_felem_le f b =
    let (lo,hi) = load64x2_le b in
    load_felem f lo hi
(*
    let h0 = load32_le (sub b (size 0) (size 4)) in
    let h1 = load32_le (sub b (size 3) (size 4)) in
    let h2 = load32_le (sub b (size 6) (size 4)) in
    let h3 = load32_le (sub b (size 9) (size 4)) in
    let h4 = load32_le (sub b (size 12) (size 4)) in
    f.(size 0) <- h0 &. mask26;
    f.(size 1) <- (h1 >>. u32 2) &. mask26;
    f.(size 2) <- (h2 >>. u32 4) &. mask26;
    f.(size 3) <- (h3 >>. u32 6) &. mask26;
    f.(size 4) <- (h4 >>. u32 8) &. mask26
*)

inline_for_extraction
val load_felems_le: f:felem -> b:lbytes 16 -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1))
let load_felems_le f b = load_felem_le f b

inline_for_extraction
val store_felem_le: b:lbytes 16 -> f:felem -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer b) h0 h1))
let store_felem_le b f = 
    carry_felem f;
    let (f0,f1) = store_felem f in
    store64x2_le b f0 f1

