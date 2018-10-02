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

let felem5 = (uint32 * uint32 * uint32 * uint32 * uint32)
let felem_wide5 = (uint64 * uint64 * uint64 * uint64 * uint64)

let scale32 = s:nat{s <= 64}
let scale64 = s:nat{s <= 4096}
let nat5 = (nat * nat * nat * nat * nat)
let scale32_5 = x:nat5{let (x1,x2,x3,x4,x5) = x in 
		       x1 <= 64 /\ x2 <= 64 /\ x3 <= 64 /\ x4 <= 64 /\ x5 <= 64}
let scale64_5 = x:nat5{let (x1,x2,x3,x4,x5) = x in 
		       x1 <= 4096 /\ x2 <= 4096 /\ x3 <= 4096 /\ x4 <= 4096 /\ x5 <= 4096}

let s32x5 (x:scale32) : scale32_5 = (x,x,x,x,x)
let s64x5 (x:scale64) : scale64_5 = (x,x,x,x,x)

open FStar.Mul

let ( <=* ) (x:nat5) (y:nat5) : Type =
    let (x1,x2,x3,x4,x5) = x in
    let (y1,y2,y3,y4,y5) = y in
    (x1 <= y1) /\
    (x2 <= y2) /\
    (x3 <= y3) /\
    (x4 <= y4) /\
    (x5 <= y5) 

let ( +* ) (x:nat5) (y:nat5) : nat5 =
    let (x1,x2,x3,x4,x5) = x in
    let (y1,y2,y3,y4,y5) = y in
   (x1 + y1 ,
    x2 + y2 ,
    x3 + y3 ,
    x4 + y4 ,
    x5 + y5)

let ( ** ) (x:nat5) (y:nat5) : nat5 = 
    let (x1,x2,x3,x4,x5) = x in
    let (y1,y2,y3,y4,y5) = y in
   (x1 * y1 ,
    x2 * y2 ,
    x3 * y3 ,
    x4 * y4 ,
    x5 * y5)

#reset-options "--z3rlimit 100"
let ( *^ ) (x:scale32) (y:scale32_5) : scale64_5 = 
    let (y1,y2,y3,y4,y5) = y in
   (x * y1 ,
    x * y2 ,
    x * y3 ,
    x * y4 ,
    x * y5)



assume val pow26: nat
inline_for_extraction
let max26 = pow26 - 1

assume val lemma_pow_32_26: _:unit{pow2 32 == 64 * pow26}
assume val lemma_pow_64_26: _:unit{pow2 64 == 4096 * pow26 * pow26}

//let _ : (x:unit{pow2 32 == 64 * pow2 26}) = 
//      assert_norm (pow2 32 == 64 * pow2 26)
//let _ : (x:unit{pow2 64 == 4096 * pow2 26 * pow2 26}) = 
//      assert_norm (pow2 64 == 4096 * pow2 26 * pow2 26)


let felem_fits1 (x:uint32) (m:scale32) = 
    uint_v x <= m * max26 

let felem_wide_fits1 (x:uint64) (m:scale64) = 
    uint_v x <= m * max26 * max26

let felem_fits5 (f:felem5) (m:scale32_5) = 
    let (x1,x2,x3,x4,x5) = f in
    let (m1,m2,m3,m4,m5) = m in
    felem_fits1 x1 m1 /\ 
    felem_fits1 x2 m2 /\ 
    felem_fits1 x3 m3 /\ 
    felem_fits1 x4 m4 /\ 
    felem_fits1 x5 m5 

let felem_wide_fits5 (f:felem_wide5) (m:scale64_5) = 
    let (x1,x2,x3,x4,x5) = f in
    let (m1,m2,m3,m4,m5) = m in
    felem_wide_fits1 x1 m1 /\ 
    felem_wide_fits1 x2 m2 /\ 
    felem_wide_fits1 x3 m3 /\ 
    felem_wide_fits1 x4 m4 /\ 
    felem_wide_fits1 x5 m5 
  

let felem_fits (h:mem) (f:felem) (m:scale32_5) = 
    let s = as_seq h f in
    let s0 =  (s.[size 0]) in
    let s1 =  (s.[size 1]) in
    let s2 =  (s.[size 2]) in
    let s3 =  (s.[size 3]) in
    let s4 =  (s.[size 4]) in
    felem_fits5 (s0,s1,s2,s3,s4) m

let felem_wide_fits (h:mem) (f:felem_wide) (m:scale64_5) = 
    let s = as_seq h f in
    let s0 =  (s.[size 0]) in
    let s1 =  (s.[size 1]) in
    let s2 =  (s.[size 2]) in
    let s3 =  (s.[size 3]) in
    let s4 =  (s.[size 4]) in
    felem_wide_fits5 (s0,s1,s2,s3,s4) m


noextract 
val as_nat5: f:felem5 -> GTot nat 
let as_nat5  (f:felem5) = 
    let (s0,s1,s2,s3,s4) = f in
    uint_v s0 + (uint_v s1 * pow26) + (uint_v s2 * pow26 * pow26) + (uint_v s3 * pow26 * pow26 * pow26) + (uint_v s4 * pow26 * pow26 * pow26 * pow26)

noextract 
val wide_as_nat5: f:felem_wide5 -> GTot nat 
let wide_as_nat5  (f:felem_wide5) = 
    let (s0,s1,s2,s3,s4) = f in
    uint_v s0 + (uint_v s1 * pow26) + (uint_v s2 * pow26 * pow26) + (uint_v s3 * pow26 * pow26 * pow26) + (uint_v s4 * pow26 * pow26 * pow26 * pow26)

noextract 
val as_nat: h:mem -> e:felem -> GTot nat 
let as_nat h e = 
    let s = as_seq h e in
    let s0 =  (s.[size 0]) in
    let s1 =  (s.[size 1]) in
    let s2 =  (s.[size 2]) in
    let s3 =  (s.[size 3]) in
    let s4 =  (s.[size 4]) in
    as_nat5 (s0,s1,s2,s3,s4)

noextract 
val wide_as_nat: h:mem -> e:felem_wide -> GTot nat 
let wide_as_nat h e = 
    let s = as_seq h e in
    let s0 =  (s.[size 0]) in
    let s1 =  (s.[size 1]) in
    let s2 =  (s.[size 2]) in
    let s3 =  (s.[size 3]) in
    let s4 =  (s.[size 4]) in
    wide_as_nat5 (s0,s1,s2,s3,s4)

inline_for_extraction
let create_felem () = create (u32 0) (size 5)

inline_for_extraction
let create_wide () = create (u64 0) (size 5)

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
val store_felem: f:felem -> Stack (uint64 & uint64)
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
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1 /\ as_nat h1 f == 0))
let set_zero f = 
    f.(size 0) <- u32 0;
    f.(size 1) <- u32 0;
    f.(size 2) <- u32 0;
    f.(size 3) <- u32 0;
    f.(size 4) <- u32 0

#reset-options "--z3rlimit 50"
inline_for_extraction
val copy_felem: f1:felem -> f2:felem -> Stack unit
                   (requires (fun h -> live h f1 /\ live h f2))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f1) h0 h1 /\ as_nat h1 f1 == as_nat h0 f2))
let copy_felem f1 f2 = 
    let f20 = f2.(size 0) in
    let f21 = f2.(size 1) in
    let f22 = f2.(size 2) in
    let f23 = f2.(size 3) in
    let f24 = f2.(size 4) in
    f1.(size 0) <- f20;
    f1.(size 1) <- f21;
    f1.(size 2) <- f22;
    f1.(size 3) <- f23;
    f1.(size 4) <- f24


inline_for_extraction
val load_precompute_r: p:precomp_r -> r0:uint64 -> r1:uint64 -> Stack unit
                   (requires (fun h -> live h p))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer p) h0 h1))
let load_precompute_r p r0 r1 = 
    let r = sub p (size 0) (size 5) in
    let r5 = sub p (size 5) (size 5) in
    load_felem r r0 r1;
    r5.(size 0) <- r.(size 0) *. u32 5;
    r5.(size 1) <- r.(size 1) *. u32 5;
    r5.(size 2) <- r.(size 2) *. u32 5;
    r5.(size 3) <- r.(size 3) *. u32 5;
    r5.(size 4) <- r.(size 4) *. u32 5


#reset-options "--z3rlimit 100 --max_fuel 1"


inline_for_extraction
val fadd_: #m1:scale32_5 -> #m2:scale32_5 -> out:felem -> f1:felem  -> f2:felem  -> Stack unit
                   (requires (fun h -> live h f1 /\ live h f2 /\ live h out /\
				    felem_fits h f1 m1 /\ felem_fits h f2 m2 /\
				    (m1 +* m2) <=* s32x5 64))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer out) h0 h1 /\
				         as_nat h1 out ==
					 as_nat h0 f1 +
					 as_nat h0 f2))		
let fadd_ #m1 #m2 out f1 f2 = 
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
  out.(size 0) <- f10 +! f20;
  out.(size 1) <- f11 +! f21;
  out.(size 2) <- f12 +! f22;
  out.(size 3) <- f13 +! f23;
  out.(size 4) <- f14 +! f24


//inline_for_extraction
[@ CInline]
val fadd: out:felem -> f1:felem  -> f2:felem  -> Stack unit
                   (requires (fun h -> live h f1 /\ live h f2 /\ live h out /\
				    felem_fits h f1 (s32x5 32) /\ 
				    felem_fits h f2 (s32x5 32)))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer out) h0 h1 /\
				         as_nat h1 out ==
					 as_nat h0 f1 +
					 as_nat h0 f2))		
[@ CInline]
let fadd out f1 f2 = fadd_ #(s32x5 32) #(s32x5 32) out f1 f2

#reset-options "--z3rlimit 400 --max_fuel 1"

inline_for_extraction
val mul_wide32: #m1:scale32 -> #m2:scale32 -> x:uint32{felem_fits1 x m1} -> 
		     y:uint32{felem_fits1 y m2 /\ m1 * m2 <= 4096} -> 
		     z:uint64{uint_v z == uint_v x * uint_v y /\ 
			      felem_wide_fits1 z (m1 * m2)}

let mul_wide32 #m1 #m2 x y = 
  assert (uint_v x * uint_v y <= m1 * m2 * max26 * max26);
  to_u64 x *! to_u64 y 


inline_for_extraction
val smul_felem5: #m1:scale32 -> #m2:scale32_5 -> 
		u1:uint32{felem_fits1 u1 m1} -> 
		f2:felem5{felem_fits5 f2 m2} -> 
		out:felem_wide5{
			     wide_as_nat5 out == uint_v u1 * as_nat5 f2 /\
			     felem_wide_fits5 out (m1 *^ m2)}


let smul_felem5 #m1 #m2 u1 (f20,f21,f22,f23,f24) = 
  let (m20,m21,m22,m23,m24) = m2 in
  let o0 = mul_wide32 #m1 #m20 u1 f20 in
  let o1 = mul_wide32 #m1 #m21 u1 f21 in
  let o2 = mul_wide32 #m1 #m22 u1 f22 in
  let o3 = mul_wide32 #m1 #m23 u1 f23 in
  let o4 = mul_wide32 #m1 #m24 u1 f24 in
  (o0,o1,o2,o3,o4)
  

inline_for_extraction
val smul_add_felem5: #m1:scale32 -> #m2:scale32_5 -> #m3:scale64_5 -> 
		    u1:uint32{felem_fits1 u1 m1} -> 
		    f2:felem5{felem_fits5 f2 m2} -> 
		    acc1:felem_wide5{felem_wide_fits5 acc1 m3 /\ 
				     (m3 +* (m1 *^ m2))  <=* s64x5 4096} ->
		    acc2:felem_wide5{felem_wide_fits5 acc2 (m3 +* (m1 *^ m2)) /\
		                     wide_as_nat5 acc2 == 
				     wide_as_nat5 acc1 + (uint_v u1 * as_nat5 f2)}
#reset-options "--z3rlimit 300 --max_fuel 1"				     
let smul_add_felem5 #m1 #m2 #m3 u1 (f20,f21,f22,f23,f24) (o0,o1,o2,o3,o4) =
  let (r0,r1,r2,r3,r4) = smul_felem5 #m1 #m2 u1 (f20,f21,f22,f23,f24) in
  let o0 = o0 +! r0 in
  let o1 = o1 +! r1 in
  let o2 = o2 +! r2 in
  let o3 = o3 +! r3 in 
  let o4 = o4 +! r4 in
  (o0,o1,o2,o3,o4)
  
inline_for_extraction
val mul_felem5: f1:felem5{felem_fits5 f1 (2,3,2,2,2)} -> 
		r:felem5{felem_fits5 r (1,1,1,1,1)} -> 
		r5:felem5{felem_fits5 r5 (5,5,5,5,5)}  -> 
		out:felem_wide5{felem_wide_fits5 out (47,35,27,19,11)}

#reset-options "--z3rlimit 200"
let mul_felem5 (f10,f11,f12,f13,f14) (r0,r1,r2,r3,r4) (r50,r51,r52,r53,r54) = 
  let (a0,a1,a2,a3,a4) = smul_felem5 #2 #(1,1,1,1,1) f10 (r0,r1,r2,r3,r4) in
  let (a0,a1,a2,a3,a4) = smul_add_felem5 #3 #(5,1,1,1,1) #(2,2,2,2,2) f11 (r54,r0,r1,r2,r3) (a0,a1,a2,a3,a4) in
  let (a0,a1,a2,a3,a4) = smul_add_felem5 #2 #(5,5,1,1,1) #(17,5,5,5,5) f12 (r53,r54,r0,r1,r2) (a0,a1,a2,a3,a4) in
  let (a0,a1,a2,a3,a4) = smul_add_felem5 #2 #(5,5,5,1,1) #(27,15,7,7,7) f13 (r52,r53,r54,r0,r1) (a0,a1,a2,a3,a4) in
  let (a0,a1,a2,a3,a4) = smul_add_felem5 #2 #(5,5,5,5,1) #(37,25,17,9,9) f14 (r51,r52,r53,r54,r0) (a0,a1,a2,a3,a4) in
  (a0,a1,a2,a3,a4)


//inline_for_extraction
[@ CInline]
val mul_felem: out:felem_wide -> f1:felem -> r:felem -> r5:felem  -> Stack unit
                   (requires (fun h -> live h out /\ live h f1 /\ live h r /\ live h r5 /\
				    felem_fits h f1 (2,3,2,2,2) /\ 
				    felem_fits h r (1,1,1,1,1) /\ 
				    felem_fits h r5 (5,5,5,5,5)))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer out) h0 h1 /\ 
					 felem_wide_fits h1 out (47,35,27,19,11)))
[@ CInline]
let mul_felem out f1 r r5 = 
  let f10 = f1.(size 0) in
  let f11 = f1.(size 1) in
  let f12 = f1.(size 2) in
  let f13 = f1.(size 3) in
  let f14 = f1.(size 4) in
  
  let r0 = r.(size 0) in
  let r1 = r.(size 1) in
  let r2 = r.(size 2) in
  let r3 = r.(size 3) in
  let r4 = r.(size 4) in

  let r50 = r5.(size 0) in
  let r51 = r5.(size 1) in
  let r52 = r5.(size 2) in
  let r53 = r5.(size 3) in
  let r54 = r5.(size 4) in

  let (o0,o1,o2,o3,o4) = mul_felem5 (f10,f11,f12,f13,f14) (r0,r1,r2,r3,r4) (r50,r51,r52,r53,r54) in
  out.(size 0) <- o0;
  out.(size 1) <- o1;
  out.(size 2) <- o2;
  out.(size 3) <- o3;
  out.(size 4) <- o4


inline_for_extraction
val carry26: l:uint32{felem_fits1 l 2} -> 
	     cin:uint32{felem_fits1 cin 62}  -> 
	     res:(uint32 & uint32){felem_fits1 (fst res) 1 /\ 
				   uint_v (snd res) <= 64 /\
				   (uint_v (snd res) > 0 ==> uint_v (fst res) < uint_v cin)}
let carry26 l cin = 
    let l = l +! cin in
    admit();
    (l &. mask26, l >>. u32 26)

inline_for_extraction
val carry26_wide: #m:scale64{m < 64} ->
		  l:uint64{felem_wide_fits1 l m} -> 
		  cin:uint32{felem_fits1 cin 64} ->  
		  res:(uint32 & uint32){felem_fits1 (fst res) 1 /\ 
					felem_fits1 (snd res) (m + 1)}
let carry26_wide #m l cin = 
    let l = l +! to_u64 cin in
    admit();
    (to_u32 l &. mask26, to_u32 (l >>. u32 26))

//[@ CInline]
inline_for_extraction
val carry_wide: out:felem -> inp:felem_wide -> Stack uint32
                   (requires (fun h -> live h out /\ live h inp /\ 
				felem_wide_fits h inp (47,35,27,19,11)))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer out) h0 h1 /\ 
				         felem_fits h1 out (1,2,1,1,1)))
[@ CInline]
let carry_wide out inp =
  let i0 = inp.(size 0) in
  let i1 = inp.(size 1) in
  let i2 = inp.(size 2) in
  let i3 = inp.(size 3) in
  let i4 = inp.(size 4) in
  let tmp0,carry = carry26_wide #47 i0 (u32 0) in
  let tmp1,carry = carry26_wide #35 i1 carry in
  let tmp2,carry = carry26_wide #27 i2 carry in
  let tmp3,carry = carry26_wide #19 i3 carry in
  let tmp4,carry = carry26_wide #11 i4 carry in
  let tmp0,carry = carry26 tmp0 (carry *. u32 5) in
  let tmp1 = tmp1 +. carry in
  out.(size 0) <- tmp0;
  out.(size 1) <- tmp1;
  out.(size 2) <- tmp2;
  out.(size 3) <- tmp3; 
  out.(size 4) <- tmp4;
  carry

//[@ CInline]
inline_for_extraction
val carry_felem: f:felem -> Stack unit
                   (requires (fun h -> live h f /\ felem_fits h f (1,2,1,1,1)))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1 /\ 
			    felem_fits h1 f (1,1,1,1,2)))
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
                   (requires (fun h -> live h f /\ felem_fits h f (1,1,1,1,2)))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1 /\ felem_fits h1 f (1,2,1,1,1)))
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

//[@ CInline]
inline_for_extraction
val fmul_r: out:felem -> f1:felem -> p:precomp_r -> Stack unit
                   (requires (fun h -> live h out /\ live h f1 /\ live h p /\ 
				felem_fits h f1 (1,1,1,1,1) /\
				felem_fits h (gsub p 0ul 5ul) (1,1,1,1,1) /\
				felem_fits h (gsub p 5ul 5ul) (5,5,5,5,5)
				))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer out) h0 h1))
[@ CInline]
let fmul_r out f1 p =
  push_frame();
  let r = sub p (size 0) (size 5) in
  let r5 = sub p (size 5) (size 5) in
  let tmp = create_wide () in
  admit();
  mul_felem tmp f1 r r5;
  let carry = carry_wide out tmp in
  pop_frame()

//[@ CInline]
inline_for_extraction
val fadd_mul_r: out:felem -> f1:felem -> p:precomp_r -> Stack unit
                   (requires (fun h -> live h out /\ live h f1 /\ live h p))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer out) h0 h1))
[@ CInline]
let fadd_mul_r out f1 p =
  push_frame();
  let r = sub p (size 0) (size 5) in
  let r5 = sub p (size 5) (size 5) in
  let tmp = create_wide () in
  admit();
  fadd out out f1;
  mul_felem tmp out r r5;
  let carry = carry_wide out tmp in
  pop_frame()

//[@ CInline]
inline_for_extraction
val fmul_rn: out:felem -> f1:felem -> p:precomp_r -> Stack unit
                   (requires (fun h -> live h out /\ live h f1 /\ live h p))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer out) h0 h1))
[@ CInline]
let fmul_rn out f1 p =
  fmul_r out f1 p

inline_for_extraction
val fmul_rn_normalize: out:felem -> p:precomp_r -> Stack unit
                   (requires (fun h -> live h out /\ live h p))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer out) h0 h1))
[@ CInline]
let fmul_rn_normalize out p = 
    fmul_r out out p

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
                   (requires (fun h -> live h f /\ felem_fits h f (1,2,1,1,1)))
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
                   (requires (fun h -> live h f /\ live h b /\ felem_fits h f (1,2,1,1,1)))
		   (ensures (fun h0 _ h1 -> modifies (loc_union (loc_buffer f) (loc_buffer b)) h0 h1))
let store_felem_le b f = 
    carry_felem f;
    let (f0,f1) = store_felem f in
    store64x2_le b f0 f1


