module Hacl.Impl.Poly1305.Field64

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Sequence
open Lib.Buffer
open Lib.ByteBuffer

let felem = lbuffer uint64 3ul
let felem_wide = lbuffer uint128 3ul
let precomp_r = lbuffer uint64 6ul

noextract 
val as_nat: h:mem -> e:felem -> GTot nat 
let as_nat h e = 
    let s = as_seq h e in
    let s0 =  uint_v (s.[0]) in
    let s1 =  uint_v (s.[1]) in
    let s2 =  uint_v (s.[2]) in
    let ( * ) = op_Multiply in
    s0 + (s1 * pow2 44) + (s2 * pow2 44) 

noextract 
val wide_as_nat: h:mem -> e:felem_wide -> GTot nat 
let wide_as_nat h e = 
    let s = as_seq h e in
    let s0 =  uint_v (s.[0]) in
    let s1 =  uint_v (s.[1]) in
    let s2 =  uint_v (s.[2]) in
    let ( * ) = op_Multiply in
    s0 + (s1 * pow2 44) + (s2 * pow2 44) 


inline_for_extraction
val create_felem: unit -> StackInline felem
		       (requires (fun h -> True))
		       (ensures (fun h0 b h1 -> live h1 b /\ stack_allocated b h0 h1 (Lib.Sequence.create 3 (u64 0))))
inline_for_extraction
let create_felem () = create (size 3) (u64 0) 

inline_for_extraction
val create_wide: unit -> StackInline felem_wide
		       (requires (fun h -> True))
		       (ensures (fun h0 b h1 -> live h1 b /\ stack_allocated b h0 h1 (Lib.Sequence.create 3 (to_u128 (u64 0)))))
inline_for_extraction
let create_wide () = create (size 3) (to_u128 (u64 0)) 

inline_for_extraction
let mask44 = u64 0xfffffffffff
inline_for_extraction
let mask42 = u64 0x3ffffffffff


inline_for_extraction
val load_felem: f:felem -> lo:uint64 -> hi:uint64 -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let load_felem f lo hi = 
    f.(size 0) <- lo &. mask44;
    f.(size 1) <- (lo >>. size 44) ^. ((hi &. u64 0xffffff) <<. size 20);
    f.(size 2) <- hi >>. size 24

inline_for_extraction
val store_felem: f:felem -> Stack (uint64 * uint64)
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> h0 == h1))
let store_felem f = 
    let f0 = f.(size 0) |. (f.(size 1) <<. size 44) in
    let f1 = (f.(size 1) >>. size 20) |. (f.(size 2) <<. size 24) in
    (f0,f1)

inline_for_extraction
val set_bit: f:felem -> i:size_t{size_v i < 130} -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let set_bit f i = 
    f.(i /. size 44) <- f.(i /. size 44) |. (u64 1 <<. (i %. size 44))

inline_for_extraction
val set_bit128: f:felem -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let set_bit128 f = 
    f.(size 2) <- f.(size 2) |. u64 0x10000000000

inline_for_extraction
val set_zero: f:felem -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let set_zero f = 
    f.(size 0) <- u64 0;
    f.(size 1) <- u64 0;
    f.(size 2) <- u64 0

inline_for_extraction
val copy_felem: f1:felem -> f2:felem -> Stack unit
                   (requires (fun h -> live h f1 /\ live h f2))
		   (ensures (fun h0 _ h1 -> modifies (loc f1) h0 h1))
let copy_felem f1 f2 = 
    f1.(size 0) <- f2.(size 0);
    f1.(size 1) <- f2.(size 1);
    f1.(size 2) <- f2.(size 2)


inline_for_extraction
val load_precompute_r: p:precomp_r -> r0:uint64 -> r1:uint64 -> Stack unit
                   (requires (fun h -> live h p))
		   (ensures (fun h0 _ h1 -> modifies (loc p) h0 h1))
let load_precompute_r p r0 r1 = 
    let r = sub p (size 0) (size 3) in
    let r20 = sub p (size 3) (size 3) in
    load_felem r r0 r1;
    r20.(size 0) <- r.(size 0) *. u64 20;
    r20.(size 1) <- r.(size 1) *. u64 20;
    r20.(size 2) <- r.(size 2) *. u64 20

#reset-options "--z3rlimit 20"

//inline_for_extraction
[@ CInline]
val fadd: out:felem ->  f1:felem  -> f2:felem  -> Stack unit
                   (requires (fun h -> live h f1 /\ live h f2 /\ live h out /\
		    (let s1 = as_seq h f1 in
		     let s2 = as_seq h f2 in
		     uint_v s1.[0] + uint_v s2.[0] <= maxint U64 /\ 
		     uint_v s1.[1] + uint_v s2.[1] <= maxint U64 /\ 
		     uint_v s1.[2] + uint_v s2.[2] <= maxint U64 )))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\
				         as_nat h1 out ==
					 as_nat h0 f1 +
					 as_nat h0 f2))		
[@ CInline]
let fadd out f1 f2 = 
  let f10 = f1.(size 0) in
  let f11 = f1.(size 1) in
  let f12 = f1.(size 2) in
  let f20 = f2.(size 0) in
  let f21 = f2.(size 1) in
  let f22 = f2.(size 2) in
  out.(size 0) <- f10 +. f20;
  out.(size 1) <- f11 +. f21;
  out.(size 2) <- f12 +. f22

//[@ CInline]
inline_for_extraction
val smul_felem: out:felem_wide -> u1:uint64 -> f2:felem -> Stack unit
                   (requires (fun h -> live h out /\ live h f2))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\
				         wide_as_nat h1 out ==
				         uint_v u1 `op_Multiply` as_nat h0 f2))
[@ CInline]
let smul_felem out u1 f2 = 
  let f20 = f2.(size 0) in
  let f21 = f2.(size 1) in
  let f22 = f2.(size 2) in
  out.(size 0) <- mul64_wide u1 f20;
  out.(size 1) <- mul64_wide u1 f21;
  out.(size 2) <- mul64_wide u1 f22

//[@ CInline]
inline_for_extraction
val smul_add_felem: out:felem_wide -> u1:uint64 -> f2:felem -> Stack unit
                   (requires (fun h -> live h out /\ live h f2 /\
			       (let s1 = as_seq h out in
				let s2 = as_seq h f2 in
			        uint_v s1.[0] + uint_v u1 `op_Multiply` uint_v s2.[0] <= maxint U128 /\ 
			        uint_v s1.[1] + uint_v u1 `op_Multiply` uint_v s2.[1] <= maxint U128 /\ 
			        uint_v s1.[2] + uint_v u1 `op_Multiply` uint_v s2.[2] <= maxint U128 )))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\
				         wide_as_nat h1 out ==
				         wide_as_nat h0 out +
				         uint_v u1 `op_Multiply` as_nat h0 f2))		

[@ CInline]
let smul_add_felem out u1 f2 = 
  let f20 = f2.(size 0) in
  let f21 = f2.(size 1) in
  let f22 = f2.(size 2) in
  let o0 = out.(size 0) in
  let o1 = out.(size 1) in
  let o2 = out.(size 2) in
  out.(size 0) <- o0 +. mul64_wide u1 f20;
  out.(size 1) <- o1 +. mul64_wide u1 f21;
  out.(size 2) <- o2 +. mul64_wide u1 f22

//inline_for_extraction
[@ CInline]
val mul_felem: out:felem_wide -> f1:felem -> r:felem -> r20:felem  -> Stack unit
                   (requires (fun h -> live h out /\ live h f1 /\ live h r /\ live h r20))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
[@ CInline]
let mul_felem out f1 r r20 = 
  push_frame();
  let tmp = create (size 3) (u64 0) in
  smul_felem out f1.(size 0) r;
  tmp.(size 0) <- r20.(size 2);
  tmp.(size 1) <- r.(size 0);
  tmp.(size 2) <- r.(size 1);
  admit();
  smul_add_felem out f1.(size 1) tmp;
  tmp.(size 0) <- r20.(size 1);
  tmp.(size 1) <- r20.(size 2);
  tmp.(size 2) <- r.(size 0);
  smul_add_felem out f1.(size 2) tmp;
  pop_frame()


inline_for_extraction
val carry44: l:uint64 -> cin:uint64 ->  (r:uint64 * cout:uint64)
let carry44 l cin = 
    let l = l +. cin in
    (l &. mask44, l >>. size 44)

inline_for_extraction
val carry42: l:uint64 -> cin:uint64 ->  (r:uint64 * cout:uint64)
let carry42 l cin = 
    let l = l +. cin in
    (l &. mask42, l >>. size 42)

inline_for_extraction
val carry44_wide: l:uint128 -> cin:uint64 ->  (r:uint64 * cout:uint64)
let carry44_wide l cin = 
    let l = l +. to_u128 cin in
    (to_u64 l &. mask44, to_u64 (l >>. size 44))

inline_for_extraction
val carry42_wide: l:uint128 -> cin:uint64 ->  (r:uint64 * cout:uint64)
let carry42_wide l cin = 
    let l = l +. to_u128 cin in
    (to_u64 l &. mask42, to_u64 (l >>. size 42))

//[@ CInline]
inline_for_extraction
val carry_wide: out:felem -> inp:felem_wide -> Stack unit
                   (requires (fun h -> live h out /\ live h inp))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
[@ CInline]
let carry_wide out inp =
  let i0 = inp.(size 0) in
  let i1 = inp.(size 1) in
  let i2 = inp.(size 2) in
  let tmp0,carry = carry44_wide i0 (u64 0) in
  let tmp1,carry = carry44_wide i1 carry in
  let tmp2,carry = carry42_wide i2 carry in
  let tmp0 = tmp0 +. (carry *. u64 5) in
  out.(size 0) <- tmp0;
  out.(size 1) <- tmp1;
  out.(size 2) <- tmp2

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
  let tmp0,carry = carry44 f0 (u64 0) in
  let tmp1,carry = carry44 f1 carry in
  let tmp2 = f2 +. carry in
  f.(size 0) <- tmp0;
  f.(size 1) <- tmp1;
  f.(size 2) <- tmp2

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
  let tmp2,carry = carry42 f2 (u64 0) in
  let tmp0,carry = carry44 f0 (carry *. u64 5) in
  let tmp1 = f1 +. carry in
  f.(size 0) <- tmp0;
  f.(size 1) <- tmp1;
  f.(size 2) <- tmp2  

//[@ CInline]
inline_for_extraction
val fmul_r: out:felem -> f1:felem -> p:precomp_r -> Stack unit
                   (requires (fun h -> live h out /\ live h f1 /\ live h p))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
[@ CInline]
let fmul_r out f1 p =
  push_frame();
  let r = sub p (size 0) (size 3) in
  let r20 = sub p (size 3) (size 3) in
  let tmp = create_wide () in
  admit();
  mul_felem tmp f1 r r20;
  let carry = carry_wide out tmp in
  pop_frame()

//[@ CInline]
inline_for_extraction
val fadd_mul_r: out:felem -> f1:felem -> p:precomp_r -> Stack unit
                   (requires (fun h -> live h out /\ live h f1 /\ live h p))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
[@ CInline]
let fadd_mul_r out f1 p =
  push_frame();
  let r = sub p (size 0) (size 3) in
  let r20 = sub p (size 3) (size 3) in
  let tmp = create_wide () in
  admit();
  fadd out out f1;
  mul_felem tmp out r r20;
  let carry = carry_wide out tmp in
  pop_frame()

//[@ CInline]
inline_for_extraction
val fmul_rn: out:felem -> f1:felem -> p:precomp_r -> Stack unit
                   (requires (fun h -> live h out /\ live h f1 /\ live h p))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
[@ CInline]
let fmul_rn out f1 p =
  fmul_r out f1 p

inline_for_extraction
val fmul_rn_normalize: out:felem -> p:precomp_r -> Stack unit
                   (requires (fun h -> live h out /\ live h p))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
[@ CInline]
let fmul_rn_normalize out p = 
    fmul_r out out p

inline_for_extraction
val subtract_p: f:felem -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let subtract_p f =
  let f0 = f.(size 0) in
  let f1 = f.(size 1) in
  let f2 = f.(size 2) in
  let mask = eq_mask f2 (u64 0x3ffffffffff) in
  let mask = mask &. eq_mask f1 (u64 0xfffffffffff) in
  let mask = mask &. gte_mask f0 (u64 0xffffffffffb) in
  let p0 = mask &. u64 0xffffffffffb in
  let p1 = mask &. u64 0xfffffffffff in
  let p2 = mask &. u64 0x3ffffffffff in
  f.(size 0) <- f0 -. p0;
  f.(size 1) <- f1 -. p1;
  f.(size 2) <- f2 -. p2


inline_for_extraction
val reduce_felem: f:felem -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let reduce_felem f =
    carry_felem f;
    carry_top_felem f;
    subtract_p f


inline_for_extraction
val load_felem_le: f:felem -> b:lbuffer uint8 16ul -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let load_felem_le f b =
    let lo = uint_from_bytes_le (sub b 0ul 8ul) in
    let hi = uint_from_bytes_le (sub b 8ul 8ul) in
    load_felem f lo hi

inline_for_extraction
val load_felems_le: f:felem -> b:lbuffer uint8 16ul -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let load_felems_le f b = load_felem_le f b

inline_for_extraction
val store_felem_le: b:lbuffer uint8 16ul -> f:felem -> Stack unit
                   (requires (fun h -> live h f /\ live h b))
		   (ensures (fun h0 _ h1 -> modifies (union (loc f) (loc b)) h0 h1))
let store_felem_le b f = 
    carry_felem f;
    let (f0,f1) = store_felem f in
    uint_to_bytes_le (sub b 0ul 8ul) f0;
    uint_to_bytes_le (sub b 8ul 8ul) f1

