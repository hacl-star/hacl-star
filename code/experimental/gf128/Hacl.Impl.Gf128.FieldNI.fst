module Hacl.Impl.Gf128.FieldNI

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Lib.IntVector

inline_for_extraction
let cl_add (x:uint128x1) (y:uint128x1) : uint128x1 = vec_xor x y
inline_for_extraction
let clmul_wide (x:uint128x1) (y:uint128x1) : uint128x1 * uint128x1 = 
    let lo = vec_clmul_lo_lo x y in
    let m1 = vec_clmul_hi_lo x y in
    let m2 = vec_clmul_lo_hi x y in
    let hi = vec_clmul_hi_hi x y in
    let m1 = cl_add m1 m2 in
    let m2 = vec_shift_left m1 (size 64) in
    let m1 = vec_shift_right m1 (size 64) in
    let lo = cl_add lo m2 in
    let hi = cl_add hi m1 in
    (hi,lo)

inline_for_extraction
let clmul_wide4 (x1:uint128x1) (x2:uint128x1) (x3:uint128x1) (x4:uint128x1) 
		(y1:uint128x1) (y2:uint128x1) (y3:uint128x1) (y4:uint128x1): 
		uint128x1 * uint128x1 = 
    let lo1 = vec_clmul_lo_lo x1 y1 in
    let lo2 = vec_clmul_lo_lo x2 y2 in
    let lo3 = vec_clmul_lo_lo x3 y3 in
    let lo4 = vec_clmul_lo_lo x4 y4 in
    let lo = cl_add lo1 lo2 in
    let lo = cl_add lo lo3 in
    let lo = cl_add lo lo4 in
    
    let m1 = vec_clmul_hi_lo x1 y1 in
    let m2 = vec_clmul_hi_lo x2 y2 in
    let m3 = vec_clmul_hi_lo x3 y3 in
    let m4 = vec_clmul_hi_lo x4 y4 in
    let m = cl_add m1 m2 in
    let m = cl_add m m3 in
    let m = cl_add m m4 in

    let m1 = vec_clmul_lo_hi x1 y1  in
    let m2 = vec_clmul_lo_hi x2 y2  in
    let m3 = vec_clmul_lo_hi x3 y3  in
    let m4 = vec_clmul_lo_hi x4 y4  in
    let m = cl_add m m1 in
    let m = cl_add m m2 in
    let m = cl_add m m3 in
    let m = cl_add m m4 in

    let hi1 = vec_clmul_hi_hi x1 y1 in
    let hi2 = vec_clmul_hi_hi x2 y2 in
    let hi3 = vec_clmul_hi_hi x3 y3 in
    let hi4 = vec_clmul_hi_hi x4 y4 in
    let hi = cl_add hi1 hi2 in
    let hi = cl_add hi hi3 in
    let hi = cl_add hi hi4 in

    let m1 = vec_shift_left m (size 64) in
    let m2 = vec_shift_right m (size 64) in
    let lo = cl_add lo m1 in
    let hi = cl_add hi m2 in
    (hi,lo)

let shift_right64 (v:uint128x1) (s:shiftval U64) =
    cast U128 1 (vec_shift_right (cast U64 2 v) s)
let shift_left64 (v:uint128x1) (s:shiftval U64) =
    cast U128 1 (vec_shift_left (cast U64 2 v) s)
    
inline_for_extraction
let gf128_reduce (hi:uint128x1) (lo:uint128x1) : uint128x1 = 
    (* LEFT SHIFT [hi:lo] by 1 *)
    let lo1 = shift_right64 lo (size 63) in
    let lo2 = vec_shift_left lo1 (size 64) in
    let lo3 = shift_left64 lo (size 1) in
    let lo3 = vec_xor lo3 lo2 in

    let hi1 = shift_right64 hi (size 63) in
    let hi1 = vec_shift_left hi1 (size 64) in
    let hi2 = shift_left64 hi (size 1) in
    let hi2 = vec_xor hi2 hi1 in

    let lo1 = shift_right64 lo (size 63) in
    let lo1 = vec_shift_right lo1 (size 64) in
    let hi2 = vec_xor hi2 lo1 in
    
    let lo = lo3 in
    let hi = hi2 in
(*
    let lo1 = vec128_shift_right_bits lo (size 127) in
    let lo = vec128_shift_left_bits lo (size 1) in
    let hi = vec128_shift_left_bits hi (size 1) in
    let hi = vec128_xor hi lo1 in
*)
    (* LEFT SHIFT [x0:0] BY 63,62,57 and xor with [x1:x0] *)
    let lo1 = shift_left64 lo (size 63) in
    let lo2 = shift_left64 lo (size 62) in
    let lo3 = shift_left64 lo (size 57) in
    let lo1 = vec_xor lo1 lo2 in
    let lo1 = vec_xor lo1 lo3 in
    let lo2 = vec_shift_right lo1 (size 64) in
    let lo3 = vec_shift_left lo1 (size 64) in
    let lo =  vec_xor lo lo3 in    
    let lo' = lo2 in

    (* RIGHT SHIFT [x1:x0] BY 1,2,7 and xor with [x1:x0] *)
    let lo1 = shift_right64 lo (size 1) in
    let lo2 = shift_right64 lo (size 2) in
    let lo3 = shift_right64 lo (size 7) in
    let lo1 = vec_xor lo1 lo2 in
    let lo1 = vec_xor lo1 lo3 in
    
    let lo1 = vec_xor lo1 lo' in
    let lo = vec_xor lo lo1 in

    let lo = vec_xor lo hi in
    lo

let felem = lbuffer uint128x1 1ul
let felem4 = lbuffer uint128x1 4ul
let precomp = lbuffer uint128x1 4ul
let block = lbuffer uint8 16ul
let block4 = lbuffer uint8 64ul
let gcm_ctx = lbuffer uint128x1 5ul // acc + precomp

inline_for_extraction
val get_acc: ctx:gcm_ctx -> Stack felem
	     (requires (fun h -> live h ctx))
	     (ensures (fun h0 f h1 -> h0 == h1 /\ live h1 f))
let get_acc (ctx:gcm_ctx) = 
  sub ctx (size 0) (size 1)

inline_for_extraction
val get_r: ctx:gcm_ctx -> Stack felem
	     (requires (fun h -> live h ctx))
	     (ensures (fun h0 f h1 -> h0 == h1 /\ live h1 f))
let get_r (ctx:gcm_ctx) = 
  sub ctx (size 4) (size 1)

inline_for_extraction
val get_precomp: ctx:gcm_ctx -> Stack precomp
	     (requires (fun h -> live h ctx))
	     (ensures (fun h0 f h1 -> h0 == h1 /\ live h1 f))
let get_precomp (ctx:gcm_ctx) = 
  sub ctx (size 1) (size 4)


inline_for_extraction
val create_felem: unit -> StackInline felem
	  (requires (fun h -> True))
	  (ensures (fun h0 f h1 -> live h1 f))
let create_felem () = create 1ul (vec_zero U128 1)

inline_for_extraction
val felem_set_zero: f:felem -> StackInline unit
	  (requires (fun h -> live h f))
	  (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))    
let felem_set_zero f =  f.(0ul) <- (vec_zero U128 1)


inline_for_extraction
val create_felem4: unit -> StackInline felem4
	  (requires (fun h -> True))
	  (ensures (fun h0 f h1 -> live h1 f))
let create_felem4 () = create 4ul (vec_zero U128 1)

inline_for_extraction
val create_ctx: unit -> StackInline gcm_ctx
	  (requires (fun h -> True))
	  (ensures (fun h0 f h1 -> live h1 f))
let create_ctx () = create 5ul (vec_zero U128 1)

inline_for_extraction
val load_felem: x:felem -> y:lbuffer uint8 16ul -> Stack unit
	  (requires (fun h -> live h x /\ live h y))
	  (ensures (fun h0 _ h1 -> live h1 x /\ live h1 y /\ modifies (loc x) h0 h1))
let load_felem x y = 
    x.(size 0) <- vec_load_be U128 1 y

inline_for_extraction
val load_felem4: x:felem4 -> y:lbuffer uint8 64ul -> Stack unit
	  (requires (fun h -> live h x /\ live h y))
	  (ensures (fun h0 _ h1 -> live h1 x /\ live h1 y /\ modifies (loc x) h0 h1))
let load_felem4 x y = 
    x.(size 0) <- vec_load_be U128 1 (sub y (size 0) (size 16));
    x.(size 1) <- vec_load_be U128 1 (sub y (size 16) (size 16));
    x.(size 2) <- vec_load_be U128 1 (sub y (size 32) (size 16));
    x.(size 3) <- vec_load_be U128 1 (sub y (size 48) (size 16))

inline_for_extraction
val store_felem: x:lbuffer uint8 16ul -> y:felem -> Stack unit
	  (requires (fun h -> live h x /\ live h y))
	  (ensures (fun h0 _ h1 -> live h1 x /\ live h1 y /\ modifies (loc x) h0 h1))
let store_felem x y = 
    vec_store_be x y.(size 0)


[@ CInline]
val fadd: x:felem -> y:felem -> Stack unit
	  (requires (fun h -> live h x /\ live h y))
	  (ensures (fun h0 _ h1 -> live h1 x /\ live h1 y /\ modifies (loc x) h0 h1))
let fadd (x:felem) (y:felem) = 
    x.(size 0) <- cl_add x.(size 0) y.(size 0)


[@ CInline]
val fmul: x:felem -> y:felem -> Stack unit
	  (requires (fun h -> live h x /\ live h y))
	  (ensures (fun h0 _ h1 -> live h1 x /\ live h1 y /\ modifies (loc x) h0 h1))
let fmul (x:felem) (y:felem) = 
    let xe = x.(size 0) in
    let ye = y.(size 0) in
    let (hi,lo) = clmul_wide xe ye in
    let lo = gf128_reduce hi lo in
    x.(size 0) <- lo

[@ CInline]
val load_precompute_r: pre:precomp -> key:block -> Stack unit
	  (requires (fun h -> live h pre /\ live h key))
	  (ensures (fun h0 _ h1 -> modifies (loc pre) h0 h1))
let load_precompute_r pre key = 
    let r_4 = sub pre (size 0) (size 1) in
    let r_3 = sub pre (size 1) (size 1) in
    let r_2 = sub pre (size 2) (size 1) in
    let r   = sub pre (size 3) (size 1) in
    load_felem r key;
    pre.(size 0) <- r.(size 0);
    pre.(size 1) <- r.(size 0);
    pre.(size 2) <- r.(size 0);
    fmul r_2 r;
    fmul r_3 r_2;
    fmul r_4 r_3



[@ CInline]
val fmul_pre: x:felem -> y:precomp -> Stack unit
	  (requires (fun h -> live h x /\ live h y))
	  (ensures (fun h0 _ h1 -> live h1 x /\ live h1 y /\ modifies (loc x) h0 h1))
let fmul_pre x pre =
    let r = sub pre (size 3) (size 1) in
    let xe = x.(size 0) in
    let ye = r.(size 0) in
    let (hi,lo) = clmul_wide xe ye in
    let lo = gf128_reduce hi lo in
    x.(size 0) <- lo

[@ CInline]
val fadd4: x:felem4 -> y:felem4 -> Stack unit
	  (requires (fun h -> live h x /\ live h y))
	  (ensures (fun h0 _ h1 -> live h1 x /\ live h1 y /\ modifies (loc x) h0 h1))
let fadd4 (x:felem4) (y:felem4) = 
    x.(size 0) <- cl_add x.(size 0) y.(size 0);
    x.(size 1) <- cl_add x.(size 1) y.(size 1);
    x.(size 2) <- cl_add x.(size 2) y.(size 2);
    x.(size 2) <- cl_add x.(size 3) y.(size 3)

[@ CInline]
val fmul4: x:felem4 -> pre:precomp -> Stack unit
	  (requires (fun h -> live h x /\ live h pre))
	  (ensures (fun h0 _ h1 -> live h1 x /\ live h1 pre /\ modifies (loc x) h0 h1))
let fmul4 (x:felem4) (pre:precomp) = 
    fmul (sub x (size 0) (size 1)) (sub pre (size 0) (size 1));
    fmul (sub x (size 1) (size 1)) (sub pre (size 0) (size 1));
    fmul (sub x (size 2) (size 1)) (sub pre (size 0) (size 1));
    fmul (sub x (size 3) (size 1)) (sub pre (size 0) (size 1))


[@ CInline]
val fadd_mul4: acc:felem -> x:felem4 -> pre:precomp -> Stack unit
	  (requires (fun h -> live h acc /\ live h x /\ live h pre))
	  (ensures (fun h0 _ h1 -> modifies (loc acc) h0 h1))
let fadd_mul4 (acc:felem) (x:felem4) (pre:precomp) = 
    let x1 = x.(size 0) in
    let x2 = x.(size 1) in
    let x3 = x.(size 2) in
    let x4 = x.(size 3) in
    let y1 = pre.(size 0) in
    let y2 = pre.(size 1) in
    let y3 = pre.(size 2) in
    let y4 = pre.(size 3) in
    let acc0 = acc.(size 0) in
    let acc0 = cl_add acc0 x1 in
    let (hi,lo) = clmul_wide4 acc0 x2 x3 x4 y1 y2 y3 y4 in
    let lo = gf128_reduce hi lo in
    acc.(size 0) <- lo



