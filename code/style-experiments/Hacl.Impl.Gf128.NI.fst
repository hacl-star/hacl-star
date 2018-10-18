module Hacl.Impl.Gf128.NI

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open LowStar.Buffer
open Lib.Utils
open Lib.Vec128


inline_for_extraction
let cl_add (x:vec128) (y:vec128) : vec128 = vec128_xor x y
inline_for_extraction
let clmul_wide (x:vec128) (y:vec128) : vec128 * vec128 = 
    let lo = ni_clmul x y (u8 0x00) in
    let m1 = ni_clmul x y (u8 0x10) in
    let m2 = ni_clmul x y (u8 0x01) in
    let hi = ni_clmul x y (u8 0x11) in
    let m1 = cl_add m1 m2 in
    let m2 = vec128_shift_left m1 (size 64) in
    let m1 = vec128_shift_right m1 (size 64) in
    let lo = cl_add lo m2 in
    let hi = cl_add hi m1 in
    (hi,lo)

inline_for_extraction
let clmul_wide4 (x1:vec128) (x2:vec128) (x3:vec128) (x4:vec128) 
		(y1:vec128) (y2:vec128) (y3:vec128) (y4:vec128): 
		vec128 * vec128 = 
    let lo1 = ni_clmul x1 y1 (u8 0x00) in
    let lo2 = ni_clmul x2 y2 (u8 0x00) in
    let lo3 = ni_clmul x3 y3 (u8 0x00) in
    let lo4 = ni_clmul x4 y4 (u8 0x00) in
    let lo = cl_add lo1 lo2 in
    let lo = cl_add lo lo3 in
    let lo = cl_add lo lo4 in
    
    let m1 = ni_clmul x1 y1 (u8 0x10) in
    let m2 = ni_clmul x2 y2 (u8 0x10) in
    let m3 = ni_clmul x3 y3 (u8 0x10) in
    let m4 = ni_clmul x4 y4 (u8 0x10) in
    let m = cl_add m1 m2 in
    let m = cl_add m m3 in
    let m = cl_add m m4 in

    let m1 = ni_clmul x1 y1 (u8 0x01) in
    let m2 = ni_clmul x2 y2 (u8 0x01) in
    let m3 = ni_clmul x3 y3 (u8 0x01) in
    let m4 = ni_clmul x4 y4 (u8 0x01) in
    let m = cl_add m m1 in
    let m = cl_add m m2 in
    let m = cl_add m m3 in
    let m = cl_add m m4 in

    let hi1 = ni_clmul x1 y1 (u8 0x11) in
    let hi2 = ni_clmul x2 y2 (u8 0x11) in
    let hi3 = ni_clmul x3 y3 (u8 0x11) in
    let hi4 = ni_clmul x4 y4 (u8 0x11) in
    let hi = cl_add hi1 hi2 in
    let hi = cl_add hi hi3 in
    let hi = cl_add hi hi4 in

    let m1 = vec128_shift_left m (size 64) in
    let m2 = vec128_shift_right m (size 64) in
    let lo = cl_add lo m1 in
    let hi = cl_add hi m2 in
    (hi,lo)

inline_for_extraction
let vec128_shift_left_bits (x:vec128) (y:size_t) : vec128 = 
  if (y %. size 8 = size 0) then 
      vec128_shift_left x y 
  else if (y <. size 64) then 
      let x1 = vec128_shift_right64 x (size 64 -. y) in
      let x2 = vec128_shift_left64 x y in
      let x3 = vec128_shift_left x1 (size 64) in
      let x4 = vec128_or x3 x2 in
      x4
  else 
      let x1 = vec128_shift_left64 x (y -. size 64) in
      let x2 = vec128_shift_left x1 (size 64) in
      x2

inline_for_extraction
let vec128_shift_right_bits (x:vec128) (y:size_t) : vec128 = 
  if (y %. size 8 = size 0) then 
      vec128_shift_right x y 
  else if (y <. size 64) then 
      let x1 = vec128_shift_left64 x (size 64 -. y) in
      let x2 = vec128_shift_right64 x y in
      let x3 = vec128_shift_right x1 (size 64) in
      let x4 = vec128_or x3 x2 in
      x4
  else 
      let x1 = vec128_shift_right64 x (y -. size 64) in
      let x2 = vec128_shift_right x1 (size 64) in
      x2

inline_for_extraction
let gf128_reduce (hi:vec128) (lo:vec128) : vec128 = 
    (* LEFT SHIFT [hi:lo] by 1 *)
    let lo1 = vec128_shift_right64 lo (size 63) in
    let lo2 = vec128_shift_left lo1 (size 64) in
    let lo3 = vec128_shift_left64 lo (size 1) in
    let lo3 = vec128_xor lo3 lo2 in

    let hi1 = vec128_shift_right64 hi (size 63) in
    let hi1 = vec128_shift_left hi1 (size 64) in
    let hi2 = vec128_shift_left64 hi (size 1) in
    let hi2 = vec128_xor hi2 hi1 in

    let lo1 = vec128_shift_right64 lo (size 63) in
    let lo1 = vec128_shift_right lo1 (size 64) in
    let hi2 = vec128_xor hi2 lo1 in
    
    let lo = lo3 in
    let hi = hi2 in
(*
    let lo1 = vec128_shift_right_bits lo (size 127) in
    let lo = vec128_shift_left_bits lo (size 1) in
    let hi = vec128_shift_left_bits hi (size 1) in
    let hi = vec128_xor hi lo1 in
*)
    (* LEFT SHIFT [x0:0] BY 63,62,57 and xor with [x1:x0] *)
    let lo1 = vec128_shift_left64 lo (size 63) in
    let lo2 = vec128_shift_left64 lo (size 62) in
    let lo3 = vec128_shift_left64 lo (size 57) in
    let lo1 = vec128_xor lo1 lo2 in
    let lo1 = vec128_xor lo1 lo3 in
    let lo2 = vec128_shift_right lo1 (size 64) in
    let lo3 = vec128_shift_left lo1 (size 64) in
    let lo =  vec128_xor lo lo3 in    
    let lo' = lo2 in

    (* RIGHT SHIFT [x1:x0] BY 1,2,7 and xor with [x1:x0] *)
    let lo1 = vec128_shift_right64 lo (size 1) in
    let lo2 = vec128_shift_right64 lo (size 2) in
    let lo3 = vec128_shift_right64 lo (size 7) in
    let lo1 = vec128_xor lo1 lo2 in
    let lo1 = vec128_xor lo1 lo3 in
    
    let lo1 = vec128_xor lo1 lo' in
    let lo = vec128_xor lo lo1 in

    let lo = vec128_xor lo hi in
    lo



let felem = lbuffer vec128 1
let felem4 = lbuffer vec128 4
type precomp = lbuffer vec128 4
type block = lbytes 16
type block4 = lbytes 64

inline_for_extraction
val fadd: x:felem -> y:felem -> Stack unit
	  (requires (fun h -> live h x /\ live h y))
	  (ensures (fun h0 _ h1 -> live h1 x /\ live h1 y /\ modifies (loc_buffer x) h0 h1))
let fadd (x:felem) (y:felem) = 
    x.(size 0) <- cl_add x.(size 0) y.(size 0)


inline_for_extraction
val fmul: x:felem -> y:felem -> Stack unit
	  (requires (fun h -> live h x /\ live h y))
	  (ensures (fun h0 _ h1 -> live h1 x /\ live h1 y /\ modifies (loc_buffer x) h0 h1))
let fmul (x:felem) (y:felem) = 
    let xe = x.(size 0) in
    let ye = y.(size 0) in
    let (hi,lo) = clmul_wide xe ye in
    let lo = gf128_reduce hi lo in
    x.(size 0) <- lo

  

inline_for_extraction
val fadd_mul4: acc:felem -> x:felem4 -> y:felem4 -> Stack unit
	  (requires (fun h -> live h acc /\ live h x /\ live h y))
	  (ensures (fun h0 _ h1 -> modifies (loc_buffer acc) h0 h1))
let fadd_mul4 (acc:felem) (x:felem4) (y:felem4) = 
    let x1 = x.(size 0) in
    let x2 = x.(size 1) in
    let x3 = x.(size 2) in
    let x4 = x.(size 3) in
    let y1 = y.(size 0) in
    let y2 = y.(size 1) in
    let y3 = y.(size 2) in
    let y4 = y.(size 3) in
    let acc0 = acc.(size 0) in
    let x1 = cl_add x1 acc0 in
    let (hi,lo) = clmul_wide4 x1 x2 x3 x4 y1 y2 y3 y4 in
    let lo = gf128_reduce hi lo in
    acc.(size 0) <- lo

inline_for_extraction
val encode: x:felem -> y:lbytes 16 -> Stack unit
	  (requires (fun h -> live h x /\ live h y))
	  (ensures (fun h0 _ h1 -> live h1 x /\ live h1 y /\ modifies (loc_buffer x) h0 h1))
let encode x y = 
    x.(size 0) <- vec128_load_be y

inline_for_extraction
val encode4: x:felem4 -> y:lbytes 64 -> Stack unit
	  (requires (fun h -> live h x /\ live h y))
	  (ensures (fun h0 _ h1 -> live h1 x /\ live h1 y /\ modifies (loc_buffer x) h0 h1))
let encode4 x y = 
    x.(size 0) <- vec128_load_be (sub y (size 0) (size 16));
    x.(size 1) <- vec128_load_be (sub y (size 16) (size 16));
    x.(size 2) <- vec128_load_be (sub y (size 32) (size 16));
    x.(size 3) <- vec128_load_be (sub y (size 48) (size 16))

inline_for_extraction
val encode_last: x:felem -> y:bytes -> len:size_t{length y == size_v len} -> Stack unit
	  (requires (fun h -> live h x /\ live h y))
	  (ensures (fun h0 _ h1 -> live h1 x /\ live h1 y /\ modifies (loc_buffer x) h0 h1))
let encode_last x y len = 
    push_frame();
    let b = alloca 0uy 16ul in
    blit y (size 0) b (size 0) len;
    encode x b;
    pop_frame()

inline_for_extraction
val decode: x:lbytes 16 -> y:felem -> Stack unit
	  (requires (fun h -> live h x /\ live h y))
	  (ensures (fun h0 _ h1 -> live h1 x /\ live h1 y /\ modifies (loc_buffer x) h0 h1))
let decode x y = 
    vec128_store_be x y.(size 0)


inline_for_extraction
val update: acc:felem -> x:lbytes 16 -> y:felem -> Stack unit
	  (requires (fun h -> live h x /\ live h y /\ live h acc))
	  (ensures (fun h0 _ h1 -> live h1 x /\ live h1 y /\ live h1 acc /\ modifies (loc_buffer acc) h0 h1))

let update acc x y = 
    push_frame();
    let elem = alloca vec128_zero 1ul in
    encode elem x;  
    fadd acc elem;
    fmul acc y;
    pop_frame()
    


inline_for_extraction
val update_last: acc:felem -> x:bytes -> len:size_t{size_v len == length x} -> y:felem -> Stack unit
	  (requires (fun h -> live h x /\ live h y /\ live h acc))
	  (ensures (fun h0 _ h1 -> live h1 x /\ live h1 y /\ live h1 acc /\ modifies (loc_buffer acc) h0 h1))

let update_last acc x l y = 
    push_frame();
    let elem = alloca vec128_zero 1ul in
    encode_last elem x l;  
    fadd acc elem;
    fmul acc y;
    pop_frame()


inline_for_extraction
val poly: acc:felem -> text:bytes -> len:size_t{length text == size_v len} -> r:felem -> Stack unit
	  (requires (fun h -> live h acc /\ live h text /\ live h r))
	  (ensures (fun h0 _ h1 -> modifies (loc_buffer acc) h0 h1))
let poly acc text len r = 
    push_frame ();
    let blocks = len /. size 16 in
    let h0 = ST.get() in
    loop_nospec #h0 blocks acc 
      (fun i -> update acc (sub text (i *. size 16) (size 16)) r);
    let rem = len %. size 16 in
    if (rem >. size 0) then (
       let last = sub text (blocks *. size 16) rem in
       update_last acc last rem r);
    pop_frame()


[@ CInline]
val poly4: acc:felem -> text:bytes -> len:size_t{length text == size_v len} -> r4:felem4 -> Stack unit
	  (requires (fun h -> live h acc /\ live h text /\ live h r4))
	  (ensures (fun h0 _ h1 -> modifies (loc_buffer acc) h0 h1))
[@ CInline]
let poly4 acc text len r4 = 
    push_frame ();
    let tmp = alloca vec128_zero 1ul in
    let b4 = alloca vec128_zero 4ul in
    let blocks = len /. size 64 in
    let h0 = ST.get() in
    loop_nospec #h0 blocks acc 
      (fun i -> encode4 b4 (sub text (i *. size 64) (size 64)); 
             fadd_mul4 acc b4 r4);
    let rem = len %. size 64 in
    let last = sub text (blocks *. size 64) rem in
    poly acc last rem (sub r4 (size 3) (size 1));
    pop_frame()

inline_for_extraction
val gcm_alloc: unit -> StackInline (felem * felem4)
	  (requires (fun h -> True))
	  (ensures (fun h0 (x,y) h1 -> modifies (loc_union (loc_buffer x) (loc_buffer y)) h0 h1))
let gcm_alloc () = 
  let acc = alloca vec128_zero 1ul in
  let r4 = alloca vec128_zero 4ul in
  (acc,r4)

[@ CInline ]
val gcm_init: acc:felem -> r4:felem4 -> key:lbytes 16 -> Stack unit
	  (requires (fun h -> live h acc /\ live h r4 /\ live h key))
	  (ensures (fun h0 _ h1 -> modifies (loc_union (loc_buffer acc) (loc_buffer r4)) h0 h1))
[@ CInline ]
let gcm_init acc r4 key = 
    let r_4 = sub r4 (size 0) (size 1) in
    let r_3 = sub r4 (size 1) (size 1) in
    let r_2 = sub r4 (size 2) (size 1) in
    let r   = sub r4 (size 3) (size 1) in
    encode r key;
    r4.(size 0) <- r.(size 0);
    r4.(size 1) <- r.(size 0);
    r4.(size 2) <- r.(size 0);
    fmul r_2 r;
    fmul r_3 r_2;
    fmul r_4 r_3
    
  
[@ CInline ]
val ghash: tag:lbytes 16 -> text:bytes -> len:size_t{length text == size_v len} -> key:lbytes 16 -> Stack unit
	  (requires (fun h -> live h tag /\ live h text /\ live h key))
	  (ensures (fun h0 _ h1 -> modifies (loc_buffer tag) h0 h1))
[@ CInline ]
let ghash tag text len key = 
  push_frame();
  let (acc,r4) = gcm_alloc () in
  gcm_init acc r4 key;
  poly4 acc text len r4;
  decode tag acc;
  pop_frame()
