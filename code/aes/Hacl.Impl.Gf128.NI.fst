module Hacl.Impl.Gf128.NI

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open LowStar.Buffer
open Lib.Vec128

type lbuffer a len = b:buffer a{length b == len}
type bytes = buffer FStar.UInt8.t
type lbytes l = b:bytes {length b == l} 

inline_for_extraction 
val blit: #a:Type -> src:buffer a -> start1:size_t -> dst:buffer a -> start2:size_t -> len:size_t -> ST unit
               (requires (fun h -> live h src /\ live h dst)) (ensures (fun h0 _ h1 -> live h1 src /\ live h1 dst /\ modifies (loc_buffer dst) h0 h1))
let blit #a src start1 dst start2 len = 
    blit src (Lib.RawIntTypes.size_to_UInt32 start1) dst (Lib.RawIntTypes.size_to_UInt32 start2) (Lib.RawIntTypes.size_to_UInt32 len) 

inline_for_extraction 
val load64_le: b:lbytes 8 -> ST uint64 
               (requires (fun h -> live h b)) (ensures (fun h0 _ h1 -> h0 == h1))
let load64_le b = 
    let u = C.Endianness.load64_le b in
    Lib.RawIntTypes.u64_from_UInt64 u

inline_for_extraction 
val store64_le: b:lbytes 8 -> u:uint64 -> ST unit
               (requires (fun h -> live h b)) (ensures (fun h0 _ h1 -> live h1 b /\ modifies (loc_buffer b) h0 h1))
let store64_le b u = 
    C.Endianness.store64_le b (Lib.RawIntTypes.u64_to_UInt64 u)

inline_for_extraction 
val store32_be: b:lbytes 4 -> u:uint32 -> ST unit
               (requires (fun h -> live h b)) (ensures (fun h0 _ h1 -> live h1 b /\ modifies (loc_buffer b) h0 h1))
let store32_be b u = 
    C.Endianness.store32_be b (Lib.RawIntTypes.u32_to_UInt32 u)

inline_for_extraction 
val gcreateL: #a:Type -> l:list a -> ST (buffer a)
	      (requires (fun h -> True))
	      (ensures (fun h0 b h1 -> recallable b /\ length b == List.Tot.length l))
let gcreateL #a l = 
    gcmalloc_of_list FStar.HyperStack.root l


inline_for_extraction
val sub: #a:Type -> b:buffer a -> i:size_t -> j:size_t -> ST (buffer a) 
         (requires (fun h -> live h b)) (ensures (fun h0 _ h1 -> h0 == h1))
let sub #a b i j = Lib.RawIntTypes.(sub b (size_to_UInt32 i) (size_to_UInt32 j))

inline_for_extraction 
val loop_nospec: #h0:mem -> #a:Type -> n:size_t -> buf:buffer a -> 
		 impl:(size_t -> ST unit (requires (fun h -> live h buf)) (ensures (fun h0 _ h1 -> modifies (loc_buffer buf) h0 h1 /\ live h1 buf))) -> ST unit 
         (requires (fun h -> live h buf)) (ensures (fun h0 _ h1 -> live h1 buf /\ modifies (loc_buffer buf) h0 h1))
inline_for_extraction 
let loop_nospec #h0 #a (n:size_t) (buf:buffer a) impl =
  let inv (h1:mem) (j:nat) = True in
  let f' (j:UInt32.t{0 <= UInt32.v j /\ UInt32.v j <= size_v n}) : Stack unit
      (requires (fun h -> inv h (UInt32.v j)))
      (ensures (fun h1 _ h2 -> inv h2 (UInt32.v j + 1))) =
      impl (Lib.RawIntTypes.size_from_UInt32 j) in
  C.Loops.for 0ul (Lib.RawIntTypes.size_to_UInt32 n) inv f'

inline_for_extraction
let op_Array_Assignment #a #b #c buf i v = upd #a #b #c buf (Lib.RawIntTypes.size_to_UInt32 i) v
inline_for_extraction
let op_Array_Access #a #b #c buf i  = index #a #b #c buf (Lib.RawIntTypes.size_to_UInt32 i)

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
val update: acc:felem -> x:felem -> y:felem -> Stack unit
	  (requires (fun h -> live h x /\ live h y /\ live h acc))
	  (ensures (fun h0 _ h1 -> live h1 x /\ live h1 y /\ live h1 acc /\ modifies (loc_buffer acc) h0 h1))

let update acc x y = 
    fadd acc x;
    fmul acc y


inline_for_extraction
val poly: acc:felem -> text:bytes -> len:size_t{length text == size_v len} -> r:felem -> Stack unit
	  (requires (fun h -> live h acc /\ live h text /\ live h r))
	  (ensures (fun h0 _ h1 -> modifies (loc_buffer acc) h0 h1))
let poly acc text len r = 
    push_frame ();
    let elem = alloca vec128_zero 1ul in
    let blocks = len /. size 16 in
    let h0 = ST.get() in
    loop_nospec #h0 blocks acc 
      (fun i -> encode elem (sub text (i *. size 16) (size 16)); 
             update acc elem r
      );
    let rem = len %. size 16 in
    if (rem >. size 0) then (
       let last = sub text (blocks *. size 16) rem in
       encode_last elem last rem;
       update acc elem r
    );
    pop_frame()


inline_for_extraction
val poly4: acc:felem -> text:bytes -> len:size_t{length text == size_v len} -> r:felem -> Stack unit
	  (requires (fun h -> live h acc /\ live h text /\ live h r))
	  (ensures (fun h0 _ h1 -> modifies (loc_buffer acc) h0 h1))
let poly4 acc text len r = 
    push_frame ();
    let tmp = alloca vec128_zero 1ul in
    let b4 = alloca vec128_zero 4ul in
    let r4 = alloca vec128_zero 4ul in
    let r_4 = sub r4 (size 0) (size 1) in
    let r_3 = sub r4 (size 1) (size 1) in
    let r_2 = sub r4 (size 2) (size 1) in
    r4.(size 0) <- r.(size 0);
    r4.(size 1) <- r.(size 0);
    r4.(size 2) <- r.(size 0);
    r4.(size 3) <- r.(size 0);
    fmul r_2 r;
    fmul r_3 r_2;
    fmul r_4 r_3;

    let blocks = len /. size 64 in
    let h0 = ST.get() in
    loop_nospec #h0 blocks acc 
      (fun i -> encode4 b4 (sub text (i *. size 64) (size 64)); 
             fadd_mul4 acc b4 r4);
    let rem = len %. size 64 in
    let blocks16 = rem /. size 16 in
    let h0 = ST.get() in
    loop_nospec #h0 blocks16 acc 
      (fun i -> encode tmp (sub text ((i *. size 16) +. (blocks *. size 64)) (size 16));
	     update acc tmp r);
    let rem = rem %. size 16 in
    if (rem >. size 0) then (
       let last = sub text ((blocks16 *. size 16) +. (blocks *. size 64)) rem in
       encode_last tmp last rem;
       update acc tmp r
    );
    pop_frame()

inline_for_extraction
val ghash: tag:lbytes 16 -> text:bytes -> len:size_t{length text == size_v len} -> key:lbytes 16 -> Stack unit
	  (requires (fun h -> live h tag /\ live h text /\ live h key))
	  (ensures (fun h0 _ h1 -> modifies (loc_buffer tag) h0 h1))

let ghash tag text len key = 
  push_frame();
  let r = alloca vec128_zero 1ul in
  let acc = alloca vec128_zero 1ul in
  encode r key;
  poly4 acc text len r;
  decode tag acc;
  pop_frame()
