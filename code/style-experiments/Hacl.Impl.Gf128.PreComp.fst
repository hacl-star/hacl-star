module Hacl.Impl.Gf128.PreComp

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open LowStar.Buffer
open Lib.Utils
open Lib.Vec128

open Hacl.Impl.Gf128.FieldPreComp

inline_for_extraction
val encode: x:felem -> y:lbytes 16 -> Stack unit
	  (requires (fun h -> live h x /\ live h y))
	  (ensures (fun h0 _ h1 -> live h1 x /\ live h1 y /\ modifies (loc_buffer x) h0 h1))
let encode x y = load_felem x y

inline_for_extraction
val encode4: x:felem4 -> y:lbytes 64 -> Stack unit
	  (requires (fun h -> live h x /\ live h y))
	  (ensures (fun h0 _ h1 -> live h1 x /\ live h1 y /\ modifies (loc_buffer x) h0 h1))
let encode4 x y = load_felem4 x y
   
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
let decode x y = store_felem x y

    
inline_for_extraction
val update: acc:felem -> x:felem -> pre:precomp -> Stack unit
	  (requires (fun h -> live h x /\ live h pre /\ live h acc))
	  (ensures (fun h0 _ h1 -> live h1 x /\ live h1 pre /\ live h1 acc /\ modifies (loc_buffer acc) h0 h1))
let update acc x pre = 
    fadd acc x;
    fmul acc pre 

[@ "c_inline" ]
val poly: acc:felem -> text:bytes -> len:size_t{length text == size_v len} -> pre:precomp -> Stack unit
	  (requires (fun h -> live h acc /\ live h text /\ live h pre))
	  (ensures (fun h0 _ h1 -> modifies (loc_buffer acc) h0 h1))
let poly acc text len pre = 
    push_frame ();
    let elem = alloca (u64 0) 2ul in
    let blocks = len /. size 16 in
    let h0 = ST.get() in
    loop_nospec #h0 blocks acc 
      (fun i -> encode elem (sub text (i *. size 16) (size 16)); 
             update acc elem pre
      );
    let rem = len %. size 16 in
    if (rem >. size 0) then (
       let last = sub text (blocks *. size 16) rem in
       encode_last elem last rem;
       update acc elem pre
    );
    pop_frame()


[@ "c_inline" ]
val poly4: acc:felem -> text:bytes -> len:size_t{length text == size_v len} -> pre:precomp -> r4:felem4 -> Stack unit
	  (requires (fun h -> live h acc /\ live h text /\ live h pre /\ live h r4))
	  (ensures (fun h0 _ h1 -> modifies (loc_buffer acc) h0 h1))
let poly4 acc text len pre r4 = 
    push_frame ();
    let tmp = alloca (u64 0) 8ul in
    let acc4 = alloca (u64 0) 8ul in
    let blocks = len /. size 64 in
    let h0 = ST.get() in
    loop_nospec #h0 blocks acc 
      (fun i -> encode4 tmp (sub text (i *. size 64) (size 64)); 
	     fmul4 acc4 pre;
             fadd4 acc4 tmp);
    fmul_reduce (sub acc4 (size 0) (size 2)) (sub r4 (size 0) (size 2));
    fmul_reduce (sub acc4 (size 2) (size 2)) (sub r4 (size 2) (size 2));
    fmul_reduce (sub acc4 (size 4) (size 2)) (sub r4 (size 4) (size 2));
    fmul_reduce (sub acc4 (size 6) (size 2)) (sub r4 (size 6) (size 2));
    acc.(size 0) <- acc4.(size 0);
    acc.(size 1) <- acc4.(size 1);
    fadd acc (sub acc4 (size 2) (size 2));
    fadd acc (sub acc4 (size 4) (size 2));
    fadd acc (sub acc4 (size 6) (size 2));
    let rem = len %. size 64 in
    let last = sub text (blocks *. size 64) rem in 
    poly acc last rem pre;
    pop_frame()

val ghash: tag:lbytes 16 -> text:bytes -> len:size_t{length text == size_v len} -> key:lbytes 16 -> Stack unit
	  (requires (fun h -> live h tag /\ live h text /\ live h key))
	  (ensures (fun h0 _ h1 -> modifies (loc_buffer tag) h0 h1))

let ghash tag text len key = 
  push_frame();
  let ctx = create_ctx() in
  let acc = alloca (u64 0) 2ul in
  let r4 = alloca (u64 0) 8ul in
  let r = sub r4 (size 6) (size 2) in
  let r_2 = sub r4 (size 4) (size 2) in
  let r_3 = sub r4 (size 2) (size 2) in
  let r_4 = sub r4 (size 0) (size 2) in
  let pre = alloca (u64 0) 256ul in
  encode r key;
  r_3.(size 0) <- r.(size 0);
  r_3.(size 1) <- r.(size 1);
  r_2.(size 0) <- r.(size 0);
  r_2.(size 1) <- r.(size 1);
  fmul_reduce r_2 r;
  fmul_reduce r_3 r_2;
  r_4.(size 0) <- r_2.(size 0);
  r_4.(size 1) <- r_2.(size 1);
  fmul_reduce r_4 r_2;
  prepare pre r_4;
  poly4 acc text len pre r4;
  decode tag acc;
  pop_frame()


val ghash1: tag:lbytes 16 -> text:bytes -> len:size_t{length text == size_v len} -> key:lbytes 16 -> Stack unit
	  (requires (fun h -> live h tag /\ live h text /\ live h key))
	  (ensures (fun h0 _ h1 -> modifies (loc_buffer tag) h0 h1))

let ghash1 tag text len key = 
  push_frame();
  let r = alloca (u64 0) 2ul in
  let acc = alloca (u64 0) 2ul in
  let pre = alloca (u64 0) 256ul in
  encode r key;
  prepare pre r;
  poly acc text len pre;
  decode tag acc;
  pop_frame()
