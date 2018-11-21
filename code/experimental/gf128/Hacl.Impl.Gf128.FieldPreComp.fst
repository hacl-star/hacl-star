module Hacl.Impl.Gf128.FieldPreComp

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

type felem = lbuffer uint64 2ul
type felem4 = lbuffer uint64 8ul
type table = lbuffer uint64 256ul // r4(8) + table(256)
type precomp = lbuffer uint64 264ul // r4(8) + table(256)
type block = lbuffer uint8 16ul
type block4 = lbuffer uint8 64ul
type gcm_ctx = lbuffer uint64 266ul // acc + precomp

inline_for_extraction
let bit_mask64 (u:uint64) = u64 0 -. (u &. u64 1)

inline_for_extraction
val felem_set_zero: f:felem -> StackInline unit
	  (requires (fun h -> live h f))
	  (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))    
let felem_set_zero f =  f.(0ul) <- u64 0; f.(1ul) <- u64 0


inline_for_extraction
val load_felem: x:felem -> y:block -> Stack unit
	  (requires (fun h -> live h x /\ live h y))
	  (ensures (fun h0 _ h1 -> live h1 x /\ live h1 y /\ modifies (loc x) h0 h1))
let load_felem x y = 
   x.(size 1) <- uint_from_bytes_be #U64 (sub y (size 0) (size 8));
   x.(size 0) <- uint_from_bytes_be #U64 (sub y (size 8) (size 8))

inline_for_extraction
val load_felem4: x:felem4 -> y:block4 -> Stack unit
	  (requires (fun h -> live h x /\ live h y))
	  (ensures (fun h0 _ h1 -> live h1 x /\ live h1 y /\ modifies (loc x) h0 h1))
let load_felem4 x y = 
   load_felem (sub x (size 0) (size 2)) (sub y (size 0) (size 16));
   load_felem (sub x (size 2) (size 2)) (sub y (size 16) (size 16));
   load_felem (sub x (size 4) (size 2)) (sub y (size 32) (size 16));
   load_felem (sub x (size 6) (size 2)) (sub y (size 48) (size 16))

inline_for_extraction
val store_felem: x:lbuffer uint8 16ul -> y:felem -> Stack unit
	  (requires (fun h -> live h x /\ live h y))
	  (ensures (fun h0 _ h1 -> live h1 x /\ live h1 y /\ modifies (loc x) h0 h1))
let store_felem x y = 
   uint_to_bytes_be #U64 (sub x (size 0) (size 8)) y.(size 1);
   uint_to_bytes_be #U64 (sub x (size 8) (size 8)) y.(size 0)

inline_for_extraction
val get_acc: ctx:gcm_ctx -> Stack felem
	     (requires (fun h -> live h ctx))
	     (ensures (fun h0 f h1 -> h0 == h1 /\ live h1 f))
let get_acc (ctx:gcm_ctx) = 
  sub ctx (size 0) (size 2)

inline_for_extraction
val get_r: ctx:gcm_ctx -> Stack felem
	     (requires (fun h -> live h ctx))
	     (ensures (fun h0 f h1 -> h0 == h1 /\ live h1 f))
let get_r (ctx:gcm_ctx) = 
  sub ctx (size 8) (size 2)

inline_for_extraction
val get_precomp: ctx:gcm_ctx -> Stack precomp
	     (requires (fun h -> live h ctx))
	     (ensures (fun h0 f h1 -> h0 == h1 /\ live h1 f))
let get_precomp (ctx:gcm_ctx) = 
  sub ctx (size 2) (size 264)


[@ "c_inline" ]
val prepare: pre:table -> r:felem -> Stack unit
	  (requires (fun h -> live h pre /\ live h r))
	  (ensures (fun h0 _ h1 -> modifies (loc pre) h0 h1))
let prepare pre r = 
    push_frame();
    let sh = create 2ul (u64 0) in
    sh.(size 0) <- r.(size 0);
    sh.(size 1) <- r.(size 1);
    let h0 = ST.get() in
    loop_nospec #h0 (size 128) pre //footprint should include sh
      (fun i -> 
	let s0 = sh.(size 0) in
	let s1 = sh.(size 1) in
	pre.(i *. size 2) <- s0;
	pre.(size 1 +. i *. size 2) <- s1;
	let m = bit_mask64 s0 in
        sh.(size 0) <- (s0 >>. size 1) |. (s1 <<. size 63);
        sh.(size 1) <- (s1 >>. size 1) ^. (m &. u64 0xE100000000000000);
	admit());
    pop_frame()

inline_for_extraction
val fadd: x:felem -> y:felem -> Stack unit
	  (requires (fun h -> live h x /\ live h y))
	  (ensures (fun h0 _ h1 -> live h1 x /\ live h1 y /\ modifies (loc x) h0 h1))
let fadd (x:felem) (y:felem) = 
    x.(size 0) <- x.(size 0) ^. y.(size 0);
    x.(size 1) <- x.(size 1) ^. y.(size 1)

inline_for_extraction
val fadd4: x:felem4 -> y:felem4 -> Stack unit
	  (requires (fun h -> live h x /\ live h y))
	  (ensures (fun h0 _ h1 -> live h1 x /\ live h1 y /\ modifies (loc x) h0 h1))
let fadd4 (x:felem4) (y:felem4) = 
    fadd (sub x (size 0) (size 2)) (sub y (size 0) (size 2));
    fadd (sub x (size 2) (size 2)) (sub y (size 2) (size 2));
    fadd (sub x (size 4) (size 2)) (sub y (size 4) (size 2));
    fadd (sub x (size 6) (size 2)) (sub y (size 6) (size 2))

[@ "c_inline" ]
val fmul: x:felem -> y:felem -> Stack unit
	  (requires (fun h -> live h x /\ live h y))
	  (ensures (fun h0 _ h1 -> live h1 x /\ live h1 y /\ modifies (loc x) h0 h1))
let fmul (x:felem) (y:felem) = 
    push_frame();
    let tmp = create 2ul (u64 0) in
    let sh = create 2ul (u64 0) in
    sh.(size 0) <- y.(size 0);
    sh.(size 1) <- y.(size 1);
    let h0 = ST.get() in
    admit();
    loop_nospec #h0 (size 64) tmp // + sh
      (fun i -> 
	let s0 = sh.(size 0) in
	let s1 = sh.(size 1) in
	let m = bit_mask64 (x.(size 1) >>. (size 63 -. i)) in
	tmp.(size 0) <- tmp.(size 0) ^. (m &. s0);
	tmp.(size 1) <- tmp.(size 1) ^. (m &. s1);
	let s = bit_mask64 s0 in
        sh.(size 0) <- (s0 >>. size 1) |. (s1 <<. size 63);
        sh.(size 1) <- (s1 >>. size 1) ^. (s &. u64 0xE100000000000000));
    loop_nospec #h0 (size 64) tmp // + sh
      (fun i -> 
	let s0 = sh.(size 0) in
	let s1 = sh.(size 1) in
	let m = bit_mask64 (x.(size 0) >>. (size 63 -. i)) in
	tmp.(size 0) <- tmp.(size 0) ^. (m &. s0);
	tmp.(size 1) <- tmp.(size 1) ^. (m &. s1);
	let s = bit_mask64 s0 in
        sh.(size 0) <- (s0 >>. size 1) |. (s1 <<. size 63);
        sh.(size 1) <- (s1 >>. size 1) ^. (s &. u64 0xE100000000000000));
    x.(size 0) <- tmp.(size 0);
    x.(size 1) <- tmp.(size 1);
    pop_frame()

[@ "c_inline" ]
val load_precompute_r: pre:precomp -> key:block -> Stack unit
	  (requires (fun h -> live h pre /\ live h key))
	  (ensures (fun h0 _ h1 -> modifies (loc pre) h0 h1))
let load_precompute_r pre key = 
  let r4 = sub pre (size 0) (size 8) in
  let table = sub pre (size 8) (size 256) in
  let r = sub r4 (size 6) (size 2) in
  let r_2 = sub r4 (size 4) (size 2) in
  let r_3 = sub r4 (size 2) (size 2) in
  let r_4 = sub r4 (size 0) (size 2) in
  load_felem r key;
  r_3.(size 0) <- r.(size 0);
  r_3.(size 1) <- r.(size 1);
  r_2.(size 0) <- r.(size 0);
  r_2.(size 1) <- r.(size 1);
  fmul r_2 r;
  fmul r_3 r_2;
  r_4.(size 0) <- r_2.(size 0);
  r_4.(size 1) <- r_2.(size 1);
  fmul r_4 r_2;
  prepare table r_4;
  admit()

[@ "c_inline" ]
val fmul_pre: x:felem -> pre:precomp -> Stack unit
	  (requires (fun h -> live h x /\ live h pre))
	  (ensures (fun h0 _ h1 -> live h1 x /\ live h1 pre /\ modifies (loc x) h0 h1))
let fmul_pre (x:felem) (pre:precomp) = 
    push_frame();
    let tab = sub pre (size 8) (size 256) in
    let tmp = create 2ul (u64 0) in
    let h0 = ST.get() in
    admit();
    loop_nospec #h0 (size 64) tmp
      (fun i -> 
	let m = bit_mask64 (x.(size 1) >>. (size 63 -. i)) in
	tmp.(size 0) <- tmp.(size 0) ^. (m &. tab.(i *. size 2));
	tmp.(size 1) <- tmp.(size 1) ^. (m &. tab.(size 1 +. i *. size 2)));
    loop_nospec #h0 (size 64) tmp
      (fun i -> 
	let m = bit_mask64 (x.(size 0) >>. (size 63 -. i)) in
	tmp.(size 0) <- tmp.(size 0) ^. (m &. tab.(size 128 +. i *. size 2));
	tmp.(size 1) <- tmp.(size 1) ^. (m &. tab.(size 129 +. i *. size 2)));
    x.(size 0) <- tmp.(size 0);
    x.(size 1) <- tmp.(size 1);
    pop_frame()



inline_for_extraction
val fmul4: x:felem4 -> pre:precomp -> Stack unit
	  (requires (fun h -> live h x /\ live h pre))
	  (ensures (fun h0 _ h1 -> live h1 x /\ live h1 pre /\ modifies (loc x) h0 h1))
let fmul4 (x:felem4) (pre:precomp) = 
    fmul_pre (sub x (size 0) (size 2)) pre;
    fmul_pre (sub x (size 2) (size 2)) pre;
    fmul_pre (sub x (size 4) (size 2)) pre;
    fmul_pre (sub x (size 6) (size 2)) pre

inline_for_extraction
val fadd_mul4: acc:felem -> x:felem4 -> pre:precomp -> Stack unit
	  (requires (fun h -> live h acc /\ live h x /\ live h pre))
	  (ensures (fun h0 _ h1 -> modifies (loc acc) h0 h1))
let fadd_mul4 (acc:felem) (x:felem4) (pre:precomp) = 
    let x1 = sub x (size 0) (size 2) in
    let x2 = sub x (size 2) (size 2) in
    let x3 = sub x (size 4) (size 2) in
    let x4 = sub x (size 6) (size 2) in
    fadd acc x1;
    fmul_pre acc pre;
    fadd acc x2;
    fmul_pre acc pre;
    fadd acc x3;
    fmul_pre acc pre;
    fadd acc x4;
    fmul_pre acc pre
