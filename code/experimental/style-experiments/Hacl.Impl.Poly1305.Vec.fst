module Hacl.Impl.Poly1305.Vec

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open LowStar.Buffer
open Lib.Utils

open Hacl.Impl.Poly1305.Fields

inline_for_extraction
val poly1305_encode_block: #s:field_spec -> f:felem s -> b:lbytes 16 -> Stack unit
                   (requires (fun h -> live h b /\ live h f ))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1))
let poly1305_encode_block #s f b = 
    load_felem_le f b;
    set_bit128 f 

inline_for_extraction
val poly1305_encode_blocks: #s:field_spec -> f:felem s -> b:lbytes 16 -> Stack unit
                   (requires (fun h -> live h b /\ live h f ))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1))
let poly1305_encode_blocks #s f b = 
    load_felems_le f b;
    set_bit128 f 

inline_for_extraction
val poly1305_encode_last: #s:field_spec -> f:felem s -> b:bytes -> 
			len:size_t{size_v len == length b /\ length b < 16} -> Stack unit
                   (requires (fun h -> live h b /\ live h f ))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1))
#reset-options "--z3rlimit 100"
let poly1305_encode_last #s f b len = 
    push_frame();
    let tmp = create 0uy (size (blocklen s)) in
    blit b (size 0) tmp (size 0) len;
    load_felem_le f tmp;
    set_bit f (len *. size 8);
    admit();
    pop_frame()

inline_for_extraction
val poly1305_encode_r: #s:field_spec -> f:felem s -> b:lbytes 16 -> Stack unit
                   (requires (fun h -> live h b /\ live h f ))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1))
let poly1305_encode_r #s f b = 
    push_frame();
    let tmp = create 0uy (size (blocklen s)) in
    let (lo,hi) = load64x2_le b in
    let mask0 = u64 0x0ffffffc0fffffff in
    let mask1 = u64 0x0ffffffc0ffffffc in
    let lo = lo &. mask0 in
    let hi = hi &. mask1 in
    let nblocks = (size (blocklen s)) /. size 16 in
    let h0 = ST.get () in
    loop_nospec #h0 nblocks tmp (
      fun i -> store64x2_le (sub tmp (i *. size 16) (size 16)) lo hi
      );
    load_felem_le f tmp;
    admit();
    pop_frame()
  
inline_for_extraction
type poly1305_ctx (s:field_spec) = lbuffer (limb s) (nlimb s `op_Multiply` (1 + 2 `op_Multiply` (blocklen s / 32)))

inline_for_extraction 
let get_acc #s (ctx:poly1305_ctx s) = sub ctx (size 0) (size (nlimb s))

inline_for_extraction
let get_r #s (ctx:poly1305_ctx s) = sub ctx (size (nlimb s) *. size 1) (size (nlimb s))

inline_for_extraction
let get_s #s (ctx:poly1305_ctx s) = sub ctx (size (nlimb s) *. size 2) (size (nlimb s))

inline_for_extraction
let get_precomp #s (ctx:poly1305_ctx s) = sub ctx (size (nlimb s) *. size 3) (size (nlimb s) *. (size 1 +. size 2 *. size (blocklen s) /. size 32))



inline_for_extraction
val poly1305_init: #s:field_spec -> ctx:poly1305_ctx s -> key:lbytes 32 -> Stack unit
                   (requires (fun h -> live h ctx /\ live h key))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer ctx) h0 h1))
let poly1305_init #s ctx key = 
  let kr = sub key (size 0) (size 16) in
  let ks = sub key (size 16) (size 16) in
  let tmp = create 0uy (size (blocklen s)) in
  let acc = get_acc ctx in
  let r = get_r ctx in
  let precomp = get_precomp ctx in
  let sk = get_s ctx in 
  set_zero acc;
  poly1305_encode_r r kr;
  precompute_shift_reduce precomp r;
  blit ks (size 0) tmp (size 0) (size 16);
  load_felem_le sk tmp;
  admit()


inline_for_extraction
val poly1305_blocks: #s:field_spec -> ctx:poly1305_ctx s -> text:bytes -> len:size_t{size_v len == length text} -> key:lbytes 32 -> Stack unit
                   (requires (fun h -> live h ctx /\ live h text))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer ctx) h0 h1))

let poly1305_blocks #s ctx text len = 
  push_frame();
  let elem = create (limb_zero s) (size (nlimb s)) in
  let sz_block = size (blocklen s) in
  let blocks = len /. sz_block in
  let acc = get_acc ctx in
  let precomp = get_precomp ctx in
  let h0 = ST.get() in
  admit();
  loop_nospec #h0 blocks acc 
    (fun i ->
       let b = sub text (i *. sz_block) sz_block in
       poly1305_encode_blocks #s elem b;
       fmul_add #s acc elem precomp);
  fmul_reduce_n #s acc precomp;
  
  let rem = len %. sz_block in
  let remb = rem /. size 16 in
  loop_nospec #h0 remb acc 
    (fun i ->
       let b = sub text (blocks *. sz_block +. i *. size 16) (size 16) in
       poly1305_encode_block elem tmp;
       fadd_mul acc elem vr precomp
    );

  let rem = rem %. size 16 in
  if (rem >. size 0) then (
       let b = sub text (blocks *. sz_block + remb *. size 16) rem in
       poly1305_encode_last elem b rem;
       fadd_mul acc elem vr precomp
  );
  pop_frame()


inline_for_extraction
val poly1305_finish: #s:field_spec -> ctx:poly1305_ctx s -> tag:lbytes 16 -> Stack unit 
		     (requires (fun h -> live h ctx /\ live h tag))
		     (ensures (fun h0 _ h1 -> modifies (loc_buffer tag) h0 h1))
		  
let poly1305_finish #s ctx tag = 
  let acc = get_acc ctx in
  let sk = get_s ctx in
  reduce_felem acc;
  fadd acc acc sk;
  store_felem_le tag acc;
  admit()


inline_for_extraction
val poly1305_mac1: tag:lbytes 16 -> text:bytes -> len:size_t{size_v len == length text} -> key:lbytes 32 -> Stack unit
                   (requires (fun h -> live h tag /\ live h text))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer tag) h0 h1))

let poly1305_mac1 tag text len key = 
  push_frame();
  let kr = sub key (size 0) (size 16) in
  let ks = sub key (size 16) (size 16) in

  let vr = alloca Lib.Vec128.vec128_zero 5ul in
  let vr2 = alloca Lib.Vec128.vec128_zero 5ul in
  let precomp = alloca Lib.Vec128.vec128_zero 5ul in
  let vacc = alloca Lib.Vec128.vec128_zero 5ul in
  let elem = alloca Lib.Vec128.vec128_zero 5ul in
  poly1305_encode_r vr kr;
  precompute_shift_reduce precomp vr;
//  fmul vr2 vr vr precomp;
//  precompute_shift_reduce precomp vr2;
//  let blocks = len /. size 32 in
  let blocks = len /. size 16 in
  let tmp = create 0uy (size 32) in
  let h0 = ST.get() in
  admit();
  loop_nospec #h0 blocks vacc 
    (fun i ->
       let b = sub text (i *. size 16) (size 16) in
       blit b (size 0) tmp (size 0) (size 16);
       poly1305_encode_block #M128 elem tmp;
       Hacl.Impl.Poly1305.Field128.fadd_mul vacc elem vr precomp);
//  loop_nospec #h0 (size 5) vr2 
//    (fun i -> vr2.(i) <- Lib.Vec128.vec128_interleave_low64 vr.(i) vr2.(i));
//  precompute_shift_reduce precomp vr2;
//  Hacl.Impl.Poly1305.Field128.fmul vacc vacc vr2 precomp;
  
//  loop_nospec #h0 (size 5) vacc 
//    (fun i -> vacc.(i) <- Lib.Vec128.vec128_add64 vacc.(i) (Lib.Vec128.vec128_shift_right vacc.(i) (size 64))); 
//  let rem = len %. size 32 in
//  let remb = rem /. size 16 in
//  precompute_shift_reduce precomp vr;
//  loop_nospec #h0 remb vacc 
//    (fun i ->
//       let b = sub text (blocks *. size 32 +. i *. size 16) (size 16) in
//       blit b (size 0) tmp (size 0) (size 16);
//       poly1305_encode_block #M128 elem tmp;
//       Hacl.Impl.Poly1305.Field128.fadd_mul vacc elem vr precomp
//       );


  let rem = len %. size 16 in
  if (rem >. size 0) then (
       let b = sub text (blocks *. size 16) rem in
       poly1305_encode_last #M128 elem b rem;
       Hacl.Impl.Poly1305.Field128.fadd_mul vacc elem vr precomp
  );

  reduce_felem vacc;
  blit ks (size 0) tmp (size 0) (size 16);
  load_felem_le elem tmp;
  fadd vacc vacc elem;
  store_felem_le tmp vacc;
  blit tmp (size 0) tag (size 0) (size 16);
  pop_frame()


inline_for_extraction
val poly1305_mac2: tag:lbytes 16 -> text:bytes -> len:size_t{size_v len == length text} -> key:lbytes 32 -> Stack unit
                   (requires (fun h -> live h tag /\ live h text))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer tag) h0 h1))

let poly1305_mac2 tag text len key = 
  push_frame();
  let kr = sub key (size 0) (size 16) in
  let ks = sub key (size 16) (size 16) in

  let vr = alloca Lib.Vec128.vec128_zero 5ul in
  let vr2 = alloca Lib.Vec128.vec128_zero 5ul in
  let precomp = alloca Lib.Vec128.vec128_zero 5ul in
  let vacc = alloca Lib.Vec128.vec128_zero 5ul in
  let elem = alloca Lib.Vec128.vec128_zero 5ul in
  poly1305_encode_r vr kr;
  precompute_shift_reduce precomp vr;
  fmul vr2 vr vr precomp;
  precompute_shift_reduce precomp vr2;
  let blocks = len /. size 32 in
  let tmp = create 0uy (size 32) in
  let h0 = ST.get() in
  admit();
  loop_nospec #h0 blocks vacc 
    (fun i ->
       let b = sub text (i *. size 32) (size 32) in
       poly1305_encode_block #M128 elem b;
       Hacl.Impl.Poly1305.Field128.fmul vacc vacc vr2 precomp;
       Hacl.Impl.Poly1305.Field128.fadd vacc vacc elem
       );
  loop_nospec #h0 (size 5) vr2 
    (fun i -> vr2.(i) <- Lib.Vec128.vec128_interleave_low64 vr2.(i) vr.(i));
  precompute_shift_reduce precomp vr2;
  Hacl.Impl.Poly1305.Field128.fmul vacc vacc vr2 precomp;
  
  loop_nospec #h0 (size 5) vacc 
    (fun i -> vacc.(i) <- Lib.Vec128.vec128_add64 vacc.(i) (Lib.Vec128.vec128_shift_right vacc.(i) (size 64))); 
  let rem = len %. size 32 in
  let remb = rem /. size 16 in
  precompute_shift_reduce precomp vr;
  loop_nospec #h0 remb vacc 
    (fun i ->
       let b = sub text (blocks *. size 32 +. i *. size 16) (size 16) in
       blit b (size 0) tmp (size 0) (size 16);
       poly1305_encode_block #M128 elem tmp;
       Hacl.Impl.Poly1305.Field128.fadd_mul vacc elem vr precomp
       );
  let rem = rem %. size 16 in
  if (rem >. size 0) then (
       let b = sub text (blocks *. size 32 +. remb *. size 16) rem in
       poly1305_encode_last #M128 elem b rem;
       Hacl.Impl.Poly1305.Field128.fadd_mul vacc elem vr precomp
  );
  reduce_felem vacc;
  blit ks (size 0) tmp (size 0) (size 16);
  load_felem_le elem tmp;
  fadd vacc vacc elem;
  store_felem_le tmp vacc;
  blit tmp (size 0) tag (size 0) (size 16);
  pop_frame()



inline_for_extraction
val poly1305_mac: tag:lbytes 16 -> text:bytes -> len:size_t{size_v len == length text} -> key:lbytes 32 -> Stack unit
                   (requires (fun h -> live h tag /\ live h text))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer tag) h0 h1))

let poly1305_mac tag text len key = 
  push_frame();
  let kr = sub key (size 0) (size 16) in
  let ks = sub key (size 16) (size 16) in

  let vr = alloca Lib.Vec256.vec256_zero 5ul in
  let vr2 = alloca Lib.Vec256.vec256_zero 5ul in
  let vr4 = alloca Lib.Vec256.vec256_zero 5ul in
  let precomp = alloca Lib.Vec256.vec256_zero 5ul in
  let vacc = alloca Lib.Vec256.vec256_zero 5ul in
  let elem = alloca Lib.Vec256.vec256_zero 5ul in
  poly1305_encode_r vr kr;
  precompute_shift_reduce precomp vr;
  fmul vr2 vr vr precomp;
  precompute_shift_reduce precomp vr2;
  fmul vr4 vr2 vr2 precomp;
  let h0 = ST.get() in
  loop_nospec #h0 (size 5) vr2
    (fun i -> let v1212 = Lib.Vec256.vec256_interleave_low64 vr2.(i) vr.(i) in
           let v1234 = Lib.Vec256.vec256_mul64 v1212 (Lib.Vec256.vec256_shift_right vr2.(i) (size 128)) in
	   vr2.(i) <- v1234);

  precompute_shift_reduce precomp vr4;
  let blocks = len /. size 64 in
  let tmp = create 0uy (size 64) in
  let h0 = ST.get() in
  admit();
  loop_nospec #h0 blocks vacc 
    (fun i ->
       let b = sub text (i *. size 64) (size 64) in
       poly1305_encode_block elem b;
       Hacl.Impl.Poly1305.Field256.fmul vacc vacc vr4 precomp;
       Hacl.Impl.Poly1305.Field256.fadd vacc vacc elem
       );
       
  precompute_shift_reduce precomp vr2;
  Hacl.Impl.Poly1305.Field256.fmul vacc vacc vr2 precomp;
  
  loop_nospec #h0 (size 5) vacc 
    (fun i -> let v = vacc.(i) in
           let v = Lib.Vec256.vec256_add64 v (Lib.Vec256.vec256_shift_right v (size 128)) in
           let v = Lib.Vec256.vec256_add64 v (Lib.Vec256.vec256_shift_right v (size 64)) in
	   vacc.(i) <- v);
  let rem = len %. size 64 in
  let remb = rem /. size 16 in
  precompute_shift_reduce precomp vr;
  loop_nospec #h0 remb vacc 
    (fun i ->
       let b = sub text (blocks *. size 32 +. i *. size 16) (size 16) in
       blit b (size 0) tmp (size 0) (size 16);
       poly1305_encode_block elem tmp;
       Hacl.Impl.Poly1305.Field256.fadd_mul vacc elem vr precomp
       );
  let rem = rem %. size 16 in
  if (rem >. size 0) then (
       let b = sub text (blocks *. size 32 +. remb *. size 16) rem in
       poly1305_encode_last #M256 elem b rem;
       Hacl.Impl.Poly1305.Field256.fadd_mul vacc elem vr precomp
  );
  Hacl.Impl.Poly1305.Field256.reduce_felem vacc;
  blit ks (size 0) tmp (size 0) (size 16);
  Hacl.Impl.Poly1305.Field256.load_felem_le elem tmp;
  Hacl.Impl.Poly1305.Field256.fadd vacc vacc elem;
  Hacl.Impl.Poly1305.Field256.store_felem_le tmp vacc;
  blit tmp (size 0) tag (size 0) (size 16);
  pop_frame()


