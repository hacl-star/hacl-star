module Hacl.Impl.Poly1305

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
val poly1305_encode_blocks: #s:field_spec -> f:felem s -> b:lbytes (blocklen s) -> Stack unit
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
#reset-options "--z3rlimit 200"
let poly1305_encode_last #s f b len = 
    push_frame();
    let tmp = create 0uy (size 16) in
    blit b (size 0) tmp (size 0) len;
    load_felem_le f tmp;
    set_bit f (len *. size 8);
    pop_frame()

inline_for_extraction
val poly1305_encode_r: #s:field_spec -> p:precomp_r s -> b:lbytes 16 -> Stack unit
                   (requires (fun h -> live h b /\ live h p ))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer p) h0 h1))
let poly1305_encode_r #s p b = 
    let (lo,hi) = load64x2_le b in
    let mask0 = u64 0x0ffffffc0fffffff in
    let mask1 = u64 0x0ffffffc0ffffffc in
    let lo = lo &. mask0 in
    let hi = hi &. mask1 in
    load_precompute_r p lo hi

  
inline_for_extraction
type poly1305_ctx (s:field_spec) = lbuffer (limb s) (nlimb s `op_Multiply` 2 + precomplen s)

(*
inline_for_extraction
val get_acc: #s:field_spec -> ctx:poly1305_ctx s -> Stack (felem s)
                   (requires (fun h -> live h ctx))
		   (ensures (fun h0 r h1 -> h0 == h1 /\ live h1 r))
*)
inline_for_extraction 
let get_acc #s (ctx:poly1305_ctx s) = sub ctx (size 0) (size (nlimb s))


(*
inline_for_extraction
val get_precomp_r: #s:field_spec -> ctx:poly1305_ctx s -> Stack (precomp_r s)
                   (requires (fun h -> live h ctx))
		   (ensures (fun h0 r h1 -> h0 == h1 /\ live h1 r))
*)
inline_for_extraction
let get_precomp_r #s (ctx:poly1305_ctx s) = sub ctx (size (nlimb s)) (size (precomplen s))

(*
inline_for_extraction
val get_s: #s:field_spec -> ctx:poly1305_ctx s -> Stack (felem s)
                   (requires (fun h -> live h ctx))
		   (ensures (fun h0 r h1 -> h0 == h1 /\ live h1 r))
*)
inline_for_extraction
let get_s #s (ctx:poly1305_ctx s) = sub ctx (size (nlimb s) +. size (precomplen s)) (size (nlimb s))


inline_for_extraction
val poly1305_init: #s:field_spec -> ctx:poly1305_ctx s -> key:lbytes 32 -> Stack unit
                   (requires (fun h -> live h ctx /\ live h key))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer ctx) h0 h1))
let poly1305_init #s ctx key = 
  let kr = sub key (size 0) (size 16) in
  let ks = sub key (size 16) (size 16) in
  
  let acc = get_acc ctx in
  let precomp_r = get_precomp_r ctx in
  let sk = get_s ctx in 
  set_zero acc;
  poly1305_encode_r precomp_r kr;
  load_felem_le sk ks;
  admit()


inline_for_extraction
val poly1305_nblocks: #s:field_spec -> ctx:poly1305_ctx s -> text:bytes -> len:size_t{size_v len == length text /\ size_v len % blocklen s == 0} -> Stack unit
                   (requires (fun h -> live h ctx /\ live h text))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer ctx) h0 h1))

let poly1305_nblocks #s ctx text len = 
  push_frame();
  let acc = get_acc ctx in
  let pre = get_precomp_r ctx in
  let e = create (limb_zero s) (size (nlimb s)) in
  let sz_block = size (blocklen s) in
  let blocks = len /. sz_block  in
  let h0 = ST.get() in
  admit();
  loop_nospec #h0 blocks ctx 
    (fun i ->
       let b = sub text (i *. sz_block) sz_block in
       poly1305_encode_blocks e b;
       fmul_rn acc acc pre;
       fadd acc acc e);
  fmul_rn_normalize acc pre;
  pop_frame()

inline_for_extraction
val poly1305_update: #s:field_spec -> ctx:poly1305_ctx s -> text:bytes -> len:size_t{size_v len == length text} -> Stack unit
                   (requires (fun h -> live h ctx /\ live h text))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer ctx) h0 h1))

let poly1305_update #s ctx text len = 
  push_frame();
  let acc = get_acc ctx in
  let pre = get_precomp_r ctx in
  let sz_block = size (blocklen s) in
  let len0 = if sz_block >. size 16 then (len /. sz_block) *. sz_block else size 0 in
  if (sz_block >. size 16) then (
    let t0 = sub text (size 0) len0 in
    poly1305_nblocks ctx t0 len0
  );
  let len = len -. len0 in
  let text = sub text len0 len in
  let e = create (limb_zero s) (size (nlimb s)) in
  let blocks = len /. size 16 in
  let h0 = ST.get() in
  admit();
  loop_nospec #h0 blocks ctx 
    (fun i ->
       let b = sub text (i *. size 16) (size 16) in
       poly1305_encode_block e b;
       fadd_mul_r acc e pre);
  let rem = len %. size 16 in
  if (rem >. size 0) then (
     let b = sub text (blocks *. size 16) (size 16) in
     poly1305_encode_last e b rem;
     fadd_mul_r acc e pre);
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
val poly1305_mac: #s:field_spec -> tag:lbytes 16 -> text:bytes -> len:size_t{size_v len == length text} -> key:lbytes 32 -> Stack unit 
		     (requires (fun h -> live h text /\ live h tag /\ live h key))
 		     (ensures (fun h0 _ h1 -> modifies (loc_buffer tag) h0 h1))
let poly1305_mac #s tag text len key = 
  push_frame();
  let ctx = create (limb_zero s) (size (nlimb s) *. size 2 +. size (precomplen s)) in
  poly1305_init ctx key;
  poly1305_update ctx text len;
  poly1305_finish ctx tag;
  pop_frame()

