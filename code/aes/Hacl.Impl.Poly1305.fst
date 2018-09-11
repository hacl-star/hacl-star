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
    let (lo,hi) = load64x2_le b in
    load_felem f lo hi;
    set_bit128 f 

inline_for_extraction
val poly1305_encode_last: #s:field_spec -> f:felem s -> b:bytes -> 
			len:size_t{size_v len == length b /\ length b < 16} -> Stack unit
                   (requires (fun h -> live h b /\ live h f ))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1))
#reset-options "--z3rlimit 100"
let poly1305_encode_last #s f b len = 
    push_frame();
    let tmp = create 0uy (size 16) in
    blit b (size 0) tmp (size 0) len;
    let (lo,hi) = load64x2_le tmp in
    load_felem f lo hi;
    set_bit f (len *. size 8);
    admit();
    pop_frame()

inline_for_extraction
val poly1305_encode_r: #s:field_spec -> f:felem s -> b:lbytes 16 -> Stack unit
                   (requires (fun h -> live h b /\ live h f ))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer f) h0 h1))
let poly1305_encode_r #s f b = 
    let (lo,hi) = load64x2_le b in
    let mask0 = u64 0x0ffffffc0fffffff in
    let mask1 = u64 0x0ffffffc0ffffffc in
    let lo = lo &. mask0 in
    let hi = hi &. mask1 in
    load_felem f lo hi
  

type poly1305_ctx (s:field_spec) = lbuffer (limb s) (nlimb s `op_Multiply` 4)

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
val get_r: #s:field_spec -> ctx:poly1305_ctx s -> Stack (felem s)
                   (requires (fun h -> live h ctx))
		   (ensures (fun h0 r h1 -> h0 == h1 /\ live h1 r))
*)
inline_for_extraction
let get_r #s (ctx:poly1305_ctx s) = sub ctx (size (nlimb s)) (size (nlimb s))

(*
inline_for_extraction
val get_r_20: #s:field_spec -> ctx:poly1305_ctx s -> Stack (felem s)
                   (requires (fun h -> live h ctx))
		   (ensures (fun h0 r h1 -> h0 == h1 /\ live h1 r))
*)
inline_for_extraction
let get_r_20 #s (ctx:poly1305_ctx s) = sub ctx (size (nlimb s) *. size 2) (size (nlimb s))

(*
inline_for_extraction
val get_s: #s:field_spec -> ctx:poly1305_ctx s -> Stack (felem s)
                   (requires (fun h -> live h ctx))
		   (ensures (fun h0 r h1 -> h0 == h1 /\ live h1 r))
*)
inline_for_extraction
let get_s #s (ctx:poly1305_ctx s) = sub ctx (size (nlimb s) *. size 3) (size (nlimb s))


inline_for_extraction
val poly1305_init: #s:field_spec -> ctx:poly1305_ctx s -> key:lbytes 32 -> Stack unit
                   (requires (fun h -> live h ctx /\ live h key))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer ctx) h0 h1))
let poly1305_init #s ctx key = 
  let kr = sub key (size 0) (size 16) in
  let ks = sub key (size 16) (size 16) in
  
  let acc = get_acc ctx in
  let r = get_r ctx in
  let r_20 = get_r_20 ctx in
  let sk = get_s ctx in 
  set_zero acc;
  poly1305_encode_r r kr;
  smul_top_felem r_20 r;
  let (sl,sh) = load64x2_le ks in
  load_felem sk sl sh;
  admit()

inline_for_extraction
val poly1305_update: #s:field_spec -> ctx:poly1305_ctx s -> text:bytes -> len:size_t{size_v len == length text} -> Stack unit
                   (requires (fun h -> live h ctx /\ live h text))
		   (ensures (fun h0 _ h1 -> modifies (loc_buffer ctx) h0 h1))

let poly1305_update #s ctx text len = 
  push_frame();
  let acc = get_acc ctx in
  let r = get_r ctx in
  let r_20 = get_r_20 ctx in
  let e = create (limb_zero s) (size (nlimb s)) in
  let blocks = len /. size 16 in
  let h0 = ST.get() in
  admit();
  loop_nospec #h0 blocks ctx 
    (fun i ->
       let b = sub text (i *. size 16) (size 16) in
       poly1305_encode_block e b;
       fadd_mul_felem acc e r r_20);
  let rem = len %. size 16 in
  if (rem >. size 0) then (
     let b = sub text (blocks *. size 16) (size 16) in
     poly1305_encode_last e b rem;
     fadd_mul_felem acc e r r_20);
  pop_frame()

inline_for_extraction
val poly1305_finish: #s:field_spec -> ctx:poly1305_ctx s -> tag:lbytes 16 -> Stack unit 
		     (requires (fun h -> live h ctx /\ live h tag))
		     (ensures (fun h0 _ h1 -> modifies (loc_buffer tag) h0 h1))
		  
let poly1305_finish #s ctx tag = 
  let acc = get_acc ctx in
  let sk = get_s ctx in
  carry_felem acc;
  carry_top_felem acc;
//  carry_felem acc;
//  carry_top_felem acc;
  add_felem acc sk;
  carry_felem acc;
  let (lo,hi) = store_felem acc in
  store64x2_le tag lo hi;
  admit()


inline_for_extraction
val poly1305_mac: #s:field_spec -> tag:lbytes 16 -> text:bytes -> len:size_t{size_v len == length text} -> key:lbytes 32 -> Stack unit 
		     (requires (fun h -> live h text /\ live h tag /\ live h key))
 		     (ensures (fun h0 _ h1 -> modifies (loc_buffer tag) h0 h1))
let poly1305_mac #s tag text len key = 
  push_frame();
  let ctx : lbuffer (limb s) (nlimb s `op_Multiply` 4) = create (limb_zero s) (size (nlimb s) *. size 4) in
  poly1305_init ctx key;
  poly1305_update ctx text len;
  poly1305_finish ctx tag;
  pop_frame()
