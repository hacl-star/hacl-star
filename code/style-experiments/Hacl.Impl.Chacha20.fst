module Hacl.Impl.Chacha20

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open LowStar.Buffer
open Lib.Utils

open Hacl.Impl.Chacha20.Core32

//inline_for_extraction
[@ CInline]
val rounds: st:state -> ST unit
		  (requires (fun h -> live h st))
		  (ensures (fun h0 _ h1 -> modifies (loc_buffer st) h0 h1))
[@ CInline]
let rounds st =
  double_round st;
  double_round st;
  double_round st;
  double_round st;
  double_round st;
  double_round st;
  double_round st;
  double_round st;
  double_round st;
  double_round st

[@ CInline ]
val chacha20_core: k:state -> ctx:state -> ST unit
		  (requires (fun h -> live h ctx /\ live h k))
		  (ensures (fun h0 _ h1 -> modifies (loc_buffer k) h0 h1))
[@ CInline ]
let chacha20_core k ctx =
    copy_state k ctx;
    rounds k;
    sum_state k ctx

//val chacha20_constants: lbuffer 
let chacha20_constants = 
  gcreateL [0x65uy;0x78uy;0x70uy;0x61uy;
	    0x6euy;0x64uy;0x20uy;0x33uy;
	    0x32uy;0x2duy;0x62uy;0x79uy;
	    0x74uy;0x65uy;0x20uy;0x6buy]


inline_for_extraction
val chacha20_init: ctx:state -> k:lbytes 32 -> n:lbytes 12 -> ST unit
		  (requires (fun h -> live h ctx /\ live h k /\ live h n))
		  (ensures (fun h0 _ h1 -> modifies (loc_buffer ctx) h0 h1))
[@ CInline]
let chacha20_init ctx k n =
    push_frame();
    let tmp = create 0uy (size 64) in
    blit chacha20_constants (size 0) tmp (size 0) (size 16);
    blit k (size 0) tmp (size 16) (size 32);
    blit n (size 0) tmp (size 52) (size 12);
    load_state ctx tmp;
    pop_frame()


inline_for_extraction
val chacha20_update: out:bytes -> ctx:state -> ctr:size_t -> text:bytes -> len:size_t{size_v len == length text /\ size_v len == length out} -> ST unit
		  (requires (fun h -> live h ctx /\ live h text /\ live h out))
		  (ensures (fun h0 _ h1 -> modifies (loc_union (loc_buffer ctx) (loc_buffer out)) h0 h1))
[@ CInline ]
let chacha20_update out ctx ctr text len =
  push_frame();
  let k = create_state () in
  let blocks = len /. size 64 in
  let h0 = ST.get() in
  loop_nospec #h0 blocks out 
    (fun i -> set_counter ctx (ctr +. i); 
	   chacha20_core k ctx; 
	   let ib = sub text (size 64 *. i) (size 64) in
	   let ob = sub out (size 64 *. i) (size 64) in
	   xor_block ob k ib
	   );
  let rem = len %. size 64 in
  if (rem >. size 0) then (
    let tmp = create 0uy (size 64) in
    blit text (size 64 *. blocks) tmp (size 0) rem;
    set_counter ctx (ctr +. blocks); 
    chacha20_core k ctx; 
    xor_block tmp ctx tmp;
    blit tmp (size 0) out (size 64 *. blocks) rem);
  pop_frame()

inline_for_extraction
val chacha20_encrypt: out:bytes -> text:bytes -> len:size_t{size_v len == length text /\ size_v len == length out} -> key:lbytes 32 -> n:lbytes 12 -> ctr:size_t -> ST unit
		  (requires (fun h -> live h key /\ live h n -> live h text /\ live h out))
		  (ensures (fun h0 _ h1 -> modifies (loc_buffer out) h0 h1))
let chacha20_encrypt out text len key n ctr = 
    push_frame();
    let ctx = create_state () in
    chacha20_init ctx key n;
    chacha20_update out ctx ctr text len;
    pop_frame()


inline_for_extraction
val chacha20_decrypt: out:bytes -> text:bytes -> len:size_t{size_v len == length text /\ size_v len == length out} -> key:lbytes 32 -> n:lbytes 12 -> ctr:size_t -> ST unit
		  (requires (fun h -> live h key /\ live h n -> live h text /\ live h out))
		  (ensures (fun h0 _ h1 -> modifies (loc_buffer out) h0 h1))
let chacha20_decrypt out text len key n ctr = 
    push_frame();
    let ctx = create_state () in
    chacha20_init ctx key n;
    chacha20_update out ctx ctr text len;
    pop_frame()


