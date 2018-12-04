module Hacl.Impl.Chacha20

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Chacha20.Core32

//inline_for_extraction
[@ CInline]
val rounds: st:state -> ST unit
		  (requires (fun h -> live h st))
		  (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1))
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
		  (requires (fun h -> live h ctx /\ live h k /\ disjoint ctx k))
		  (ensures (fun h0 _ h1 -> modifies (loc k) h0 h1))
[@ CInline ]
let chacha20_core k ctx =
    copy_state k ctx;
    rounds k;
    sum_state k ctx


inline_for_extraction noextract
let chacha20_constants_spec : Lib.Sequence.lseq byte_t 16 = 
  [@ inline_let]
  let l =  [0x65uy;0x78uy;0x70uy;0x61uy;
	    0x6euy;0x64uy;0x20uy;0x33uy;
	    0x32uy;0x2duy;0x62uy;0x79uy;
	    0x74uy;0x65uy;0x20uy;0x6buy] in
  assert_norm (List.Tot.length l == 16);
  Lib.Sequence.createL l

val chacha20_constants: b:ilbuffer byte_t 16ul{recallable b /\ witnessed b chacha20_constants_spec} 
let chacha20_constants = 
  [@ inline_let]
  let l =  [0x65uy;0x78uy;0x70uy;0x61uy;
	    0x6euy;0x64uy;0x20uy;0x33uy;
	    0x32uy;0x2duy;0x62uy;0x79uy;
	    0x74uy;0x65uy;0x20uy;0x6buy] in
  assert_norm (List.Tot.length l == 16);
  createL_global l


inline_for_extraction
val chacha20_init: ctx:state -> k:lbuffer uint8 32ul -> n:lbuffer uint8 12ul -> ST unit
		  (requires (fun h -> live h ctx /\ live h k /\ live h n))
		  (ensures (fun h0 _ h1 -> modifies (loc ctx) h0 h1))

#set-options "--z3rlimit 100"
[@ CInline]
let chacha20_init ctx k n =
    push_frame();
    recall_contents chacha20_constants chacha20_constants_spec;
    let tmp = create 64ul (u8 0) in
    let tmp_c = sub tmp 0ul 16ul in
    assert (disjoint tmp_c chacha20_constants);
    mapT 16ul tmp_c secret chacha20_constants;
    copy (sub tmp 16ul 32ul) k;
    copy (sub tmp 52ul 12ul) n;
    load_state ctx tmp;
    pop_frame()


inline_for_extraction
val chacha20_update: ctx:state -> len:size_t -> out:lbuffer uint8 len -> text:lbuffer uint8 len -> ctr:size_t -> ST unit
		  (requires (fun h -> 
			    live h ctx /\ 
			    live h text /\ 
			    live h out /\ 
			    disjoint text ctx /\
			    disjoint out ctx))
		  (ensures (fun h0 _ h1 -> modifies (loc ctx |+| loc out) h0 h1))
[@ CInline ]
let chacha20_update ctx len out text ctr =
  push_frame();
  let k = create_state () in
  let blocks = len /. size 64 in
  let h0 = ST.get() in
  loop2 h0 blocks out ctx
    (fun h -> (fun i bufs -> bufs))
    (fun i -> assert (live h0 ctx);
	   set_counter ctx (ctr +. i); 
	   chacha20_core k ctx; 
	   let ib = sub text (size 64 *. i) (size 64) in
	   let ob = sub out (size 64 *. i) (size 64) in
	   xor_block ob k ib;
	   admit()
	   );
  let rem = len %. size 64 in
  if (rem >. size 0) then (
    let tmp = create (size 64) (u8 0) in
    let tmp_l = sub tmp 0ul rem in
    let text_l = sub text (size 64 *. blocks) rem in
    assume (disjoint text_l tmp_l);
    copy tmp_l text_l;
    set_counter ctx (ctr +. blocks); 
    chacha20_core k ctx; 
    xor_block tmp ctx tmp;
    copy (sub out (size 64 *. blocks) rem) (sub tmp 0ul rem));
  admit();
  pop_frame()



inline_for_extraction
val chacha20_encrypt: len:size_t -> out:lbuffer uint8 len -> text:lbuffer uint8 len -> key:lbuffer uint8 32ul -> n:lbuffer uint8 12ul -> ctr:size_t -> ST unit
		  (requires (fun h -> live h key /\ live h n /\ live h text /\ live h out))
		  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
let chacha20_encrypt len out text key n ctr = 
    push_frame();
    let ctx = create_state () in
    chacha20_init ctx key n;
    chacha20_update ctx len out text ctr;
    pop_frame()


inline_for_extraction
val chacha20_decrypt: len:size_t -> out:lbuffer uint8 len -> text:lbuffer uint8 len -> key:lbuffer uint8 32ul -> n:lbuffer uint8 12ul -> ctr:size_t -> ST unit
		  (requires (fun h -> live h key /\ live h n /\ live h text /\ live h out))
		  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
let chacha20_decrypt len out text key n ctr = 
    push_frame();
    let ctx = create_state () in
    chacha20_init ctx key n;
    chacha20_update ctx len out text ctr;
    pop_frame()


