module Hacl.Impl.Chacha20.Vec

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.IntVector
open FStar.Mul
open Hacl.Impl.Chacha20.Core32xN
module Spec = Hacl.Spec.Chacha20.Vec
module Loop = Lib.LoopCombinators

#set-options "--z3rlimit 100"
#set-options "--debug Hacl.Impl.Chacha20.Vec --debug_level ExtractNorm"

inline_for_extraction
val rounds: #w:lanes -> st:state w -> ST unit
		  (requires (fun h -> live h st))
		  (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1 /\
		    as_seq h1 st == Spec.rounds (as_seq h0 st)))

[@ CInline]
let rounds #w st =
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
	  
inline_for_extraction
val chacha20_core_: #w:lanes -> k:state w -> ctx0:state w -> ctr:size_t{w * v ctr <= max_size_t}  -> ST unit
		  (requires (fun h -> live h ctx0 /\ live h k /\ disjoint ctx0 k))
		  (ensures (fun h0 _ h1 -> modifies (loc k) h0 h1 /\
					as_seq h1 k == Spec.chacha20_core (v ctr) (as_seq h0 ctx0)))


let chacha20_core_ #w k ctx ctr =
    copy_state k ctx;
    let ctr_u32 = u32 w *! size_to_uint32 ctr in
    let cv = vec_load ctr_u32 w in
    k.(12ul) <- k.(12ul) +| cv;
    rounds k;
    sum_state k ctx;
    k.(12ul) <- k.(12ul) +| cv


[@CInline]
let chacha20_core1 k ctx0 ctr = chacha20_core_ #1 k ctx0 ctr
[@CInline]
let chacha20_core4 k ctx0 ctr = chacha20_core_ #4 k ctx0 ctr
[@CInline]
let chacha20_core8 k ctx0 ctr = chacha20_core_ #8 k ctx0 ctr

inline_for_extraction
val chacha20_core: #w:lanes -> k:state w -> ctx0:state w -> ctr:size_t{w * v ctr <= max_size_t} -> ST unit
		  (requires (fun h -> live h ctx0 /\ live h k /\ disjoint ctx0 k))
		  (ensures (fun h0 _ h1 -> modifies (loc k) h0 h1 /\
					as_seq h1 k == Spec.chacha20_core (v ctr) (as_seq h0 ctx0)))
let chacha20_core #w k ctx ctr =
  match w with
  | 1 -> chacha20_core1 k ctx ctr
  | 4 -> chacha20_core4 k ctx ctr
  | 8 -> chacha20_core8 k ctx ctr
  

val chacha20_constants: b:ilbuffer size_t 4ul{
			recallable b /\
			witnessed b Spec.Chacha20.chacha20_constants}
let chacha20_constants =
  [@ inline_let]
  let l = [Spec.c0;Spec.c1;Spec.c2;Spec.c3] in
  assert_norm(List.Tot.length l == 4);
  createL_global l
  

inline_for_extraction
val setup1: ctx:lbuffer uint32 16ul -> k:lbuffer uint8 32ul -> n:lbuffer uint8 12ul -> ctr0:size_t -> ST unit
		  (requires (fun h -> live h ctx /\ live h k /\ live h n /\ disjoint ctx k /\ disjoint ctx n /\ as_seq h ctx == Lib.Sequence.create 16 (u32 0)))
		  (ensures (fun h0 _ h1 -> modifies (loc ctx) h0 h1 /\
			   as_seq h1 ctx == Spec.setup1 (as_seq h0 k) (as_seq h0 n) (v ctr0)))
#set-options "--z3rlimit 300"
inline_for_extraction
let setup1 ctx k n ctr =
    let h0 = ST.get() in
    recall_contents chacha20_constants Spec.chacha20_constants;
    update_sub_f h0 ctx 0ul 4ul
      (fun h -> Lib.Sequence.map secret Spec.chacha20_constants)
      (fun b -> mapT 4ul b secret chacha20_constants);
    let h1 = ST.get() in
    update_sub_f h1 ctx 4ul 8ul
      (fun h -> Lib.ByteSequence.uints_from_bytes_le (as_seq h k))
      (fun b -> uints_from_bytes_le b k);
    let h2 = ST.get() in
    ctx.(12ul) <- size_to_uint32 ctr;
    let h3 = ST.get() in
    update_sub_f h3 ctx 13ul 3ul
      (fun h -> Lib.ByteSequence.uints_from_bytes_le (as_seq h n))
      (fun b -> uints_from_bytes_le b n)


inline_for_extraction
val chacha20_init_: #w:lanes -> ctx:state w -> k:lbuffer uint8 32ul -> n:lbuffer uint8 12ul -> ctr0:size_t -> ST unit
		  (requires (fun h -> live h ctx /\ live h k /\ live h n /\ disjoint ctx k /\ disjoint ctx n /\ as_seq h ctx == Lib.Sequence.create 16 (vec_zero U32 w)))
		  (ensures (fun h0 _ h1 -> modifies (loc ctx) h0 h1 /\
			   as_seq h1 ctx == Spec.chacha20_init (as_seq h0 k) (as_seq h0 n) (v ctr0)))

#set-options "--z3rlimit 300"
[@ CInline]
let chacha20_init_ #w ctx k n ctr =
    push_frame();
    let ctx1 = create 16ul (u32 0) in
    setup1 ctx1 k n ctr;
    let h0 = ST.get() in
    mapT 16ul ctx (Spec.vec_load_i w) ctx1;
    let ctr = vec_counter U32 w in
    let c12 = ctx.(12ul) in
    ctx.(12ul) <- c12 +| ctr;
    pop_frame()

[@CInline]
let chacha20_init1 ctx k n ctr = chacha20_init_ #1 ctx k n ctr
[@CInline]
let chacha20_init4 ctx k n ctr = chacha20_init_ #4 ctx k n ctr
[@CInline]
let chacha20_init8 ctx k n ctr = chacha20_init_ #8 ctx k n ctr

inline_for_extraction
val chacha20_init: #w:lanes -> ctx:state w -> k:lbuffer uint8 32ul -> n:lbuffer uint8 12ul -> ctr0:size_t -> ST unit
		  (requires (fun h -> live h ctx /\ live h k /\ live h n /\ disjoint ctx k /\ disjoint ctx n /\ as_seq h ctx == Lib.Sequence.create 16 (vec_zero U32 w)))
		  (ensures (fun h0 _ h1 -> modifies (loc ctx) h0 h1 /\
			   as_seq h1 ctx == Spec.chacha20_init (as_seq h0 k) (as_seq h0 n) (v ctr0)))
let chacha20_init #w ctx k n ctr =
  match w with
  | 1 -> chacha20_init1 ctx k n ctr 
  | 4 -> chacha20_init4 ctx k n ctr 
  | 8 -> chacha20_init8 ctx k n ctr 
  

inline_for_extraction
val chacha20_encrypt_block: #w:lanes -> 
			   ctx:state w -> 
			   out:lbuffer uint8 (size w *! 64ul) -> 
			   incr:size_t{w * v incr <= max_size_t} ->
			   text:lbuffer uint8 (size w *! 64ul) -> 
			   ST unit
		  (requires (fun h -> 
			    live h ctx /\ 
			    live h text /\ 
			    live h out /\ 
			    disjoint out ctx /\
			    disjoint text ctx))
		  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\
			      as_seq h1 out == Spec.chacha20_encrypt_block (as_seq h0 ctx) (v incr) (as_seq h0 text)))
[@ CInline ]
let chacha20_encrypt_block #w ctx out incr text =
    push_frame();
    let k = create 16ul (vec_zero U32 w) in
    chacha20_core k ctx incr;
    xor_block out k text;
    pop_frame()


inline_for_extraction
val chacha20_encrypt_last: #w:lanes ->
			   ctx:state w -> 
			   len:size_t{v len < w * 64} ->
			   out:lbuffer uint8 len -> 
			   incr:size_t{w * v incr <= max_size_t} ->
			   text:lbuffer uint8 len -> 
			   ST unit
		  (requires (fun h -> 
			    live h ctx /\ 
			    live h text /\ 
			    live h out /\ 
			    disjoint out ctx /\
			    disjoint text ctx))
		  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\
			      as_seq h1 out == Spec.chacha20_encrypt_last (as_seq h0 ctx) (v incr) (v len) (as_seq h0 text)))
[@ CInline ]
let chacha20_encrypt_last #w ctx len out incr text =
    push_frame();
    let plain = create (size w *! size 64) (u8 0) in
    update_sub plain 0ul len text;
    chacha20_encrypt_block ctx plain incr plain;
    copy out (sub plain 0ul len);
    pop_frame()



inline_for_extraction
val chacha20_update: #w:lanes -> ctx:state w -> len:size_t -> out:lbuffer uint8 len -> text:lbuffer uint8 len -> ST unit
		  (requires (fun h -> 
			    live h ctx /\ 
			    live h text /\ 
			    live h out /\ 
			    eq_or_disjoint text out /\
			    disjoint text ctx /\
			    disjoint out ctx /\
			    v len / (w * 64) <= max_size_t))
		  (ensures (fun h0 _ h1 -> modifies (loc ctx |+| loc out) h0 h1 /\
			      as_seq h1 out == Spec.chacha20_update (as_seq h0 ctx) (as_seq h0 text)))
[@ CInline ]
let chacha20_update #w ctx len out text =
  push_frame();
  let k = create_state w in
  let blocks = len /. (size w *. size 64) in
  let rem = len %. (size w *. size 64) in
  let h0 = ST.get() in
  map_blocks h0 len (size w *. 64ul) text out 
    (fun h -> Spec.chacha20_encrypt_block (as_seq h0 ctx))
    (fun h -> Spec.chacha20_encrypt_last (as_seq h0 ctx))
    (fun i -> chacha20_encrypt_block ctx (sub out (i *! (size w *. 64ul)) (size w *. 64ul)) i (sub text (i *! (size w *! 64ul)) (size w *! 64ul)))
    (fun i -> chacha20_encrypt_last ctx rem (sub out (i *! (size w *. 64ul)) rem) i (sub text (i *! (size w *. 64ul)) rem));
  pop_frame()

inline_for_extraction
val chacha20_encrypt: #w:lanes -> len:size_t -> out:lbuffer uint8 len -> text:lbuffer uint8 len -> key:lbuffer uint8 32ul -> n:lbuffer uint8 12ul -> ctr:size_t -> ST unit
		  (requires (fun h -> live h key /\ live h n /\ live h text /\ live h out /\ eq_or_disjoint text out))
		  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\
			      as_seq h1 out == Spec.chacha20_encrypt_bytes #w (as_seq h0 key) (as_seq h0 n) (v ctr) (as_seq h0 text)))
let chacha20_encrypt #w len out text key n ctr = 
    push_frame();
    let ctx = create_state w in
    chacha20_init #w ctx key n ctr;
    chacha20_update #w ctx len out text;
    pop_frame()



inline_for_extraction
val chacha20_decrypt: #w:lanes -> len:size_t -> out:lbuffer uint8 len -> cipher:lbuffer uint8 len -> key:lbuffer uint8 32ul -> n:lbuffer uint8 12ul -> ctr:size_t -> ST unit
		  (requires (fun h -> live h key /\ live h n /\ live h cipher /\ live h out /\ eq_or_disjoint cipher out))
		  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\
			      as_seq h1 out == Spec.chacha20_decrypt_bytes #w (as_seq h0 key) (as_seq h0 n) (v ctr) (as_seq h0 cipher)))
let chacha20_decrypt #w len out cipher key n ctr = 
    push_frame();
    let ctx = create_state w in
    chacha20_init ctx key n ctr;
    chacha20_update ctx len out cipher;
    pop_frame()


    
