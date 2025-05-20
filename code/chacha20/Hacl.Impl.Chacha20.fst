module Hacl.Impl.Chacha20

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.Chacha20.Core32

module ST = FStar.HyperStack.ST
module Spec = Spec.Chacha20
module Loop = Lib.LoopCombinators

#set-options "--z3rlimit 200 --max_fuel 2"
//#set-options "--debug Hacl.Impl.Curve25519.Generic --debug_level ExtractNorm"


val rounds:
    st:state
  -> Stack unit
  (requires fun h -> live h st)
  (ensures  fun h0 _ h1 -> modifies (loc st) h0 h1 /\
    as_seq h1 st == Spec.rounds (as_seq h0 st))

[@ CInline]
let rounds st =
  let h0 = ST.get () in
  Loop.eq_repeat0 #Spec.state Spec.double_round (as_seq h0 st);
  Loop.unfold_repeat 10 Spec.double_round (as_seq h0 st) 0;
  Loop.unfold_repeat 10 Spec.double_round (as_seq h0 st) 1;
  Loop.unfold_repeat 10 Spec.double_round (as_seq h0 st) 2;
  Loop.unfold_repeat 10 Spec.double_round (as_seq h0 st) 3;
  Loop.unfold_repeat 10 Spec.double_round (as_seq h0 st) 4;
  Loop.unfold_repeat 10 Spec.double_round (as_seq h0 st) 5;
  Loop.unfold_repeat 10 Spec.double_round (as_seq h0 st) 6;
  Loop.unfold_repeat 10 Spec.double_round (as_seq h0 st) 7;
  Loop.unfold_repeat 10 Spec.double_round (as_seq h0 st) 8;
  Loop.unfold_repeat 10 Spec.double_round (as_seq h0 st) 9;
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


val chacha20_core:
    k:state
  -> ctx0:state
  -> ctr:size_t ->
  Stack unit
  (requires fun h -> live h ctx0 /\ live h k /\ disjoint ctx0 k)
  (ensures  fun h0 _ h1 -> modifies (loc k) h0 h1 /\
    as_seq h1 k == Spec.chacha20_core (v ctr) (as_seq h0 ctx0))

[@ CInline ]
let chacha20_core k ctx ctr =
  copy_state k ctx;
  let ctr_u32 = size_to_uint32 ctr in
  k.(12ul) <- k.(12ul) +. ctr_u32;
  rounds k;
  sum_state k ctx;
  k.(12ul) <- k.(12ul) +. ctr_u32


inline_for_extraction noextract
val chacha20_constants:
  b:glbuffer size_t 4ul{recallable b /\ witnessed b Spec.Chacha20.chacha20_constants}
let chacha20_constants = Hacl.Impl.Chacha20.Vec.chacha20_constants


val chacha20_init:
    ctx:state
  -> k:lbuffer uint8 32ul
  -> n:lbuffer uint8 12ul
  -> ctr0:size_t ->
  Stack unit
  (requires fun h ->
    live h ctx /\ live h k /\ live h n /\
    disjoint ctx k /\ disjoint ctx n /\
    as_seq h ctx == Lib.Sequence.create 16 (u32 0))
  (ensures  fun h0 _ h1 -> modifies (loc ctx) h0 h1 /\
    as_seq h1 ctx == Spec.chacha20_init (as_seq h0 k) (as_seq h0 n) (v ctr0))

let chacha20_init ctx k n ctr =
  let h0 = ST.get() in
  recall_contents chacha20_constants Spec.chacha20_constants;
  update_sub_f h0 ctx 0ul 4ul
    (fun h -> Lib.Sequence.map secret Spec.chacha20_constants)
    (fun _ -> mapT 4ul (sub ctx 0ul 4ul) secret chacha20_constants);
  let h1 = ST.get() in
  update_sub_f h1 ctx 4ul 8ul
    (fun h -> Lib.ByteSequence.uints_from_bytes_le (as_seq h k))
    (fun _ -> uints_from_bytes_le (sub ctx 4ul 8ul) k);
  let h2 = ST.get() in
  ctx.(12ul) <- size_to_uint32 ctr;
  let h3 = ST.get() in
  update_sub_f h3 ctx 13ul 3ul
    (fun h -> Lib.ByteSequence.uints_from_bytes_le (as_seq h n))
    (fun _ -> uints_from_bytes_le (sub ctx 13ul 3ul) n);
  let h4 = ST.get() in
  assert (as_seq h4 ctx == Spec.setup (as_seq h0 k) (as_seq h0 n) (v ctr) (as_seq h0 ctx));
  ()


val chacha20_encrypt_block:
    ctx:state
  -> out:lbuffer uint8 64ul
  -> incr:size_t
  -> text:lbuffer uint8 64ul ->
  Stack unit
  (requires fun h ->
    live h ctx /\ live h text /\ live h out /\
    disjoint out ctx /\ disjoint text ctx)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == Spec.chacha20_encrypt_block (as_seq h0 ctx) (v incr) (as_seq h0 text))

let chacha20_encrypt_block ctx out incr text =
  push_frame();
  let k = create 16ul (u32 0) in
  chacha20_core k ctx incr;
  xor_block out k text;
  pop_frame()


val chacha20_encrypt_last:
    ctx:state
  -> len:size_t{v len < 64}
  -> out:lbuffer uint8 len
  -> incr:size_t
  -> text:lbuffer uint8 len ->
  Stack unit
  (requires fun h ->
    live h ctx /\ live h text /\ live h out /\
    disjoint out ctx /\ disjoint text ctx)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == Spec.chacha20_encrypt_last (as_seq h0 ctx) (v incr) (v len) (as_seq h0 text))

[@CInline]
let chacha20_encrypt_last ctx len out incr text =
  push_frame();
  let plain = create (size 64) (u8 0) in
  update_sub plain 0ul len text;
  (* HACL-RS *)
  let plain_copy = create (size 64) (u8 0) in
  copy plain_copy plain;
  chacha20_encrypt_block ctx plain incr plain_copy;
  copy out (sub plain 0ul len);
  pop_frame()


val chacha20_update:
    ctx:state
  -> len:size_t
  -> out:lbuffer uint8 len
  -> text:lbuffer uint8 len ->
  Stack unit
  (requires fun h ->
    live h ctx /\ live h text /\ live h out /\
    eq_or_disjoint text out /\ disjoint text ctx /\ disjoint out ctx)
  (ensures  fun h0 _ h1 -> modifies (loc ctx |+| loc out) h0 h1 /\
    as_seq h1 out == Spec.chacha20_update (as_seq h0 ctx) (as_seq h0 text))

let chacha20_update ctx len out text =
  push_frame();
  let blocks = len /. size 64 in
  let rem = len %. size 64 in
  let h0 = ST.get() in
  map_blocks h0 len 64ul text out
    (fun h -> Spec.chacha20_encrypt_block (as_seq h0 ctx))
    (fun h -> Spec.chacha20_encrypt_last (as_seq h0 ctx))
    (fun i -> chacha20_encrypt_block ctx (sub out (i *! 64ul) 64ul) i (sub text (i *! 64ul) 64ul))
    (fun i -> chacha20_encrypt_last ctx rem (sub out (i *! 64ul) rem) i (sub text (i *! 64ul) rem));
  pop_frame()


inline_for_extraction
val chacha20_encrypt:
    len:size_t
  -> out:lbuffer uint8 len
  -> text:lbuffer uint8 len
  -> key:lbuffer uint8 32ul
  -> n:lbuffer uint8 12ul
  -> ctr:size_t ->
  Stack unit
  (requires fun h ->
    live h key /\ live h n /\ live h text /\ live h out /\ eq_or_disjoint text out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == Spec.chacha20_encrypt_bytes (as_seq h0 key) (as_seq h0 n) (v ctr) (as_seq h0 text))

let chacha20_encrypt len out text key n ctr =
  push_frame();
  let ctx = create_state () in
  chacha20_init ctx key n ctr;
  chacha20_update ctx len out text;
  pop_frame()


inline_for_extraction
val chacha20_decrypt:
    len:size_t
  -> out:lbuffer uint8 len
  -> cipher:lbuffer uint8 len
  -> key:lbuffer uint8 32ul
  -> n:lbuffer uint8 12ul
  -> ctr:size_t ->
  Stack unit
  (requires fun h ->
    live h key /\ live h n /\ live h cipher /\ live h out /\ eq_or_disjoint cipher out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == Spec.chacha20_decrypt_bytes (as_seq h0 key) (as_seq h0 n) (v ctr) (as_seq h0 cipher))

let chacha20_decrypt len out cipher key n ctr =
  push_frame();
  let ctx = create_state () in
  chacha20_init ctx key n ctr;
  chacha20_update ctx len out cipher;
  pop_frame()
