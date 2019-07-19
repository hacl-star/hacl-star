module Hacl.Impl.Salsa20

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.Salsa20.Core32

module ST = FStar.HyperStack.ST
module Spec = Spec.Salsa20
module Loop = Lib.LoopCombinators


#set-options "--z3rlimit 100 --max_fuel 0"

val rounds: st:state ->
  Stack unit
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

val salsa20_core:
    k:state
  -> ctx0:state
  -> ctr:size_t ->
  Stack unit
  (requires fun h -> live h ctx0 /\ live h k /\ disjoint ctx0 k)
  (ensures  fun h0 _ h1 -> modifies (loc k) h0 h1 /\
    as_seq h1 k == Spec.salsa20_core (v ctr) (as_seq h0 ctx0))

[@ CInline ]
let salsa20_core k ctx ctr =
  copy_state k ctx;
  let ctr_u32 = size_to_uint32 ctr in
  k.(8ul) <- k.(8ul) +. ctr_u32;
  rounds k;
  sum_state k ctx;
  k.(8ul) <- k.(8ul) +. ctr_u32


#set-options "--z3rlimit 100 --max_fuel 2"

inline_for_extraction
val salsa20_init:
    ctx:state
  -> k:lbuffer uint8 32ul
  -> n:lbuffer uint8 8ul
  -> ctr0:size_t ->
  Stack unit
  (requires fun h ->
    live h ctx /\ live h k /\ live h n /\
    disjoint ctx k /\ disjoint ctx n /\
    as_seq h ctx == Lib.Sequence.create 16 (u32 0))
  (ensures  fun h0 _ h1 -> modifies (loc ctx) h0 h1 /\
    as_seq h1 ctx == Spec.salsa20_init (as_seq h0 k) (as_seq h0 n) (v ctr0))

let salsa20_init ctx k n ctr =
  let h0 = ST.get() in
  push_frame();
  let k32 = create 8ul (u32 0) in
  let n32 = create 2ul (u32 0) in
  let h0' = ST.get() in
  uints_from_bytes_le k32 k;
  uints_from_bytes_le n32 n;
  ctx.(0ul) <- Spec.constant0;
  let k0 = sub k32 0ul 4ul in
  let k1 = sub k32 4ul 4ul in
  update_sub #MUT ctx 1ul 4ul k0;
  ctx.(5ul) <- Spec.constant1;
  update_sub #MUT ctx 6ul 2ul n32;
  ctx.(8ul) <- secret ctr;
  ctx.(9ul) <- u32 0;
  ctx.(10ul) <- Spec.constant2;
  update_sub #MUT ctx 11ul 4ul k1;
  ctx.(15ul) <- Spec.constant3;
  let h1' = ST.get() in
  assert (modifies (loc ctx |+| loc k32 |+| loc n32) h0' h1');
  pop_frame();
  let h1 = ST.get() in
  assert (modifies (loc ctx) h0 h1)


inline_for_extraction
val salsa20_encrypt_block:
    ctx:state
  -> out:lbuffer uint8 64ul
  -> incr:size_t
  -> text:lbuffer uint8 64ul ->
  Stack unit
  (requires fun h ->
    live h ctx /\ live h text /\ live h out /\
    disjoint out ctx /\ disjoint text ctx)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == Spec.salsa20_encrypt_block (as_seq h0 ctx) (v incr) (as_seq h0 text))

let salsa20_encrypt_block ctx out incr text =
  push_frame();
  let k = create 16ul (u32 0) in
  salsa20_core k ctx incr;
  xor_block out k text;
  pop_frame()


inline_for_extraction
val salsa20_encrypt_last:
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
    as_seq h1 out == Spec.salsa20_encrypt_last (as_seq h0 ctx) (v incr) (v len) (as_seq h0 text))

let salsa20_encrypt_last ctx len out incr text =
  push_frame();
  let plain = create (size 64) (u8 0) in
  update_sub plain 0ul len text;
  salsa20_encrypt_block ctx plain incr plain;
  copy out (sub plain 0ul len);
  pop_frame()


inline_for_extraction
val salsa20_update:
    ctx:state
  -> len:size_t
  -> out:lbuffer uint8 len
  -> text:lbuffer uint8 len ->
  Stack unit
  (requires fun h ->
    live h ctx /\ live h text /\ live h out /\
    eq_or_disjoint text out /\ disjoint text ctx /\ disjoint out ctx)
  (ensures  fun h0 _ h1 -> modifies (loc ctx |+| loc out) h0 h1 /\
    as_seq h1 out == Spec.salsa20_update (as_seq h0 ctx) (as_seq h0 text))

let salsa20_update ctx len out text =
  push_frame();
  let k = create_state () in
  let blocks = len /. size 64 in
  let rem = len %. size 64 in
  let h0 = ST.get() in
  map_blocks h0 len 64ul text out
    (fun h -> Spec.salsa20_encrypt_block (as_seq h0 ctx))
    (fun h -> Spec.salsa20_encrypt_last (as_seq h0 ctx))
    (fun i -> salsa20_encrypt_block ctx (sub out (i *! 64ul) 64ul) i (sub text (i *! 64ul) 64ul))
    (fun i -> salsa20_encrypt_last ctx rem (sub out (i *! 64ul) rem) i (sub text (i *! 64ul) rem));
  pop_frame()


val salsa20_key_block0:
    out:lbuffer uint8 64ul
  -> key:lbuffer uint8 32ul
  -> n:lbuffer uint8 8ul ->
  Stack unit
  (requires fun h -> live h key /\ live h n /\ live h out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == Spec.salsa20_key_block0 (as_seq h0 key) (as_seq h0 n))

[@CInline]
let salsa20_key_block0 out key n =
  push_frame();
  let ctx = create_state () in
  let k = create_state() in
  salsa20_init ctx key n 0ul;
  salsa20_core k ctx 0ul;
  store_state out k;
  pop_frame()


val salsa20_encrypt:
    len:size_t
  -> out:lbuffer uint8 len
  -> text:lbuffer uint8 len
  -> key:lbuffer uint8 32ul
  -> n:lbuffer uint8 8ul
  -> ctr:size_t ->
  Stack unit
  (requires fun h ->
    live h key /\ live h n /\ live h text /\ live h out /\ eq_or_disjoint text out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == Spec.salsa20_encrypt_bytes (as_seq h0 key) (as_seq h0 n) (v ctr) (as_seq h0 text))

[@CInline]
let salsa20_encrypt len out text key n ctr =
  push_frame();
  let ctx = create_state () in
  salsa20_init ctx key n ctr;
  salsa20_update ctx len out text;
  pop_frame()


val salsa20_decrypt:
    len:size_t
  -> out:lbuffer uint8 len
  -> cipher:lbuffer uint8 len
  -> key:lbuffer uint8 32ul
  -> n:lbuffer uint8 8ul
  -> ctr:size_t ->
  Stack unit
  (requires fun h ->
    live h key /\ live h n /\ live h cipher /\ live h out /\ eq_or_disjoint cipher out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == Spec.salsa20_decrypt_bytes (as_seq h0 key) (as_seq h0 n) (v ctr) (as_seq h0 cipher))

[@CInline]
let salsa20_decrypt len out cipher key n ctr =
  push_frame();
  let ctx = create_state () in
  salsa20_init ctx key n ctr;
  salsa20_update ctx len out cipher;
  pop_frame()
