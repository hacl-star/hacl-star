module Hacl.Impl.Chacha20_vec

open FStar.Mul
open FStar.HyperStack
open FStar.ST
open FStar.Buffer
open Hacl.Cast
open Hacl.Spec.Endianness
open Hacl.Endianness
open Spec.Chacha20
open Combinators

module Spec = Spec.Chacha20
module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32 = Hacl.UInt32
open Hacl.UInt32x4

let u32 = U32.t
let h32 = H32.t
let uint8_p = buffer H8.t
type state = b:Buffer.buffer uint32x4{length b = 4}

#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 100"

[@ "substitute"]
val constant_setup_:
  c:state ->
  Stack unit
    (requires (fun h -> live h c))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_1 c h0 h1))
[@ "substitute"]
let constant_setup_ st =
  st.(0ul)  <- vec_load_32x4 (uint32_to_sint32 0x61707865ul) 
  	       		     (uint32_to_sint32 0x3320646eul)
			     (uint32_to_sint32 0x79622d32ul)
			     (uint32_to_sint32 0x6b206574ul)


[@ "substitute"]
val constant_setup:
  c:state ->
  Stack unit
    (requires (fun h -> live h c))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_1 c h0 h1))
[@ "substitute"]
let constant_setup st =
  constant_setup_ st

[@ "substitute"]
val keysetup:
  st:state ->
  k:uint8_p{length k = 32 /\ disjoint st k} ->
  Stack unit
    (requires (fun h -> live h st /\ live h k))
    (ensures  (fun h0 _ h1 -> live h0 st /\ live h0 k /\ live h1 st /\ modifies_1 st h0 h1))
[@ "substitute"]
let keysetup st k =
  let k0 = vec_load_le (Buffer.sub k 0ul 16ul) in
  let k1 = vec_load_le (Buffer.sub k 16ul 16ul) in
  st.(1ul) <- k0;
  st.(2ul) <- k1


[@ "substitute"]
val ctr_ivsetup:
  st:state ->
  ctr:U32.t ->
  iv:uint8_p{length iv = 12 /\ disjoint st iv} ->
  StackInline unit
    (requires (fun h -> live h st /\ live h iv))
    (ensures  (fun h0 _ h1 -> live h1 st /\ modifies_1 st h0 h1 /\ live h0 iv))
[@ "substitute"]
let ctr_ivsetup st ctr iv =
  let n0 = load32_le (Buffer.sub iv 0ul 4ul) in
  let n1 = load32_le (Buffer.sub iv 4ul 4ul) in
  let n2 = load32_le (Buffer.sub iv 8ul 4ul) in
  let v = vec_load_32x4 ctr n0 n1 n2 in
  st.(3ul) <- v

[@ "c_inline"]
val setup:
  st:state ->
  k:uint8_p{length k = 32 /\ disjoint st k} ->
  n:uint8_p{length n = 12 /\ disjoint st n} ->
  c:U32.t ->
  Stack unit
    (requires (fun h -> live h st /\ live h k /\ live h n))
    (ensures (fun h0 _ h1 -> live h0 k /\ live h0 n /\ live h1 st /\ modifies_1 st h0 h1))
[@ "c_inline"]
let setup st k n c =
  constant_setup st;
  keysetup st k;
  ctr_ivsetup st c n


let idx = a:U32.t{U32.v a < 4}

[@ "substitute"]
val line:
  st:state ->
  a:idx -> b:idx -> d:idx -> s:U32.t{U32.v s < 32} ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h1 st /\ modifies_1 st h0 h1 /\ live h0 st))
[@ "substitute"]
let line st a b d s =
  let sa = st.(a) in 
  let sb = st.(b) in
  let sd = st.(d) in 
  let sa = sa +%^ sb in
  let sd = (sd ^^ sa) <<< s in
  st.(a) <- sa;
  st.(d) <- sd


[@ "c_inline"]
val round:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1))
[@ "c_inline"]
let round st =
  line st 0ul 1ul 3ul 16ul;
  line st 2ul 3ul 1ul 12ul;
  line st 0ul 1ul 3ul 8ul ;
  line st 2ul 3ul 1ul 7ul


[@ "substitute"]
val column_round:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1))
[@ "substitute"]
let column_round st = round st

val shuffle_rows_0123:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1))
let shuffle_rows_0123 st = 
    let r1 = st.(1ul) in
    let r2 = st.(2ul) in
    let r3 = st.(3ul) in
    st.(1ul) <-  vec_shuffle_right r1 1ul;
    st.(2ul) <-  vec_shuffle_right r2 2ul;
    st.(3ul) <-  vec_shuffle_right r3 3ul

val shuffle_rows_0321:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1))
let shuffle_rows_0321 st = 
    let r1 = st.(1ul) in
    let r2 = st.(2ul) in
    let r3 = st.(3ul) in
    st.(1ul) <-  vec_shuffle_right r1 3ul;
    st.(2ul) <-  vec_shuffle_right r2 2ul;
    st.(3ul) <-  vec_shuffle_right r3 1ul
    
[@ "substitute"]
val diagonal_round:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1))
[@ "substitute"]
let diagonal_round st =
  shuffle_rows_0123 st;
  round st;
  shuffle_rows_0321 st


[@ "c_inline"]
val double_round:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1))
[@ "c_inline"]
let double_round st =
    column_round st;
    diagonal_round st

#reset-options "--initial_fuel 0 --max_fuel 1 --z3rlimit 100"

[@ "c_inline"]
val rounds:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1))
[@ "c_inline"]
let rounds st = Loops_vec.rounds st
// Real implementation bellow
  (* Combinators.iter #H32.t #16 #(double_round') 10ul double_round st 16ul *)


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"


[@ "c_inline"]
val sum_states:
  st:state ->
  st':state{disjoint st st'} ->
  Stack unit
    (requires (fun h -> live h st /\ live h st'))
    (ensures  (fun h0 _ h1 -> live h0 st /\ live h1 st /\ live h0 st' /\ modifies_1 st h0 h1))
[@ "c_inline"]
let sum_states st st' = Loops_vec.sum_states st st'
  // Real implementation bellow
  (* Combinators.inplace_map2 (fun x y -> Hacl.UInt32x4.(x +%^ y)) st st' 16ul *)


[@ "c_inline"]
val copy_state:
  st':state ->
  st:state{disjoint st st'} ->
  Stack unit
    (requires (fun h -> live h st /\ live h st'))
    (ensures (fun h0 _ h1 -> live h1 st /\ live h0 st' /\ modifies_1 st' h0 h1))
[@ "c_inline"]
let copy_state st' st =
  st'.(0ul) <- st.(0ul);
  st'.(1ul) <- st.(1ul);
  st'.(2ul) <- st.(2ul);
  st'.(3ul) <- st.(3ul)


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"


type log_t_ = | MkLog: k:Spec.key -> n:Spec.nonce -> (* c:Spec.counter -> *) log_t_
type log_t = Ghost.erased log_t_



[@ "c_inline"]
val chacha20_core:
  k:state ->
  st:state ->
  Stack unit
    (requires (fun h -> live h k /\ live h st))
    (ensures  (fun h0 updated_log h1 -> live h1 k /\ live h1 st /\ modifies_1 k h0 h1))
[@ "c_inline"]
let chacha20_core k st =
  copy_state k st;
  rounds k;
  sum_states k st

[@ "c_inline"]
val chacha20_block:
  stream_block:uint8_p{length stream_block = 64} ->
  st:state{disjoint st stream_block} ->
  Stack unit
    (requires (fun h -> live h stream_block))
    (ensures  (fun h0 updated_log h1 -> live h1 stream_block /\ modifies_1 stream_block h0 h1))
[@ "c_inline"]
let chacha20_block stream_block st =
  push_frame();
  let k = Buffer.create zero 4ul in
  chacha20_core k st;
  vec_store_le (Buffer.sub stream_block 0ul 16ul) k.(0ul);
  vec_store_le (Buffer.sub stream_block 16ul 16ul) k.(1ul);
  vec_store_le (Buffer.sub stream_block 32ul 16ul) k.(2ul);
  vec_store_le (Buffer.sub stream_block 48ul 16ul) k.(3ul);
  pop_frame()

[@ "c_inline"]
val alloc:
  unit ->
  StackInline state
    (requires (fun h -> True))
    (ensures (fun h0 st h1 -> ~(contains h0 st) /\ live h1 st /\ modifies_0 h0 h1 /\ frameOf st == h1.tip
      /\ Map.domain h1.h == Map.domain h0.h))
[@ "c_inline"]
let alloc () =
  create zero 4ul


[@ "c_inline"]
val init:
  st:state ->
  k:uint8_p{length k = 32 /\ disjoint st k} ->
  n:uint8_p{length n = 12 /\ disjoint st n} ->
  Stack unit
    (requires (fun h -> live h k /\ live h n /\ live h st))
    (ensures  (fun h0 log h1 -> live h1 st /\ live h0 k /\ live h0 n /\ modifies_1 st h0 h1))
[@ "c_inline"]
let init st k n = 
  setup st k n 0ul


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val lemma_chacha20_counter_mode_1:
  ho:mem -> output:uint8_p{live ho output} ->
  hi:mem -> input:uint8_p{live hi input} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length input /\ U32.v len <= 64 /\ U32.v len > 0} ->
  (* h:mem -> st:state{live h st} -> *)
  k:Spec.key -> n:Spec.nonce -> ctr:U32.t{U32.v ctr + (length input / 64) < pow2 32} -> Lemma
    (Spec.CTR.counter_mode chacha20_ctx chacha20_cipher k n (U32.v ctr) (reveal_sbytes (as_seq hi input))
     == Combinators.seq_map2 (fun x y -> FStar.UInt8.(x ^^ y))
                             (reveal_sbytes (as_seq hi input))
                             (Seq.slice (Spec.chacha20_block k n (U32.v ctr)) 0 (U32.v len)))
#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 100"
let lemma_chacha20_counter_mode_1 ho output hi input len k n ctr = ()

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val lemma_chacha20_counter_mode_2:
  ho:mem -> output:uint8_p{live ho output} ->
  hi:mem -> input:uint8_p{live hi input} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length input /\ U32.v len > 64} ->
  k:Spec.key -> n:Spec.nonce -> ctr:U32.t{U32.v ctr + (length input / 64) < pow2 32} -> Lemma
    (Spec.CTR.counter_mode chacha20_ctx chacha20_cipher k n (U32.v ctr) (reveal_sbytes (as_seq hi input))
     == (let b, plain = Seq.split (reveal_sbytes (as_seq hi input)) 64 in
         let mask = Spec.chacha20_block k n (U32.v ctr) in
         let eb = Combinators.seq_map2 (fun x y -> FStar.UInt8.(x ^^ y)) b mask in
         let cipher = Spec.CTR.counter_mode chacha20_ctx chacha20_cipher k n (U32.v ctr + 1) plain in
         Seq.append eb cipher))
#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 100"
let lemma_chacha20_counter_mode_2 ho output hi input len k n ctr = ()


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val lemma_chacha20_counter_mode_0:
  ho:mem -> output:uint8_p{live ho output} ->
  hi:mem -> input:uint8_p{live hi input} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length input /\ U32.v len = 0} ->
  k:Spec.key -> n:Spec.nonce -> ctr:U32.t{U32.v ctr + (length input / 64) < pow2 32} -> Lemma
    (Spec.CTR.counter_mode chacha20_ctx chacha20_cipher k n (U32.v ctr) (reveal_sbytes (as_seq hi input))
     == reveal_sbytes (as_seq ho output))
#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 100"
let lemma_chacha20_counter_mode_0 ho output hi input len k n ctr =
  Seq.lemma_eq_intro (as_seq ho output) Seq.createEmpty


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val update_last:
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length plain /\ U32.v len <= 64 /\ U32.v len > 0} ->
  st:state{disjoint st output /\ disjoint st plain} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain))
    (ensures (fun h0 updated_log h1 -> live h1 output /\ live h0 plain /\ modifies_2 output st h0 h1))
let update_last output plain len st =
  push_frame();
  let block = create (uint8_to_sint8 0uy) 64ul in
  chacha20_block block st;
  let mask = Buffer.sub block 0ul len in
  Loops_vec.xor_bytes output plain mask len;
  pop_frame()

val xor_block:
  output:uint8_p{length output = 64} ->
  plain:uint8_p{disjoint output plain /\ length plain = 64} ->
  st:state{disjoint st output /\ disjoint st plain} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h0 plain /\ modifies_1 output h0 h1))
let xor_block output plain st = 
  let p0 = vec_load_le (Buffer.sub plain 0ul 16ul) in
  let p1 = vec_load_le (Buffer.sub plain 16ul 16ul) in
  let p2 = vec_load_le (Buffer.sub plain 32ul 16ul) in
  let p3 = vec_load_le (Buffer.sub plain 48ul 16ul) in
  let k0 = st.(0ul) in
  let k1 = st.(1ul) in
  let k2 = st.(2ul) in
  let k3 = st.(3ul) in
  let o0 = vec_xor p0 k0 in
  let o1 = vec_xor p1 k1 in
  let o2 = vec_xor p2 k2 in
  let o3 = vec_xor p3 k3 in
  vec_store_le (Buffer.sub output 0ul 16ul) o0;
  vec_store_le (Buffer.sub output 16ul 16ul) o1;
  vec_store_le (Buffer.sub output 32ul 16ul) o2;
  vec_store_le (Buffer.sub output 48ul 16ul) o3

val update:
  output:uint8_p{length output = 64} ->
  plain:uint8_p{disjoint output plain /\ length plain = 64} ->
  st:state{disjoint st output /\ disjoint st plain} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain))
    (ensures (fun h0 updated_log h1 -> live h1 output /\ live h0 plain /\ modifies_2 output st h0 h1))
let update output plain st =
  let h0 = ST.get() in
  push_frame();
  let k = Buffer.create zero 4ul in
  chacha20_core k st;
  xor_block output plain k;
  st.(3ul) <- vec_add st.(3ul) one_le;
  pop_frame()


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 300"

val chacha20_counter_mode_:
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length plain /\ U32.v len <= 64} ->
  st:state{disjoint st output /\ disjoint st plain} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h0 plain /\ live h1 st
      /\ modifies_2 output st h0 h1))
let rec chacha20_counter_mode_ output plain len st =
  let h0 = ST.get() in
  if U32.(len =^ 0ul) then (
     ()
  ) else  (
     update_last output plain len st 
  )

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val chacha20_counter_mode:
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length plain} ->
  st:state{disjoint st output /\ disjoint st plain} ->
  ctr:U32.t{U32.v ctr + (length plain / 64) < pow2 32} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h0 plain /\ live h1 st
      /\ modifies_2 output st h0 h1))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 500"
let rec chacha20_counter_mode output plain len st ctr =
  let h0 = ST.get() in
  if U32.(len <=^ 64ul) then chacha20_counter_mode_ output plain len st
  else (
    let b  = Buffer.sub plain 0ul 64ul in
    let b' = Buffer.offset plain 64ul in
    let o  = Buffer.sub output 0ul 64ul in
    let o' = Buffer.offset output 64ul in
    update o b st;
    let h = ST.get() in
    let l = chacha20_counter_mode o' b' U32.(len -^ 64ul) st U32.(ctr +^ 1ul) in
    let h' = ST.get() in
    ())


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val chacha20:
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length plain} ->
  key:uint8_p{length key = 32} ->
  nonce:uint8_p{length nonce = 12} ->
  ctr:U32.t{U32.v ctr + (length plain / 64) < pow2 32} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain /\ live h key /\ live h nonce))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h0 plain /\ live h0 key /\ live h0 nonce
      /\ modifies_1 output h0 h1))
let chacha20 output plain len k n ctr =
  push_frame();
  let st = alloc () in
  setup st k n ctr;
  chacha20_counter_mode output plain len st ctr;
  pop_frame()(* ; *)
