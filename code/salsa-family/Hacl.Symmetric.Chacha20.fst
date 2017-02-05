module Hacl.Symmetric.Chacha20


open FStar.HyperStack
open FStar.ST
open FStar.Buffer
open Hacl.Cast
open Hacl.UInt32
open Hacl.Spec.Symmetric.Chacha20

module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32 = Hacl.UInt32

let u32 = U32.t
let h32 = H32.t
let uint8_p = buffer H8.t

type chacha_ctx = b:Buffer.buffer h32{length b = 16}

private inline_for_extraction let op_Less_Less_Less (a:h32) (s:u32{U32.v s <= 32}) : Tot h32 =
  (a <<^ s) |^ (a >>^ (FStar.UInt32.(32ul -^ s)))


#reset-options "--initial_ifuel 0 --max_ifuel 0 --initial_fuel 0 --max_fuel 0 --z3rlimit 50"

[@"c_inline"]
#set-options "--lax"
private inline_for_extraction let load32_le (k:uint8_p) : Stack h32
  (requires (fun h -> live h k /\ length k = 4))
  (ensures  (fun h0 r h1 -> h0 == h1 /\ live h0 k /\ length k = 4
    /\ r == load32_le_spec (as_seq h0 k)))
  = C.load32_le k

[@"c_inline"]
private inline_for_extraction let store32_le (k:uint8_p) (x:h32) : Stack unit
  (requires (fun h -> live h k /\ length k = 4))
  (ensures  (fun h0 _ h1 -> modifies_1 k h0 h1 /\ live h1 k /\ length k = 4 /\ live h0 k
    /\ as_seq h1 k == store32_le_spec (as_seq h0 k) x))
  = C.store32_le k x


#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 100"

[@"c_inline"]
val chacha_keysetup:
  ctx:chacha_ctx ->
  k:uint8_p{length k = 32 /\ disjoint ctx k} ->
  Stack unit
    (requires (fun h -> live h ctx /\ live h k))
    (ensures  (fun h0 _ h1 -> live h0 ctx /\ live h0 k /\ live h1 ctx /\ modifies_1 ctx h0 h1
      (* /\ as_seq h1 ctx == chacha_keysetup_spec (as_seq h0 ctx) (as_seq h0 k) *)
    ))
[@"c_inline"]
let chacha_keysetup ctx k =
    ctx.(0ul)  <- (uint32_to_sint32 0x61707865ul);
    ctx.(1ul)  <- (uint32_to_sint32 0x3320646eul);
    ctx.(2ul)  <- (uint32_to_sint32 0x79622d32ul);
    ctx.(3ul)  <- (uint32_to_sint32 0x6b206574ul);
    ctx.(4ul)  <- load32_le(Buffer.sub k  0ul 4ul);
    ctx.(5ul)  <- load32_le(Buffer.sub k  4ul 4ul);
    ctx.(6ul)  <- load32_le(Buffer.sub k  8ul 4ul);
    ctx.(7ul)  <- load32_le(Buffer.sub k 12ul 4ul);
    ctx.(8ul)  <- load32_le(Buffer.sub k 16ul 4ul);
    ctx.(9ul)  <- load32_le(Buffer.sub k 20ul 4ul);
    ctx.(10ul) <- load32_le(Buffer.sub k 24ul 4ul);
    ctx.(11ul) <- load32_le(Buffer.sub k 28ul 4ul)


[@"c_inline"]
val chacha_ietf_ivsetup:
  ctx:chacha_ctx ->
  k:uint8_p{length k = 12 /\ disjoint ctx k} ->
  counter:u32 ->
  Stack unit
    (requires (fun h -> live h ctx /\ live h k))
    (ensures  (fun h0 _ h1 -> live h1 ctx /\ modifies_1 ctx h0 h1 /\ live h0 ctx /\ live h0 k
      (* /\ as_seq h1 ctx == chacha_ietf_ivsetup_spec (as_seq h0 ctx) (as_seq h0 k) counter *)
    ))
[@"c_inline"]
let chacha_ietf_ivsetup ctx iv counter =
    ctx.(12ul) <- uint32_to_sint32 counter;
    ctx.(13ul) <- load32_le(Buffer.sub iv 0ul 4ul);
    ctx.(14ul) <- load32_le(Buffer.sub iv 4ul 4ul);
    ctx.(15ul) <- load32_le(Buffer.sub iv 8ul 4ul)



[@"c_inline"]
private inline_for_extraction val chacha_encrypt_bytes_quarter_round:
  ctx:chacha_ctx ->
  a:u32 -> b:u32 -> c:u32 -> d:u32 ->
  Stack unit
    (requires (fun h -> U32.v a < 16 /\ U32.v b < 16 /\ U32.v c < 16 /\ U32.v d < 16 /\ live h ctx))
    (ensures  (fun h0 _ h1 -> modifies_1 ctx h0 h1 /\ live h1 ctx /\ live h0 ctx))
[@"c_inline"]
private inline_for_extraction let chacha_encrypt_bytes_quarter_round ctx a b c d =
  let xa = ctx.(a) in
  let xb = ctx.(b) in
  let xc = ctx.(c) in
  let xd = ctx.(d) in
  let xa = xa +%^ xb in
  let xd = xd ^^ xa in
  let xd = xd <<< 16ul in
  let xc = xc +%^ xd in
  let xb = xb ^^ xc in
  let xb = xb <<< 12ul in
  let xa = xa +%^ xb in
  let xd = xd ^^ xa in
  let xd = xd <<< 8ul in
  let xc = xc +%^ xd in
  let xb = xb ^^ xc in
  let xb = xb <<< 7ul in
  ctx.(a) <- xa;
  ctx.(b) <- xb;
  ctx.(c) <- xc;
  ctx.(d) <- xd


[@"c_inline"]
private val chacha_encrypt_bytes_round:
  ctx:chacha_ctx ->
  Stack unit
    (requires (fun h -> live h ctx))
    (ensures  (fun h0 _ h1 -> modifies_1 ctx h0 h1 /\ live h1 ctx /\ live h0 ctx 
      (* /\ as_seq h1 ctx == chacha_encrypt_bytes_round_spec (as_seq h0 ctx) *)
      ))
[@"c_inline"]
private let chacha_encrypt_bytes_round ctx =
  chacha_encrypt_bytes_quarter_round ctx 0ul 4ul 8ul 12ul;
  chacha_encrypt_bytes_quarter_round ctx 1ul 5ul 9ul 13ul;
  chacha_encrypt_bytes_quarter_round ctx 2ul 6ul 10ul 14ul;
  chacha_encrypt_bytes_quarter_round ctx 3ul 7ul 11ul 15ul;
  chacha_encrypt_bytes_quarter_round ctx 0ul 5ul 10ul 15ul;
  chacha_encrypt_bytes_quarter_round ctx 1ul 6ul 11ul 12ul;
  chacha_encrypt_bytes_quarter_round ctx 2ul 7ul 8ul 13ul;
  chacha_encrypt_bytes_quarter_round ctx 3ul 4ul 9ul 14ul


[@"c_inline"]
private val chacha_encrypt_bytes_rounds:
  ctx:chacha_ctx ->
  Stack unit
    (requires (fun h -> live h ctx))
    (ensures  (fun h0 _ h1 -> modifies_1 ctx h0 h1 /\ live h1 ctx /\ live h0 ctx
      (* /\ as_seq h1 ctx == chacha_encrypt_bytes_rounds_spec (as_seq h0 ctx) *)
    ))
[@"c_inline"]
private let chacha_encrypt_bytes_rounds ctx =
  chacha_encrypt_bytes_round ctx;
  chacha_encrypt_bytes_round ctx;
  chacha_encrypt_bytes_round ctx;
  chacha_encrypt_bytes_round ctx;
  chacha_encrypt_bytes_round ctx;
  chacha_encrypt_bytes_round ctx;
  chacha_encrypt_bytes_round ctx;
  chacha_encrypt_bytes_round ctx;
  chacha_encrypt_bytes_round ctx;
  chacha_encrypt_bytes_round ctx


[@"substitute"]
private val chacha_encrypt_bytes_store:
  c:uint8_p{length c = 64} ->
  x0:h32 -> x1:h32 -> x2:h32 -> x3:h32 -> x4:h32 -> x5:h32 -> x6:h32 -> x7:h32 -> 
  x8:h32 -> x9:h32 -> x10:h32 -> x11:h32 -> x12:h32 -> x13:h32 -> x14:h32 -> x15:h32 ->
  Stack unit
    (requires (fun h -> live h c))
    (ensures (fun h0 _ h1 -> live h1 c /\ modifies_1 c h0 h1 /\ live h0 c
      (* /\ as_seq h1 c == chacha_encrypt_bytes_store_spec (as_seq h0 c) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 *)
    ))
[@"substitute"]
private let chacha_encrypt_bytes_store c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 =
  let open FStar.Buffer in
  store32_le (sub c 0ul 4ul) x0;
  store32_le (sub c 4ul 4ul) x1;
  store32_le (sub c 8ul 4ul) x2;
  store32_le (sub c 12ul 4ul) x3;
  store32_le (sub c 16ul 4ul) x4;
  store32_le (sub c 20ul 4ul) x5;
  store32_le (sub c 24ul 4ul) x6;
  store32_le (sub c 28ul 4ul) x7;
  store32_le (sub c 32ul 4ul) x8;
  store32_le (sub c 36ul 4ul) x9;
  store32_le (sub c 40ul 4ul) x10;
  store32_le (sub c 44ul 4ul) x11;
  store32_le (sub c 48ul 4ul) x12;
  store32_le (sub c 52ul 4ul) x13;
  store32_le (sub c 56ul 4ul) x14;
  store32_le (sub c 60ul 4ul) x15  


[@"c_inline"]
val chacha_encrypt_bytes_stream:
  ctx:chacha_ctx ->
  c:uint8_p{length c >= 64 /\ disjoint ctx c} ->
  Stack unit
    (requires (fun h -> live h ctx /\ live h c))
    (ensures  (fun h0 _ h1 -> modifies_1 c h0 h1 /\ live h1 c))
[@"c_inline"]
let chacha_encrypt_bytes_stream ctx c =
  push_frame();
  let tmp = create (uint32_to_sint32 0ul) 16ul in
  blit ctx 0ul tmp 0ul 16ul;
  chacha_encrypt_bytes_rounds tmp;
  let j0 = ctx.(0ul) in
  let j1 = ctx.(1ul) in
  let j2 = ctx.(2ul) in
  let j3 = ctx.(3ul) in
  let j4 = ctx.(4ul) in
  let j5 = ctx.(5ul) in
  let j6 = ctx.(6ul) in
  let j7 = ctx.(7ul) in
  let j8 = ctx.(8ul) in
  let j9 = ctx.(9ul) in
  let j10 = ctx.(10ul) in
  let j11 = ctx.(11ul) in
  let j12 = ctx.(12ul) in
  let j13 = ctx.(13ul) in
  let j14 = ctx.(14ul) in
  let j15 = ctx.(15ul) in
  let x0 = tmp.(0ul) in
  let x1 = tmp.(1ul) in
  let x2 = tmp.(2ul) in
  let x3 = tmp.(3ul) in
  let x4 = tmp.(4ul) in
  let x5 = tmp.(5ul) in
  let x6 = tmp.(6ul) in
  let x7 = tmp.(7ul) in
  let x8 = tmp.(8ul) in
  let x9 = tmp.(9ul) in
  let x10 = tmp.(10ul) in
  let x11 = tmp.(11ul) in
  let x12 = tmp.(12ul) in
  let x13 = tmp.(13ul) in
  let x14 = tmp.(14ul) in
  let x15 = tmp.(15ul) in
  let x0 = x0 +%^ j0 in
  let x1 = x1 +%^ j1 in
  let x2 = x2 +%^ j2 in
  let x3 = x3 +%^ j3 in
  let x4 = x4 +%^ j4 in
  let x5 = x5 +%^ j5 in
  let x6 = x6 +%^ j6 in
  let x7 = x7 +%^ j7 in
  let x8 = x8 +%^ j8 in
  let x9 = x9 +%^ j9 in
  let x10 = x10 +%^ j10 in
  let x11 = x11 +%^ j11 in
  let x12 = x12 +%^ j12 in
  let x13 = x13 +%^ j13 in
  let x14 = x14 +%^ j14 in
  let x15 = x15 +%^ j15 in
  chacha_encrypt_bytes_store (Buffer.sub c 0ul 64ul) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15;
  pop_frame()


[@"c_inline"]
private val chacha_encrypt_bytes_core:
  ctx:chacha_ctx ->
  m:uint8_p{length m >= 64} ->
  c:uint8_p{length c >= 64 /\ disjoint ctx c} ->
  Stack unit
    (requires (fun h -> live h ctx /\ live h c /\ live h m))
    (ensures  (fun h0 _ h1 -> modifies_1 c h0 h1 /\ live h1 c))
[@"c_inline"]
private let chacha_encrypt_bytes_core ctx m c =
  push_frame();
  let tmp = create (uint32_to_sint32 0ul) 16ul in
  blit ctx 0ul tmp 0ul 16ul;
  chacha_encrypt_bytes_rounds tmp;
  let j0 = ctx.(0ul) in
  let j1 = ctx.(1ul) in
  let j2 = ctx.(2ul) in
  let j3 = ctx.(3ul) in
  let j4 = ctx.(4ul) in
  let j5 = ctx.(5ul) in
  let j6 = ctx.(6ul) in
  let j7 = ctx.(7ul) in
  let j8 = ctx.(8ul) in
  let j9 = ctx.(9ul) in
  let j10 = ctx.(10ul) in
  let j11 = ctx.(11ul) in
  let j12 = ctx.(12ul) in
  let j13 = ctx.(13ul) in
  let j14 = ctx.(14ul) in
  let j15 = ctx.(15ul) in
  let x0 = tmp.(0ul) in
  let x1 = tmp.(1ul) in
  let x2 = tmp.(2ul) in
  let x3 = tmp.(3ul) in
  let x4 = tmp.(4ul) in
  let x5 = tmp.(5ul) in
  let x6 = tmp.(6ul) in
  let x7 = tmp.(7ul) in
  let x8 = tmp.(8ul) in
  let x9 = tmp.(9ul) in
  let x10 = tmp.(10ul) in
  let x11 = tmp.(11ul) in
  let x12 = tmp.(12ul) in
  let x13 = tmp.(13ul) in
  let x14 = tmp.(14ul) in
  let x15 = tmp.(15ul) in
  let x0 = x0 +%^ j0 in
  let x1 = x1 +%^ j1 in
  let x2 = x2 +%^ j2 in
  let x3 = x3 +%^ j3 in
  let x4 = x4 +%^ j4 in
  let x5 = x5 +%^ j5 in
  let x6 = x6 +%^ j6 in
  let x7 = x7 +%^ j7 in
  let x8 = x8 +%^ j8 in
  let x9 = x9 +%^ j9 in
  let x10 = x10 +%^ j10 in
  let x11 = x11 +%^ j11 in
  let x12 = x12 +%^ j12 in
  let x13 = x13 +%^ j13 in
  let x14 = x14 +%^ j14 in
  let x15 = x15 +%^ j15 in
  let open FStar.Buffer in
  let m0 = load32_le (sub m 0ul 4ul) in
  let m1 = load32_le (sub m 4ul 4ul) in
  let m2 = load32_le (sub m 8ul 4ul) in
  let m3 = load32_le (sub m 12ul 4ul) in
  let m4 = load32_le (sub m 16ul 4ul) in
  let m5 = load32_le (sub m 20ul 4ul) in
  let m6 = load32_le (sub m 24ul 4ul) in
  let m7 = load32_le (sub m 28ul 4ul) in
  let m8 = load32_le (sub m 32ul 4ul) in
  let m9 = load32_le (sub m 36ul 4ul) in
  let m10 = load32_le (sub m 40ul 4ul) in
  let m11 = load32_le (sub m 44ul 4ul) in
  let m12 = load32_le (sub m 48ul 4ul) in
  let m13 = load32_le (sub m 52ul 4ul) in
  let m14 = load32_le (sub m 56ul 4ul) in
  let m15 = load32_le (sub m 60ul 4ul) in
  let x0 = x0 ^^ m0 in
  let x1 = x1 ^^ m1 in
  let x2 = x2 ^^ m2 in
  let x3 = x3 ^^ m3 in
  let x4 = x4 ^^ m4 in
  let x5 = x5 ^^ m5 in
  let x6 = x6 ^^ m6 in
  let x7 = x7 ^^ m7 in
  let x8 = x8 ^^ m8 in
  let x9 = x9 ^^ m9 in
  let x10 = x10 ^^ m10 in
  let x11 = x11 ^^ m11 in
  let x12 = x12 ^^ m12 in
  let x13 = x13 ^^ m13 in
  let x14 = x14 ^^ m14 in
  let x15 = x15 ^^ m15 in
  chacha_encrypt_bytes_store (Buffer.sub c 0ul 64ul)  x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15;
  pop_frame()


[@"c_inline"]
private val chacha_encrypt_bytes_loop:
  ctx:chacha_ctx ->
  m:uint8_p ->
  c:uint8_p{disjoint ctx c} ->
  len:U32.t{U32.v len <= length m /\ U32.v len <= length c} ->
  Stack unit
    (requires (fun h -> live h c /\ live h m /\ live h ctx))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_2 ctx c h0 h1))
[@"c_inline"]
private let rec chacha_encrypt_bytes_loop ctx m c len =
  if FStar.UInt32.(len <^ 64ul) then ()
  else (
    chacha_encrypt_bytes_core ctx m c;
    let ctr = ctx.(12ul) in
    let one = uint32_to_sint32 1ul in
    ctx.(12ul) <- H32.(ctr +%^ one);
    chacha_encrypt_bytes_loop ctx (offset m 64ul) (offset c 64ul) (FStar.UInt32.(len -^ 64ul))
  )


[@"c_inline"]
private val chacha_encrypt_bytes_finish:
  ctx:chacha_ctx ->
  m:uint8_p ->
  c:uint8_p{disjoint ctx c} ->
  len:UInt32.t{U32.v len <= length m /\ U32.v len <= length c /\ U32.v len < 64} ->
  Stack unit
    (requires (fun h -> live h c /\ live h m /\ live h ctx))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_2 ctx c h0 h1))
[@"c_inline"]
private let chacha_encrypt_bytes_finish ctx m c len =
  let hinit = ST.get() in
  push_frame();
  let h0 = ST.get() in
  let zero = uint8_to_sint8 0uy in
  let tmp = create zero 64ul in
  let h0' = ST.get() in
  blit m 0ul tmp 0ul len;
  let h1 = ST.get() in
  chacha_encrypt_bytes_core ctx tmp tmp;
  let h2 = ST.get() in
  blit tmp 0ul c 0ul len;
  let h3 = ST.get() in
  lemma_modifies_2_1'' ctx c h0 h2 h3;
  pop_frame();
  let hfin = ST.get() in
  ()


[@"c_inline"]
val chacha_encrypt_bytes_finish_stream:
  ctx:chacha_ctx ->
  c:uint8_p{disjoint ctx c} ->
  len:UInt32.t{U32.v len <= length c /\ U32.v len < 64} ->
  Stack unit
    (requires (fun h -> live h c /\ live h ctx))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_1 c h0 h1))
let chacha_encrypt_bytes_finish_stream ctx c len =
  let hinit = ST.get() in
  push_frame();
  let zero = uint8_to_sint8 0uy in
  let tmp = create zero 64ul in
  chacha_encrypt_bytes_stream ctx tmp;
  blit tmp 0ul c 0ul len;
  pop_frame();
  ()

(** API a la LibSodium **)
val chacha_encrypt_bytes:
  ctx:chacha_ctx ->
  m:uint8_p ->
  c:uint8_p{disjoint ctx c} ->
  len:UInt32.t{U32.v len <= length m /\ U32.v len <= length c} ->
  Stack unit
    (requires (fun h -> live h c /\ live h m /\ live h ctx))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_2 ctx c h0 h1))
let rec chacha_encrypt_bytes ctx m c len =
  chacha_encrypt_bytes_loop ctx m c len;
  UInt.logand_mask (U32.v len) 6;
  assert_norm(pow2 6 = 64);
  Math.Lemmas.euclidean_division_definition (U32.v len) 64;
  let rema = U32.(len &^ 63ul) in // % 64
  let q   = U32.(len >>^ 6ul) in // / 64
  if FStar.UInt32.(rema >=^ 0ul) then (
    let m = offset m (U32.(len -^ rema)) in
    let c = offset c (U32.(len -^ rema)) in
    chacha_encrypt_bytes_finish ctx m c rema)


(* ************************************* *)
(*              CHACHA20 API             *)
(* ************************************* *)
val chacha20_init:
  key:uint8_p{length key = 32} ->
  nonce:uint8_p{length nonce = 12} ->
  ctr:UInt32.t ->
  StackInline chacha_ctx
    (requires (fun h -> live h key /\ live h nonce))
    (ensures  (fun h0 st h1 -> live h0 key /\ live h0 nonce /\ live h1 st /\ modifies_0 h0 h1
    ))
let chacha20_init k n ctr =
  let ctx = Buffer.create (Hacl.Cast.uint32_to_sint32 0ul) 16ul in
  chacha_keysetup ctx k;
  chacha_ietf_ivsetup ctx n ctr;
  ctx

[@"c_inline"]
val chacha20_update:
  ctx:chacha_ctx ->
  m:uint8_p{length m = 64} ->
  c:uint8_p{disjoint ctx c /\ length c = 64} ->
  Stack unit
    (requires (fun h -> live h c /\ live h m /\ live h ctx))
    (ensures  (fun h0 _ h1 -> live h1 c /\ live h1 ctx /\ modifies_2 ctx c h0 h1))
[@"c_inline"]
let chacha20_update ctx m c =
  chacha_encrypt_bytes_core ctx m c;
  let ctr = ctx.(12ul) in
  let one = uint32_to_sint32 1ul in
  ctx.(12ul) <- H32.(ctr +%^ one)


[@"c_inline"]
val chacha20_finish:
  ctx:chacha_ctx ->
  m:uint8_p ->
  c:uint8_p{disjoint ctx c} ->
  len:UInt32.t{U32.v len = length m /\ U32.v len = length c /\ U32.v len < 64} ->
  Stack unit
    (requires (fun h -> live h c /\ live h m /\ live h ctx))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_2 ctx c h0 h1))
[@"c_inline"]
let chacha20_finish ctx m c len =
  let hinit = ST.get() in
  push_frame();
  let h0 = ST.get() in
  let zero = uint8_to_sint8 0uy in
  let tmp = create zero 64ul in
  let h0' = ST.get() in
  blit m 0ul tmp 0ul len;
  let h1 = ST.get() in
  chacha_encrypt_bytes_core ctx tmp tmp;
  let h2 = ST.get() in
  blit tmp 0ul c 0ul len;
  let h3 = ST.get() in
  lemma_modifies_2_1'' ctx c h0 h2 h3;
  pop_frame();
  let hfin = ST.get() in
  ()
