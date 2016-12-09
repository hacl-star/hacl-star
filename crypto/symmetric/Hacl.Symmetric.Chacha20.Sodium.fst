module Hacl.Symmetric.Chacha20.Sodium

open FStar.HyperStack
open FStar.ST
open FStar.Buffer
open Hacl.UInt32
open Hacl.Cast

let h32 = Hacl.UInt32.t
let u32 = FStar.UInt32.t
let uint8_p = buffer Hacl.UInt8.t

type chacha_ctx = b:Buffer.buffer h32{length b = 16}

assume MaxUInt32: pow2 32 = 4294967296

let op_Less_Less_Less (a:h32) (s:u32{FStar.UInt32.v s <= 32}) : Tot h32 =
  (a <<^ s) |^ (a >>^ (FStar.UInt32 (32ul -^ s)))


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 5"

let load32_le (k:uint8_p) : Stack h32
  (requires (fun h -> live h k /\ length k >= 4))
  (ensures  (fun h0 _ h1 -> h0 == h1))
  = let k0 = k.(0ul) in
    let k1 = k.(1ul) in
    let k2 = k.(2ul) in
    let k3 = k.(3ul) in
    let z = sint8_to_sint32 k0
            |^ (sint8_to_sint32 k1 <<^ 8ul)
            |^ (sint8_to_sint32 k2 <<^ 16ul)
            |^ (sint8_to_sint32 k3 <<^ 24ul) in
    z

let store32_le (k:uint8_p) (x:h32) : Stack unit
  (requires (fun h -> live h k /\ length k >= 4))
  (ensures  (fun h0 _ h1 -> modifies_1 k h0 h1 /\ live h1 k))
  = k.(0ul) <- sint32_to_sint8 x;
    k.(1ul) <- sint32_to_sint8 (x >>^ 8ul);
    k.(2ul) <- sint32_to_sint8 (x >>^ 16ul);
    k.(3ul) <- sint32_to_sint8 (x >>^ 24ul)


val quarter_round:
  m:chacha_ctx ->
  a:u32{FStar.UInt32.v a < 16} ->
  b:u32{FStar.UInt32.v b<16} ->
  c:u32{FStar.UInt32.v c<16} ->
  d:u32{FStar.UInt32.v d<16} ->
  Stack unit
    (requires (fun h -> live h m))
    (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1))
let quarter_round m a b c d =
  let ma = m.(a) in let mb = m.(b) in m.(a) <- (ma +%^ mb);
  let md = m.(d) in let ma = m.(a) in m.(d) <- (md ^^ ma);
  let md = m.(d) in                   m.(d) <- (md <<< 16ul);
  let mc = m.(c) in let md = m.(d) in m.(c) <- (mc +%^ md);
  let mb = m.(b) in let mc = m.(c) in m.(b) <- (mb ^^ mc);
  let mb = m.(b) in                   m.(b) <- (mb <<< 12ul);
  let ma = m.(a) in let mb = m.(b) in m.(a) <- (ma +%^ mb);
  let md = m.(d) in let ma = m.(a) in m.(d) <- (md ^^ ma);
  let md = m.(d) in                   m.(d) <- (md <<< 8ul);
  let mc = m.(c) in let md = m.(d) in m.(c) <- (mc +%^ md);
  let mb = m.(b) in let mc = m.(c) in m.(b) <- (mb ^^ mc);
  let mb = m.(b) in                   m.(b) <- (mb <<< 7ul)


val chacha_keysetup:
  ctx:chacha_ctx ->
  k:uint8_p ->
  Stack unit
    (requires (fun _ -> True))
    (ensures  (fun _ _ _ -> True))
let chacha_keysetup ctx k =
    ctx.(0ul)  <- uint32_to_sint32 (0x61707865ul);
    ctx.(1ul)  <- uint32_to_sint32 (0x3320646eul);
    ctx.(2ul)  <- uint32_to_sint32 (0x79622d32ul);
    ctx.(3ul)  <- uint32_to_sint32 (0x6b206574ul);
    ctx.(4ul)  <- load32_le(offset k  0ul);
    ctx.(5ul)  <- load32_le(offset k  4ul);
    ctx.(6ul)  <- load32_le(offset k  8ul);
    ctx.(7ul)  <- load32_le(offset k 12ul);
    ctx.(8ul)  <- load32_le(offset k 16ul);
    ctx.(9ul)  <- load32_le(offset k 20ul);
    ctx.(10ul) <- load32_le(offset k 24ul);
    ctx.(11ul) <- load32_le(offset k 28ul)


val chacha_ivsetup:
  ctx:chacha_ctx ->
  k:uint8_p ->
  counter:uint8_p ->
  Stack unit
    (requires (fun _ -> True))
    (ensures  (fun _ _ _ -> True))
let chacha_ivsetup ctx iv counter =
    ctx.(12ul) <- load32_le(counter);
    ctx.(13ul) <- load32_le(offset counter 4ul);
    ctx.(14ul) <- load32_le(iv);
    ctx.(15ul) <- load32_le(offset iv 4ul)


val chacha_ietf_ivsetup:
  ctx:chacha_ctx ->
  k:uint8_p ->
  counter:h32 ->
  Stack unit
    (requires (fun _ -> True))
    (ensures  (fun _ _ _ -> True))
let chacha_ietf_ivsetup ctx iv counter =
    ctx.(12ul) <- counter;
    ctx.(13ul) <- load32_le(iv);
    ctx.(14ul) <- load32_le(offset iv 4ul);
    ctx.(15ul) <- load32_le(offset iv 8ul)


val chacha_encrypt_bytes_core:
  ctx:chacha_ctx ->
  m:uint8_p ->
  c:uint8_p ->
  Stack unit
    (requires (fun _ -> True))
    (ensures  (fun _ _ _ -> True))
let chacha_encrypt_bytes_core ctx m c =
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

  (* let x = Buffer.sub ctx 16ul 16ul in *)
  (* let ctx = Buffer.sub ctx 0ul 16ul in *)
  (* blit ctx 0ul x 0ul 16ul; *)

  (* quarter_round x 0ul 4ul 8ul 12ul; *)
  (* quarter_round x 1ul 5ul 9ul 13ul; *)
  (* quarter_round x 2ul 6ul 10ul 14ul; *)
  (* quarter_round x 3ul 7ul 11ul 15ul; *)
  (* quarter_round x 0ul 5ul 10ul 15ul; *)
  (* quarter_round x 1ul 6ul 11ul 12ul; *)
  (* quarter_round x 2ul 7ul 8ul 13ul; *)
  (* quarter_round x 3ul 4ul 9ul 14ul;   *)

  (* quarter_round x 0ul 4ul 8ul 12ul; *)
  (* quarter_round x 1ul 5ul 9ul 13ul; *)
  (* quarter_round x 2ul 6ul 10ul 14ul; *)
  (* quarter_round x 3ul 7ul 11ul 15ul; *)
  (* quarter_round x 0ul 5ul 10ul 15ul; *)
  (* quarter_round x 1ul 6ul 11ul 12ul; *)
  (* quarter_round x 2ul 7ul 8ul 13ul; *)
  (* quarter_round x 3ul 4ul 9ul 14ul;   *)

  (* quarter_round x 0ul 4ul 8ul 12ul; *)
  (* quarter_round x 1ul 5ul 9ul 13ul; *)
  (* quarter_round x 2ul 6ul 10ul 14ul; *)
  (* quarter_round x 3ul 7ul 11ul 15ul; *)
  (* quarter_round x 0ul 5ul 10ul 15ul; *)
  (* quarter_round x 1ul 6ul 11ul 12ul; *)
  (* quarter_round x 2ul 7ul 8ul 13ul; *)
  (* quarter_round x 3ul 4ul 9ul 14ul;   *)

  (* quarter_round x 0ul 4ul 8ul 12ul; *)
  (* quarter_round x 1ul 5ul 9ul 13ul; *)
  (* quarter_round x 2ul 6ul 10ul 14ul; *)
  (* quarter_round x 3ul 7ul 11ul 15ul; *)
  (* quarter_round x 0ul 5ul 10ul 15ul; *)
  (* quarter_round x 1ul 6ul 11ul 12ul; *)
  (* quarter_round x 2ul 7ul 8ul 13ul; *)
  (* quarter_round x 3ul 4ul 9ul 14ul;   *)

  (* quarter_round x 0ul 4ul 8ul 12ul; *)
  (* quarter_round x 1ul 5ul 9ul 13ul; *)
  (* quarter_round x 2ul 6ul 10ul 14ul; *)
  (* quarter_round x 3ul 7ul 11ul 15ul; *)
  (* quarter_round x 0ul 5ul 10ul 15ul; *)
  (* quarter_round x 1ul 6ul 11ul 12ul; *)
  (* quarter_round x 2ul 7ul 8ul 13ul; *)
  (* quarter_round x 3ul 4ul 9ul 14ul;   *)

  (* quarter_round x 0ul 4ul 8ul 12ul; *)
  (* quarter_round x 1ul 5ul 9ul 13ul; *)
  (* quarter_round x 2ul 6ul 10ul 14ul; *)
  (* quarter_round x 3ul 7ul 11ul 15ul; *)
  (* quarter_round x 0ul 5ul 10ul 15ul; *)
  (* quarter_round x 1ul 6ul 11ul 12ul; *)
  (* quarter_round x 2ul 7ul 8ul 13ul; *)
  (* quarter_round x 3ul 4ul 9ul 14ul;   *)

  (* quarter_round x 0ul 4ul 8ul 12ul; *)
  (* quarter_round x 1ul 5ul 9ul 13ul; *)
  (* quarter_round x 2ul 6ul 10ul 14ul; *)
  (* quarter_round x 3ul 7ul 11ul 15ul; *)
  (* quarter_round x 0ul 5ul 10ul 15ul; *)
  (* quarter_round x 1ul 6ul 11ul 12ul; *)
  (* quarter_round x 2ul 7ul 8ul 13ul; *)
  (* quarter_round x 3ul 4ul 9ul 14ul;   *)

  (* quarter_round x 0ul 4ul 8ul 12ul; *)
  (* quarter_round x 1ul 5ul 9ul 13ul; *)
  (* quarter_round x 2ul 6ul 10ul 14ul; *)
  (* quarter_round x 3ul 7ul 11ul 15ul; *)
  (* quarter_round x 0ul 5ul 10ul 15ul; *)
  (* quarter_round x 1ul 6ul 11ul 12ul; *)
  (* quarter_round x 2ul 7ul 8ul 13ul; *)
  (* quarter_round x 3ul 4ul 9ul 14ul;   *)

  (* quarter_round x 0ul 4ul 8ul 12ul; *)
  (* quarter_round x 1ul 5ul 9ul 13ul; *)
  (* quarter_round x 2ul 6ul 10ul 14ul; *)
  (* quarter_round x 3ul 7ul 11ul 15ul; *)
  (* quarter_round x 0ul 5ul 10ul 15ul; *)
  (* quarter_round x 1ul 6ul 11ul 12ul; *)
  (* quarter_round x 2ul 7ul 8ul 13ul; *)
  (* quarter_round x 3ul 4ul 9ul 14ul;   *)

  (* quarter_round x 0ul 4ul 8ul 12ul; *)
  (* quarter_round x 1ul 5ul 9ul 13ul; *)
  (* quarter_round x 2ul 6ul 10ul 14ul; *)
  (* quarter_round x 3ul 7ul 11ul 15ul; *)
  (* quarter_round x 0ul 5ul 10ul 15ul; *)
  (* quarter_round x 1ul 6ul 11ul 12ul; *)
  (* quarter_round x 2ul 7ul 8ul 13ul; *)
  (* quarter_round x 3ul 4ul 9ul 14ul;   *)

  let x0 = j0 in
  let x1 = j1 in
  let x2 = j2 in
  let x3 = j3 in
  let x4 = j4 in
  let x5 = j5 in
  let x6 = j6 in
  let x7 = j7 in
  let x8 = j8 in
  let x9 = j9 in
  let x10 = j10 in
  let x11 = j11 in
  let x12 = j12 in
  let x13 = j13 in
  let x14 = j14 in
  let x15 = j15 in

  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 16ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 12ul in
  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 8ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 7ul in

  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 16ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 12ul in
  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 8ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 7ul in

  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 16ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 12ul in
  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 8ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 7ul in

  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 16ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 12ul in
  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 8ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 7ul in

  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 16ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 12ul in
  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 8ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 7ul in

  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 16ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 12ul in
  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 8ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 7ul in

  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 16ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 12ul in
  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 8ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 7ul in

  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 16ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 12ul in
  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 8ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 7ul in

  (* 1 *)

  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 16ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 12ul in
  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 8ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 7ul in

  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 16ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 12ul in
  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 8ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 7ul in

  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 16ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 12ul in
  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 8ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 7ul in

  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 16ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 12ul in
  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 8ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 7ul in

  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 16ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 12ul in
  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 8ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 7ul in

  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 16ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 12ul in
  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 8ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 7ul in

  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 16ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 12ul in
  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 8ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 7ul in

  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 16ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 12ul in
  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 8ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 7ul in

  (* 2 *)

  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 16ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 12ul in
  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 8ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 7ul in

  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 16ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 12ul in
  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 8ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 7ul in

  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 16ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 12ul in
  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 8ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 7ul in

  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 16ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 12ul in
  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 8ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 7ul in

  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 16ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 12ul in
  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 8ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 7ul in

  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 16ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 12ul in
  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 8ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 7ul in

  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 16ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 12ul in
  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 8ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 7ul in

  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 16ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 12ul in
  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 8ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 7ul in

  (* 3 *)

  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 16ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 12ul in
  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 8ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 7ul in

  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 16ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 12ul in
  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 8ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 7ul in

  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 16ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 12ul in
  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 8ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 7ul in

  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 16ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 12ul in
  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 8ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 7ul in

  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 16ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 12ul in
  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 8ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 7ul in

  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 16ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 12ul in
  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 8ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 7ul in

  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 16ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 12ul in
  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 8ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 7ul in

  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 16ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 12ul in
  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 8ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 7ul in

  (* 4 *)

  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 16ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 12ul in
  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 8ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 7ul in

  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 16ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 12ul in
  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 8ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 7ul in

  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 16ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 12ul in
  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 8ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 7ul in

  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 16ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 12ul in
  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 8ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 7ul in

  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 16ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 12ul in
  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 8ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 7ul in

  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 16ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 12ul in
  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 8ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 7ul in

  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 16ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 12ul in
  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 8ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 7ul in

  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 16ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 12ul in
  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 8ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 7ul in

  (* 5 *)

  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 16ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 12ul in
  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 8ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 7ul in

  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 16ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 12ul in
  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 8ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 7ul in

  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 16ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 12ul in
  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 8ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 7ul in

  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 16ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 12ul in
  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 8ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 7ul in

  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 16ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 12ul in
  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 8ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 7ul in

  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 16ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 12ul in
  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 8ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 7ul in

  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 16ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 12ul in
  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 8ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 7ul in

  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 16ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 12ul in
  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 8ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 7ul in

  (* 6 *)

  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 16ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 12ul in
  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 8ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 7ul in

  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 16ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 12ul in
  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 8ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 7ul in

  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 16ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 12ul in
  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 8ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 7ul in

  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 16ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 12ul in
  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 8ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 7ul in

  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 16ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 12ul in
  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 8ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 7ul in

  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 16ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 12ul in
  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 8ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 7ul in

  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 16ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 12ul in
  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 8ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 7ul in

  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 16ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 12ul in
  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 8ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 7ul in

  (* 7 *)

  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 16ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 12ul in
  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 8ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 7ul in

  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 16ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 12ul in
  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 8ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 7ul in

  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 16ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 12ul in
  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 8ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 7ul in

  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 16ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 12ul in
  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 8ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 7ul in

  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 16ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 12ul in
  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 8ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 7ul in

  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 16ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 12ul in
  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 8ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 7ul in

  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 16ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 12ul in
  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 8ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 7ul in

  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 16ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 12ul in
  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 8ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 7ul in

  (* 8 *)

  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 16ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 12ul in
  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 8ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 7ul in

  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 16ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 12ul in
  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 8ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 7ul in

  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 16ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 12ul in
  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 8ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 7ul in

  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 16ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 12ul in
  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 8ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 7ul in

  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 16ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 12ul in
  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 8ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 7ul in

  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 16ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 12ul in
  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 8ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 7ul in

  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 16ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 12ul in
  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 8ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 7ul in

  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 16ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 12ul in
  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 8ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 7ul in

  (* 9 *)

  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 16ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 12ul in
  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 8ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 7ul in

  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 16ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 12ul in
  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 8ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 7ul in

  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 16ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 12ul in
  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 8ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 7ul in

  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 16ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 12ul in
  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 8ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 7ul in

  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 16ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 12ul in
  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 8ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 7ul in

  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 16ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 12ul in
  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 8ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 7ul in

  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 16ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 12ul in
  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 8ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 7ul in

  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 16ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 12ul in
  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 8ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 7ul in
 
  (* (\* 10 *\) *)
  (* let x0 = x.(0ul) in *)
  (* let x1 = x.(1ul) in *)
  (* let x2 = x.(2ul) in *)
  (* let x3 = x.(3ul) in *)
  (* let x4 = x.(4ul) in *)
  (* let x5 = x.(5ul) in *)
  (* let x6 = x.(6ul) in *)
  (* let x7 = x.(7ul) in *)
  (* let x8 = x.(8ul) in *)
  (* let x9 = x.(9ul) in *)
  (* let x10 = x.(10ul) in *)
  (* let x11 = x.(11ul) in *)
  (* let x12 = x.(12ul) in *)
  (* let x13 = x.(13ul) in *)
  (* let x14 = x.(14ul) in *)
  (* let x15 = x.(15ul) in *)

  let x0 = x0 +^ j0 in
  let x1 = x1 +^ j1 in
  let x2 = x2 +^ j2 in
  let x3 = x3 +^ j3 in
  let x4 = x4 +^ j4 in
  let x5 = x5 +^ j5 in
  let x6 = x6 +^ j6 in
  let x7 = x7 +^ j7 in
  let x8 = x8 +^ j8 in
  let x9 = x9 +^ j9 in
  let x10 = x10 +^ j10 in
  let x11 = x11 +^ j11 in
  let x12 = x12 +^ j12 in
  let x13 = x13 +^ j13 in
  let x14 = x14 +^ j14 in
  let x15 = x15 +^ j15 in

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


val chacha_encrypt_bytes_loop:
  ctx:chacha_ctx ->
  m:uint8_p ->
  c:uint8_p ->
  len:UInt32.t ->
  Stack unit
    (requires (fun _ -> True))
    (ensures  (fun _ _ _ -> True))
let rec chacha_encrypt_bytes_loop ctx m c len =
  if FStar.UInt32 (len <^ 64ul) then ()
  else (
    chacha_encrypt_bytes_core ctx m c;
    let ctr = ctx.(12ul) in
    ctx.(12ul) <- Hacl.UInt32 (ctr +^ uint32_to_sint32 1ul);
    chacha_encrypt_bytes_loop ctx (offset m 64ul) (offset c 64ul) (FStar.UInt32 (len -^ 64ul))
  )

module U32 = FStar.UInt32

val chacha_encrypt_bytes:
  ctx:chacha_ctx ->
  m:uint8_p ->
  c:uint8_p ->
  len:UInt32.t ->
  Stack unit
    (requires (fun _ -> True))
    (ensures  (fun _ _ _ -> True))
let rec chacha_encrypt_bytes ctx m c len =
  push_frame();
  chacha_encrypt_bytes_loop ctx m c len;
  let rem = U32 (len &^ 63ul) in // % 64
  let q   = U32 (len >>^ 6ul) in // / 64
  if FStar.UInt32 (rem >=^ 0ul) then (
    let tmp = create (uint8_to_sint8 0uy) 64ul in
    let m = offset m (U32 (len -^ rem)) in
    let c = offset c (U32 (len -^ rem)) in
    blit m 0ul tmp 0ul rem;
    chacha_encrypt_bytes_core ctx tmp tmp;
    blit tmp 0ul c 0ul rem );
  pop_frame()
