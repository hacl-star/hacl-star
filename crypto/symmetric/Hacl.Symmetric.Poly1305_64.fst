module Hacl.Symmetric.Poly1305_64

open FStar.ST
open FStar.Buffer

open Hacl.Cast

open Hacl.Symmetric.Poly1305_64.Parameters
open Hacl.Symmetric.Poly1305_64.Bigint


module H64 = Hacl.UInt64
module H128 = Hacl.UInt128
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module U128 = FStar.UInt64

type poly1305_state = {
  r:buffer h64;
  h:buffer h64;
  }

(* type poly1305_state = b:buffer h64{length b = 6} *)

(* type triple = {t1:h64; t2:h64; t3:h64} *)

val load64_le:
  b:uint8_p{length b >= 8} ->
  Stack h64
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> h0 == h1))
let load64_le b =
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b4 = b.(4ul) in
  let b5 = b.(5ul) in
  let b6 = b.(6ul) in
  let b7 = b.(7ul) in
  H64 (
    sint8_to_sint64 b0
    |^ (sint8_to_sint64 b1 <<^ 8ul)
    |^ (sint8_to_sint64 b2 <<^ 16ul)
    |^ (sint8_to_sint64 b3 <<^ 24ul)
    |^ (sint8_to_sint64 b4 <<^ 32ul)
    |^ (sint8_to_sint64 b5 <<^ 40ul)
    |^ (sint8_to_sint64 b6 <<^ 48ul)
    |^ (sint8_to_sint64 b7 <<^ 56ul)
  )


val store64_le:
  b:uint8_p{length b >= 8} ->
  z:H64.t ->
  Stack unit
    (requires (fun _ -> True))
    (ensures  (fun _ _ _ -> True))
let store64_le b z =
  let open Hacl.UInt64 in
  b.(0ul) <- sint64_to_sint8 z;
  b.(1ul) <- sint64_to_sint8 (z >>^ 8ul);
  b.(2ul) <- sint64_to_sint8 (z >>^ 16ul);
  b.(3ul) <- sint64_to_sint8 (z >>^ 24ul);
  b.(4ul) <- sint64_to_sint8 (z >>^ 32ul);
  b.(5ul) <- sint64_to_sint8 (z >>^ 40ul);
  b.(6ul) <- sint64_to_sint8 (z >>^ 48ul);
  b.(7ul) <- sint64_to_sint8 (z >>^ 56ul)


val poly1305_init:
  st:poly1305_state ->
  key:uint8_p{length key = 32} ->
  Stack unit
    (requires (fun _ -> True))
    (ensures  (fun _ _ _ -> True))
let poly1305_init st key =
  let t0 = load64_le(key) in
  let t1 = load64_le(offset key 8ul) in

  let open Hacl.UInt64 in
  st.r.(0ul) <- ( t0                           ) &^ uint64_to_sint64 0xffc0fffffffuL;
  st.r.(1ul) <- ((t0 >>^ 44ul) |^ (t1 <<^ 20ul)) &^ uint64_to_sint64 0xfffffc0ffffuL;
  st.r.(2ul) <- ((t1 >>^ 24ul)                 ) &^ uint64_to_sint64 0x00ffffffc0fuL;

  let zero = uint64_to_sint64 0uL in
  st.h.(0ul) <- zero;
  st.h.(1ul) <- zero;
  st.h.(2ul) <- zero


val poly1305_blocks_loop:
  st:poly1305_state ->
  m:uint8_p ->
  len:U64.t ->
  r0:h64 ->
  r1:h64 ->
  r2:h64 ->
  s1:h64 ->
  s2:h64 ->
  h0:h64 ->
  h1:h64 ->
  h2:h64 ->
  Stack unit
    (requires (fun h -> True))
    (ensures  (fun _ _ _ -> True))
let rec poly1305_blocks_loop st m len r0 r1 r2 s1 s2 h0 h1 h2 =
  (* if U64 (len <^ 16uL) then (h0, h1, h2) *)
  if U64 (len <^ 16uL) then (
    st.h.(0ul) <- h0;
    st.h.(1ul) <- h1;
    st.h.(2ul) <- h2
  )
  else (
    let t0 = load64_le m in
    let t1 = load64_le (offset m 8ul) in

    let mask_2_44 = uint64_to_sint64 0xfffffffffffuL in
    let mask_2_42 = uint64_to_sint64 0x3ffffffffffuL in

    let open Hacl.UInt64 in

    let h0 = h0 +^ (t0 &^ mask_2_44) in
    let h1 = h1 +^ (((t0 >>^ 44ul) |^ (t1 <<^ 20ul)) &^ mask_2_44) in
    let h2 = h2 +^ (((t1 >>^ 24ul) &^ mask_2_42) |^ (uint64_to_sint64 1uL <<^ 40ul)) in

    let open Hacl.UInt128 in

    let d0 = h0 *^ r0 in
    let d  = h1 *^ s2 in
    let d0 = d0 +^ d  in
    let d  = h2 *^ s1 in
    let d0 = d0 +^ d  in

    let d1 = h0 *^ r1 in
    let d  = h1 *^ r0 in
    let d1 = d1 +^ d  in
    let d  = h2 *^ s2 in
    let d1 = d1 +^ d  in

    let d2 = h0 *^ r2 in
    let d  = h1 *^ r1 in
    let d2 = d2 +^ d  in
    let d  = h2 *^ r0 in
    let d2 = d2 +^ d  in

    let c  = sint128_to_sint64 (d0 >>^ 44ul) in
    let h0 = H64 (sint128_to_sint64 d0 &^ mask_2_44) in
    let d1 = d1 +^ sint64_to_sint128 c in

    let c  = sint128_to_sint64 (d1 >>^ 44ul) in
    let h1 = H64 (sint128_to_sint64 d1 &^ mask_2_44) in
    let d2 = d2 +^ sint64_to_sint128 c in

    let c  = sint128_to_sint64 (d2 >>^ 42ul) in
    let h2 = H64 (sint128_to_sint64 d2 &^ mask_2_42) in

    let open Hacl.UInt64 in
    let h0 = h0 +^ (c *^ uint64_to_sint64 5uL) in
    let c  = h0 >>^ 44ul in
    let h0 = h0 &^ mask_2_44 in
    let h1 = h1 +^ c in

    let len = U64 (len -^ 16uL) in
    let m   = offset m 16ul in
    poly1305_blocks_loop st m len r0 r1 r2 s1 s2 h0 h1 h2
  )


val poly1305_blocks:
  st:poly1305_state ->
  m:uint8_p ->
  len:FStar.UInt64.t ->
  Stack unit
    (requires (fun h -> True))
    (ensures  (fun h0 _ h1 -> True))
let poly1305_blocks st m len =
  let r0 = st.r.(0ul) in
  let r1 = st.r.(1ul) in
  let r2 = st.r.(2ul) in
  let h0 = st.h.(0ul) in
  let h1 = st.h.(1ul) in
  let h2 = st.h.(2ul) in

  let five = uint64_to_sint64 5uL in
  let s1 = H64 (r1 *^ (five <<^ 2ul)) in
  let s2 = H64 (r2 *^ (five <<^ 2ul)) in

  (* let h0, h1, h2 = poly1305_blocks_loop m len r0 r1 r2 s1 s2 h0 h1 h2 in *)
  poly1305_blocks_loop st m len r0 r1 r2 s1 s2 h0 h1 h2;

  (* st.h.(0ul) <- h0; *)
  (* st.h.(1ul) <- h1; *)
  (* st.h.(2ul) <- h2; *)
  (* st.h.(0ul) <- t.t1; *)
  (* st.h.(1ul) <- t.t2; *)
  (* st.h.(2ul) <- t.t3; *)
  ()


val poly1305_finish:
  mac:uint8_p ->
  m:uint8_p ->
  len:U64.t ->
  key:uint8_p ->
  st:poly1305_state ->
  Stack unit
    (requires (fun _ -> True))
    (ensures  (fun _ _ _ -> True))
let poly1305_finish mac m len key st =
  push_frame();

  let mask_2_44 = uint64_to_sint64 0xfffffffffffuL in
  let mask_2_42 = uint64_to_sint64 0x3ffffffffffuL in

  let rem = U64 (len &^ 0xfuL) in

  let h0 = st.h.(0ul) in
  let h1 = st.h.(1ul) in
  let h2 = st.h.(2ul) in
  let r0 = st.r.(0ul) in
  let r1 = st.r.(1ul) in
  let r2 = st.r.(2ul) in
  let five = uint64_to_sint64 5uL in
  let s1 = H64 (r1 *^ (five <<^ 2ul)) in
  let s2 = H64 (r2 *^ (five <<^ 2ul)) in

  (* let h0, h1, h2 = *)
  (* let t = *)
    if U64 (rem =^ 0uL) then ()// {t1 = h0; t2 = h1; t3 = h2}
    else (
      let zero = uint8_to_sint8 0uy in
      let block = create zero 16ul in
      let i = FStar.Int.Cast.uint64_to_uint32 rem in
      blit m (FStar.Int.Cast.uint64_to_uint32 (H64 (len -^ rem))) block 0ul i;
      block.(i) <- uint8_to_sint8 1uy;

      let t0 = load64_le block in
      let t1 = load64_le (offset block 8ul) in

      let open Hacl.UInt64 in

      let h0 = h0 +^ (t0 &^ mask_2_44) in
      let h1 = h1 +^ (((t0 >>^ 44ul) |^ (t1 <<^ 20ul)) &^ mask_2_44) in
      let h2 = h2 +^ ((t1 >>^ 24ul) &^ mask_2_42) in

      let open Hacl.UInt128 in

      let d0 = h0 *^ r0 in
      let d  = h1 *^ s2 in
      let d0 = d0 +^ d  in
      let d  = h2 *^ s1 in
      let d0 = d0 +^ d  in

      let d1 = h0 *^ r1 in
      let d  = h1 *^ r0 in
      let d1 = d1 +^ d  in
      let d  = h2 *^ s2 in
      let d1 = d1 +^ d  in

      let d2 = h0 *^ r2 in
      let d  = h1 *^ r1 in
      let d2 = d2 +^ d  in
      let d  = h2 *^ r0 in
      let d2 = d2 +^ d  in

      let c  = sint128_to_sint64 (d0 >>^ 44ul) in
      let h0 = H64 (sint128_to_sint64 d0 &^ mask_2_44) in
      let d1 = d1 +^ sint64_to_sint128 c in

      let c  = sint128_to_sint64 (d1 >>^ 44ul) in
      let h1 = H64 (sint128_to_sint64 d1 &^ mask_2_44) in
      let d2 = d2 +^ sint64_to_sint128 c in

      let c  = sint128_to_sint64 (d2 >>^ 42ul) in
      let h2 = H64 (sint128_to_sint64 d2 &^ mask_2_42) in

      let open Hacl.UInt64 in
      let h0 = h0 +^ (c *^ uint64_to_sint64 5uL) in
      let c  = h0 >>^ 44ul in
      let h0 = h0 &^ mask_2_44 in
      let h1 = h1 +^ c in
      st.h.(0ul) <- h0;
      st.h.(1ul) <- h1;
      st.h.(2ul) <- h2
      (* h0, h1, h2 *)
    );

  let h0 = st.h.(0ul) in
  let h1 = st.h.(1ul) in
  let h2 = st.h.(2ul) in

  let open Hacl.UInt64 in

  let c  = h1 >>^ 44ul in
  let h1 = h1 &^ mask_2_44 in
  let h2 = h2 +^ c in
  let c  = h2 >>^ 42ul in
  let h2 = h2 &^ mask_2_42 in
  let h0 = h0 +^ (c *^ uint64_to_sint64 5uL) in
  let c  = h0 >>^ 44ul in
  let h0 = h0 &^ mask_2_44 in
  let h1 = h1 +^ c in
  let c  = h1 >>^ 44ul in
  let h1 = h1 &^ mask_2_44 in
  let h2 = h2 +^ c in
  let c  = h2 >>^ 42ul in
  let h2 = h2 &^ mask_2_42 in
  let h0 = h0 +^ (c *^ uint64_to_sint64 5uL) in
  let c  = h0 >>^ 44ul in
  let h0 = h0 &^ mask_2_44 in
  let h1 = h1 +^ c in

  let mask = (eq_mask h0 mask_2_44)
             &^ (eq_mask h1 mask_2_44)
             &^ (gte_mask h2 (uint64_to_sint64 0x3fffffffffbuL)) in
  let h0 = h0 &^ lognot mask in
  let h1 = h1 &^ lognot mask in
  let h2 = h2 -^ ((uint64_to_sint64 0x3fffffffffbuL) &^ mask) in

  let t0 = load64_le (offset key 16ul) in
  let t1 = load64_le (offset key 24ul) in

  let h0 = h0 +^ (t0 &^ mask_2_44) in
  let c  = h0 >>^ 44ul in
  let h0 = h0 &^ mask_2_44 in
  let h1 = h1 +^ (((t0 >>^ 44ul) |^ (t1 <<^ 20ul)) &^ mask_2_44) +^ c in
  let c  = h1 >>^ 44ul in
  let h1 = h1 &^ mask_2_44 in
  let h2 = h2 +^ ((t1 >>^ 24ul) &^ mask_2_42) +^ c in
  let h2 = h2 &^ mask_2_42 in

  let h0 = h0 |^ (h1 <<^ 44ul) in
  let h1 = (h1 >>^ 20ul) |^ (h2 <<^ 24ul) in

  store64_le mac h0;
  store64_le (offset mac 8ul) h1;
  pop_frame()

val crypto_onetimeauth:
  output:uint8_p ->
  input:uint8_p ->
  len:U64.t ->
  k:uint8_p ->
  Stack unit
    (requires (fun _ -> True))
    (ensures  (fun _ _ _ -> True))
let crypto_onetimeauth output input len k =
  push_frame();
  let zero = uint64_to_sint64 0uL in
  let r = create zero 3ul in
  let h = create zero 3ul in
  let st = {r = r; h = h} in
  poly1305_init st k;
  poly1305_blocks st input len;
  poly1305_finish output input len k st;
  pop_frame()
