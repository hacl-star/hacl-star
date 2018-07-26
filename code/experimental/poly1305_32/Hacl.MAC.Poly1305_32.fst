module Hacl.MAC.Poly1305_32

open FStar.HyperStack.All

module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.HyperStack.ST
open FStar.Ghost
open FStar.Seq
open FStar.Buffer
open FStar.HyperStack

open Hacl.Cast
open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
(* open Hacl.Spec.Bignum.AddAndMultiply *)
(* open Hacl.Spec.MAC.Poly1305_64 *)
open Hacl.Bignum.AddAndMultiply

module H8   = Hacl.UInt8
module Limb = Hacl.Bignum.Limb
module Wide = Hacl.Bignum.Wide
module U8   = FStar.UInt8
module U32  = FStar.UInt32
module U64  = FStar.UInt64

inline_for_extraction let log_t = unit

inline_for_extraction let bigint = felem
inline_for_extraction let uint8_p = buffer Hacl.UInt8.t

let elemB : Type0 = b:felem

let wordB = b:uint8_p{length b <= 16}
let wordB_16 = b:uint8_p{length b = 16}

noeq type poly1305_state = | MkState: r:bigint -> h:bigint -> poly1305_state

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val load32_le:
  b:uint8_p{length b = 8} ->
  Stack limb
    (requires (fun h -> live h b))
    (ensures  (fun h0 r h1 -> h0 == h1 /\ live h0 b
      (* /\ r == load64_le_spec (as_seq h1 b) *)
      ))
let load32_le b =
  assert_norm (pow2 32 = 0x100000000);
  let h = ST.get() in
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  Limb.(
    sint8_to_sint32 b0
    |^ (sint8_to_sint32 b1 <<^ 8ul)
    |^ (sint8_to_sint32 b2 <<^ 16ul)
    |^ (sint8_to_sint32 b3 <<^ 24ul)
  )


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val store32_le:
  b:uint8_p{length b = 8} ->
  z:Limb.t ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b
      (* /\ as_seq h1 b == store64_le_spec z *)
      ))
let store32_le b z =
  assert_norm (pow2 32 = 0x100000000);
  let open Hacl.Bignum.Limb in
  let b0 = sint32_to_sint8 z in
  let b1 = sint32_to_sint8 (z >>^ 8ul) in
  let b2 = sint32_to_sint8 (z >>^ 16ul) in
  let b3 = sint32_to_sint8 (z >>^ 24ul) in
  b.(0ul) <- b0;
  b.(1ul) <- b1;
  b.(2ul) <- b2;
  b.(3ul) <- b3


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 5"


let live_st m (st:poly1305_state) : Type0 =
  live m st.h /\ live m st.r /\ disjoint st.h st.r


(* ############################################################################# *)
(*                              API FOR THE RECORD LAYER                         *)
(* ############################################################################# *)


#set-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0"

inline_for_extraction val upd_5: b:felem -> b0:limb -> b1:limb -> b2:limb -> b3:limb -> b4:limb ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1
      (* /\ as_seq h1 b == create_3 b0 b1 b2 *)
    ))
inline_for_extraction let upd_5 b b0 b1 b2 b3 b4 =
  b.(0ul) <- b0;
  b.(1ul) <- b1;
  b.(2ul) <- b2;
  b.(3ul) <- b3;
  b.(4ul) <- b4

inline_for_extraction let mask_26 = uint32_to_limb 0x3fffffful

val poly1305_encode_r:
  r:bigint ->
  key:uint8_p{length key = 16} ->
  Stack unit
    (requires (fun h -> live h r /\ live h key /\ disjoint key r))
    (ensures  (fun h0 _ h1 -> modifies_1 r h0 h1 /\ live h1 r /\ live h0 key
      (* /\ red_44 (as_seq h1 r) *)
      (* /\ as_seq h1 r == poly1305_encode_r_spec (as_seq h0 key) *)
    ))
let poly1305_encode_r r key =
  let t0 = load32_le(sub key 0ul  4ul) in
  let t1 = load32_le(sub key 4ul  4ul) in
  let t2 = load32_le(sub key 8ul  4ul) in
  let t3 = load32_le(sub key 12ul 4ul) in
  let open Hacl.Bignum.Limb in
  let t0 = t0 &^ uint32_to_limb 0x0ffffffful in
  let t1 = t1 &^ uint32_to_limb 0x0ffffffcul in
  let t2 = t2 &^ uint32_to_limb 0x0ffffffcul in
  let t3 = t3 &^ uint32_to_limb 0x0ffffffcul in
  let r0 = t0 &^ mask_26 in
  let r1 = ((t0 >>^ 26ul) |^ (t1 <<^ 6ul)) &^ mask_26 in
  let r2 = ((t1 >>^ 20ul) |^ (t2 <<^ 12ul)) &^ mask_26 in
  let r3 = ((t2 >>^ 14ul) |^ (t3 <<^ 18ul)) &^ mask_26 in
  let r4 = ((t3 >>^ 8ul)) &^ mask_26 in
  upd_5 r r0 r1 r2 r3 r4



val toField:
  b:bigint ->
  m:wordB_16 ->
  Stack unit
    (requires (fun h -> live h b /\ live h m /\ disjoint b m))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b /\ live h0 m
    ))
let toField b m =
  (* Load block values *)
  let t0 = load32_le(sub m 0ul  4ul) in
  let t1 = load32_le(sub m 4ul  4ul) in
  let t2 = load32_le(sub m 8ul  4ul) in
  let t3 = load32_le(sub m 12ul 4ul) in
  let open Hacl.Bignum.Limb in
  let r0 = t0 &^ mask_26 in
  let r1 = ((t0 >>^ 26ul) |^ (t1 <<^ 6ul)) &^ mask_26 in
  let r2 = ((t1 >>^ 20ul) |^ (t2 <<^ 12ul)) &^ mask_26 in
  let r3 = ((t2 >>^ 14ul) |^ (t3 <<^ 18ul)) &^ mask_26 in
  let r4 = ((t3 >>^ 8ul)) &^ mask_26 in
  upd_5 b r0 r1 r2 r3 r4


val toField_plus_2_128:
  b:bigint ->
  m:wordB_16 ->
  Stack unit
    (requires (fun h -> live h b /\ live h m /\ disjoint b m))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b /\ live h0 m
      (* /\ red_44 (as_seq h1 b) *)
      (* /\ as_seq h1 b == toField_plus_2_128_spec (as_seq h0 m) *)
    ))
let toField_plus_2_128 b m =
  let open Hacl.Bignum.Limb in
  toField b m;
  let b4 = b.(4ul) in
  let b4' = uint32_to_limb 0x1000000ul |^ b4 in
  b.(4ul) <- b4'


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val poly1305_start:
  a:elemB ->
  Stack unit
    (requires (fun h -> live h a))
    (ensures  (fun h0 _ h1 -> live h1 a /\ modifies_1 a h0 h1
    ))
let poly1305_start a =
  (* Zeroing the accumulator *)
  upd_5 a limb_zero limb_zero limb_zero limb_zero limb_zero


(* ******************* *)
(* Fast implementation *)
(* ******************* *)

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val poly1305_init_:
  st:poly1305_state ->
  key:uint8_p{length key = 32} ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h key /\ disjoint st.r key
      /\ disjoint st.h key
    ))
    (ensures  (fun h0 log h1 -> modifies_2 st.r st.h h0 h1 /\ live h0 key
      /\ live h1 st.r /\ live h1 st.h
    ))
let poly1305_init_ st key =
  poly1305_encode_r st.r (sub key 0ul 16ul);
  poly1305_start st.h


val poly1305_update:
  current_log:log_t ->
  st:poly1305_state ->
  m:uint8_p{length m >= 16} ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h m /\ disjoint m st.h /\ disjoint m st.r
    ))
    (ensures  (fun h0 updated_log h1 -> modifies_1 st.h h0 h1 /\ live_st h1 st /\ live_st h0 st
      /\ live h0 m
    ))
let poly1305_update log st m =
  push_frame();
  let tmp = create limb_zero clen in
  let acc = st.h in
  let r   = st.r in
  toField_plus_2_128 tmp (sub m 0ul 16ul);
  add_and_multiply acc tmp r;
  pop_frame()


val poly1305_blocks:
  current_log:log_t ->
  st:poly1305_state ->
  m:uint8_p ->
  len:U64.t{U64.v len <= length m} ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h m /\ disjoint st.r m /\ disjoint st.h m
    ))
    (ensures  (fun h0 updated_log h1 -> modifies_1 st.h h0 h1 /\ live_st h1 st /\ live_st h0 st /\ live h0 m
    ))
let rec poly1305_blocks log st m len =
  let m0 = ST.get() in
  if U64.(len <^ 16uL) then (
    ()
  )
  else (
    let new_log = poly1305_update log st m in
    let len = U64.(len -^ 16uL) in
    let m   = offset m 16ul in
    poly1305_blocks new_log st m len
  )


inline_for_extraction val poly1305_concat:
  b:uint8_p{length b = 16} ->
  m:uint8_p{disjoint b m} ->
  len:U64.t{U64.v len < 16 /\ U64.v len = length m} ->
  Stack unit
    (requires (fun h -> live h m /\ live h b
    ))
    (ensures (fun h0 _ h1 -> live h0 m /\ live h0 b /\ live h1 b /\ modifies_1 b h0 h1
    ))
inline_for_extraction let poly1305_concat b m len =
  let i = FStar.Int.Cast.uint64_to_uint32 len in
  blit m 0ul b 0ul i


val poly1305_process_last_block_:
  block:uint8_p{length block = 16} ->
  st:poly1305_state ->
  m:uint8_p ->
  len:U64.t{U64.v len < 16 /\ U64.v len = length m} ->
  Stack unit
    (requires (fun h -> live_st h st /\ live h m /\ live h block
      /\ disjoint block st.h /\ disjoint block st.r /\ disjoint block m
    ))
    (ensures (fun h0 _ h1 -> live_st h0 st /\ live h0 m /\ live_st h1 st /\ live h0 block
      /\ modifies_1 st.h h0 h1
    ))
#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"
let poly1305_process_last_block_ block st m rem' =
  push_frame();
  let tmp = create limb_zero clen in
  let i = FStar.Int.Cast.uint64_to_uint32 rem' in
  toField tmp block;
  add_and_multiply st.h tmp st.r;
  pop_frame()


val poly1305_process_last_block:
  st:poly1305_state ->
  m:uint8_p ->
  len:U64.t{U64.v len < 16 /\ U64.v len = length m} ->
  Stack unit
    (requires (fun h -> live_st h st /\ live h m
    ))
    (ensures (fun h0 _ h1 -> live_st h0 st /\ live h0 m /\ live_st h1 st /\ modifies_1 st.h h0 h1
    ))
let poly1305_process_last_block st m rem' =
  push_frame();
  let zero = uint8_to_sint8 0uy in
  let block = create zero 16ul in
  let i = FStar.Int.Cast.uint64_to_uint32 rem' in
  poly1305_concat block m rem';
  block.(i) <- uint8_to_sint8 1uy;
  poly1305_process_last_block_ block st m rem';
  pop_frame()


val poly1305_last_pass: acc:felem ->
  Stack unit
    (requires (fun h -> live h acc
    ))
    (ensures (fun h0 _ h1 -> live h0 acc /\ live h1 acc  /\ modifies_1 acc h0 h1
    ))
let poly1305_last_pass acc =
  Hacl.Bignum.Fproduct.carry_limb_ acc;
  Hacl.Bignum.Modulo.carry_top acc;
  Hacl.Bignum.Fproduct.carry_limb_ acc;
  Hacl.Bignum.Modulo.carry_top acc;
  Hacl.Bignum.Fproduct.carry_0_to_1 acc;
  let p26m1 = 0x3fffffful in
  let p26m5 = 0x3fffffbul in
  let a0 = acc.(0ul) in
  let a1 = acc.(1ul) in
  let a2 = acc.(2ul) in
  let a3 = acc.(3ul) in
  let a4 = acc.(4ul) in
  let mask0 = Hacl.Bignum.Limb.gte_mask a0 p26m5 in
  let mask1 = Hacl.Bignum.Limb.eq_mask  a1 p26m1 in
  let mask2 = Hacl.Bignum.Limb.eq_mask  a2 p26m1 in
  let mask3 = Hacl.Bignum.Limb.eq_mask  a3 p26m1 in
  let mask4 = Hacl.Bignum.Limb.eq_mask  a4 p26m1 in
  let mask  = Limb.(mask0 &^ mask1 &^ mask2 &^ mask3 &^ mask4) in
  let a0'   = Limb.(a0 -^ (p26m5 &^ mask)) in
  let a1'   = Limb.(a1 -^ (p26m1 &^ mask)) in
  let a2'   = Limb.(a2 -^ (p26m1 &^ mask)) in
  let a3'   = Limb.(a3 -^ (p26m1 &^ mask)) in
  let a4'   = Limb.(a4 -^ (p26m1 &^ mask)) in
  upd_5 acc a0' a1' a2' a3' a4'

(* val store128_le: *)
(*   mac:uint8_p{length mac = 16} -> *)
(*   mac':wide -> *)
(*   Stack unit *)
(*     (requires (fun h -> live h mac)) *)
(*     (ensures (fun h0 _ h1 -> live h1 mac /\ modifies_1 mac h0 h1 *)
(*     )) *)
(* #reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100" *)
(* let store128_le mac mac' = *)
(*   let open Hacl.Bignum.Wide in *)
(*   let macl = wide_to_limb mac' in *)
(*   let mach = wide_to_limb (mac' >>^ 64ul) in *)
(*   store32_le (Buffer.sub mac 0ul 8ul) macl; *)
(*   store64_le (Buffer.sub mac 8ul 8ul) mach *)


inline_for_extraction val poly1305_finish__:
  log:log_t ->
  st:poly1305_state ->
  mac:uint8_p{length mac = 16} ->
  m:uint8_p ->
  len:U64.t{U64.v len < pow2 32 /\ U64.v len <= length m} ->
  key_s:uint8_p{length key_s = 16} ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h mac /\ live h m /\ live h key_s /\ disjoint st.h mac
    ))
    (ensures  (fun h0 updated_log h1 -> modifies_1 st.h h0 h1 /\ live_st h0 st /\ live h0 m
      /\ live h1 st.h /\ live h1 mac /\ live h0 key_s
    ))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"
inline_for_extraction let poly1305_finish__ log st mac m len key_s =
  let rem' = U64.(len &^ 0xfuL) in
  if U64.(rem' =^ 0uL) then ()
  else (
    let start = Int.Cast.uint64_to_uint32 U64.(len -^ rem') in
    let l = Int.Cast.uint64_to_uint32 rem' in
    let last_block = sub m start l in
    poly1305_process_last_block st (sub m start l) rem'
    );
  ()


val poly1305_finish_:
  log:log_t ->
  st:poly1305_state ->
  mac:uint8_p{length mac = 16} ->
  m:uint8_p ->
  len:U64.t{U64.v len < pow2 32 /\ U64.v len <= length m} ->
  key_s:uint8_p{length key_s = 16} ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h mac /\ live h m /\ live h key_s
      /\ disjoint st.h mac /\ disjoint st.h key_s /\ disjoint st.h m
    ))
    (ensures  (fun h0 updated_log h1 -> modifies_2 st.h mac h0 h1 /\ live_st h0 st /\ live h0 m
      /\ live h1 st.h /\ live h1 mac /\ live h0 key_s
   ))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 200"
let poly1305_finish_ log st mac m len key_s =
  push_frame();
  let tmp = create limb_zero 5ul in
  toField tmp key_s;
  poly1305_finish__ log st mac m len key_s;
  poly1305_last_pass st.h;
  Hacl.Bignum.Fsum.fsum_ st.h tmp;
  Hacl.Bignum.Fproduct.carry_limb_ st.h;
  let k0 = load32_le (sub key_s 0ul  4ul) in
  let k1 = load32_le (sub key_s 4ul  4ul) in
  let k2 = load32_le (sub key_s 8ul  4ul) in
  let k3 = load32_le (sub key_s 12ul 4ul) in
  let h0 = st.h.(0ul) in
  let h1 = st.h.(1ul) in
  let h2 = st.h.(2ul) in
  let h3 = st.h.(3ul) in
  let h4 = st.h.(4ul) in
  let open Hacl.Bignum.Limb in
  let acc0 = h0 |^ (h1 <<^ 26ul) in
  let acc1 = (h1 >>^ 6ul ) |^ (h2 <<^ 20ul) in
  let acc2 = (h2 >>^ 12ul) |^ (h3 <<^ 14ul) in
  let acc3 = (h3 >>^ 18ul) |^ (h4 <<^  8ul) in
  let open Hacl.Bignum.Wide in
  store32_le (Buffer.sub mac 0ul  4ul) acc0;
  store32_le (Buffer.sub mac 4ul  4ul) acc1;
  store32_le (Buffer.sub mac 8ul  4ul) acc2;
  store32_le (Buffer.sub mac 12ul 4ul) acc3;
  pop_frame()


val crypto_onetimeauth:
  output:uint8_p{length output = 16} ->
  input:uint8_p{disjoint input output} ->
  len:U64.t{U64.v len < pow2 32 /\ U64.v len <= length input} ->
  k:uint8_p{disjoint output k /\ length k = 32} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input /\ live h k))
    (ensures  (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1 /\ live h0 input /\ live h0 k
      (* /\ as_seq h1 output == crypto_onetimeauth_spec (as_seq h0 input) len (as_seq h0 k) *)
    ))
let crypto_onetimeauth output input len k =
  push_frame();
  let buf = create limb_zero U32.(clen +^ clen) in
  let r = sub buf 0ul clen in
  let h = sub buf clen clen in
  let st = MkState r h in
  let key_r = Buffer.sub k 0ul 16ul in
  let key_s = Buffer.sub k 16ul 16ul in
  let init_log = poly1305_init_ st k in
  let partial_log = poly1305_blocks init_log st input len in
  let final_log = poly1305_finish_ partial_log st output input len key_s in
  pop_frame()
