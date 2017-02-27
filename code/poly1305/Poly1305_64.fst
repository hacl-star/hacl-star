module Poly1305_64

open FStar.Mul
open FStar.ST
open FStar.Ghost
open FStar.Seq
open FStar.HyperStack
open FStar.Endianness
open FStar.Buffer
open Hacl.Cast


module H8   = Hacl.UInt8
module Limb = Hacl.Bignum.Limb
module Wide = Hacl.Bignum.Wide
module U8   = FStar.UInt8
module U32  = FStar.UInt32
module U64  = FStar.UInt64
module I = Hacl.Impl.Poly1305_64
module S = Hacl.Spec.Poly1305_64
module Poly = Hacl.Standalone.Poly1305_64
       	      

(* Type Aliases *)
type uint8_p = Buffer.buffer Hacl.UInt8.t
type key = k:uint8_p{length k = 32}

(* abstract  *)type state = I.poly1305_state
(* abstract *) type live_state (h:mem) (st:state) = I.live_st h st
(* abstract *) type stable (h:mem) (st:state) = live_state h st /\ S.red_45 (as_seq h I.(st.h)) /\ S.red_44 (as_seq h I.(st.r))

private let get_key (st:state) = I.MkState?.r st
private let get_accumulator (st:state) = I.MkState?.h st

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

val alloc:
  unit -> StackInline state
    (requires (fun h -> True))
    (ensures (fun h0 st h1 -> modifies_0 h0 h1 /\ live_state h1 st))
let alloc () =
  I.alloc()


val init:
  st:state ->
  k:uint8_p{length k >= 16} ->
  Stack unit
    (requires (fun h -> live h k /\ live_state h st))
    (ensures (fun h0 _ h1 -> modifies_2 (get_key st) (get_accumulator st) h0 h1 /\ stable h1 st))
let init st k =
  let _ = I.poly1305_init_ st (Buffer.sub k 0ul 16ul) in ()

let empty_log : I.log_t = Ghost.hide (Seq.createEmpty)

val update_block:
  st:state ->
  m:uint8_p{length m = 16} ->
  Stack unit
    (requires (fun h -> stable h st /\ live h m))
    (ensures  (fun h0 updated_log h1 -> modifies_1 (get_accumulator st) h0 h1 /\ stable h1 st))
let update_block st m =
  let _ = I.poly1305_update empty_log st m in ()


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val update:
  st:state ->
  m:uint8_p ->
  len:FStar.UInt32.t{length m >= 16 * UInt32.v len} ->
  Stack unit
    (requires (fun h -> stable h st /\ live h m))
    (ensures  (fun h0 updated_log h1 -> modifies_1 (get_accumulator st) h0 h1 /\ stable h1 st))
let rec update st m len =
  if FStar.UInt32.(len =^ 0ul) then ()
  else
    let block = Buffer.sub m 0ul 16ul in
    let m'    = Buffer.offset m 16ul  in
    let len   = FStar.UInt32.(len -^ 1ul) in
    let _ = update_block st block in
    update st m' len

  
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

module A = Hacl.Spec.Bignum.AddAndMultiply

(* abstract *) type before_finish h st = A.(live_state h st /\ bounds (as_seq h (get_accumulator st)) p44 p44 p42)


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val update_last:
  st:state ->
  m:uint8_p ->
  len:UInt32.t{UInt32.v len < 16 /\ UInt32.v len <= length m} ->
  Stack unit
    (requires (fun h -> stable h st /\ live h m))
    (ensures  (fun h0 _ h1 -> modifies_1 (get_accumulator st) h0 h1 /\ before_finish h1 st))
let update_last st m len =
  I.poly1305_update_last empty_log st (Buffer.sub m 0ul len) (Hacl.Cast.sint32_to_sint64 len)


val finish:
  st:state ->
  mac:uint8_p{length mac = 16} ->
  k:uint8_p{length k = 16} ->
  Stack unit
    (requires (fun h -> before_finish h st /\ live h mac /\ live h k))
    (ensures (fun h0 _ h1 -> modifies_1 mac h0 h1))
let finish st mac k =
  I.poly1305_finish st mac k


val crypto_onetimeauth:
  output:uint8_p{length output = 16} ->
  input:uint8_p{disjoint input output} ->
  len:U64.t{U64.v len < pow2 32 /\ U64.v len = length input} ->
  k:uint8_p{disjoint output k /\ length k = 32} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input /\ live h k))
    (ensures  (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1 /\ live h0 input /\ live h0 k
      /\ (let mac     = Hacl.Spec.Endianness.reveal_sbytes (as_seq h1 output) in
         let message = Hacl.Spec.Endianness.reveal_sbytes (as_seq h0 input) in
         let key     = Hacl.Spec.Endianness.reveal_sbytes (as_seq h0 k) in
         mac == Spec.Poly1305.poly1305 message key)))
let crypto_onetimeauth output input len k = Hacl.Standalone.Poly1305_64.crypto_onetimeauth output input len k


val pad_16_bytes:
  input:uint8_p ->
  len:U32.t{length input = U32.v len /\ U32.v len < 16 /\ U32.v len > 0} ->
  StackInline (uint8_p)
    (requires (fun h -> live h input))
    (ensures (fun h0 output h1 -> live h0 input /\ live h1 output /\ frameOf output = h1.tip
      /\ modifies_0 h0 h1 /\ length output = 16
      (* /\ (let o = as_seq h1 output in let i = as_seq h0 input in *)
      (*    o == Spec.pad_16 i) *)))
let pad_16_bytes input len =
  let h0 = ST.get() in
  let b = Buffer.create (uint8_to_sint8 0uy) 16ul in
  Buffer.blit input 0ul b 0ul len;
  let h = ST.get() in
  no_upd_lemma_0 h0 h input;
  Seq.lemma_eq_intro (as_seq h input) (Seq.slice (as_seq h input) 0 (U32.v len));
  Seq.lemma_eq_intro (Seq.slice (as_seq h b) (U32.v len) 16) (Seq.create (16 - U32.v len) (uint8_to_sint8 0uy));
  (* Seq.lemma_eq_intro (as_seq h b) (Spec.pad_16 (as_seq h0 input)); *)
  b

(* open Hacl.Spec.Bignum.AddAndMultiply *)
(* open Hacl.Spe.Poly1305_64 *)
(* open Hacl.Bignum.AddAndMultiply *)
(* open Hacl.Impl.Poly1305_64 *)


val blocks:
  current_log:I.log_t ->
  st:I.poly1305_state ->
  m:I.uint8_p ->
  len:U64.t{16 * U64.v len = length m} ->
  Stack I.log_t
    (requires (fun h -> I.(live_st h st /\ live h m /\ disjoint st.r m /\ disjoint st.h m
      /\ A.red_45 (as_seq h st.h)
      /\ A.red_44 (as_seq h st.r)
    )))
    (ensures  (fun h0 updated_log h1 -> I.(modifies_1 st.h h0 h1 /\ live_st h1 st /\ live_st h0 st /\ live h0 m
      /\ A.red_45 (as_seq h0 st.h)
      /\ A.red_44 (as_seq h0 st.r)
      /\ A.red_44 (as_seq h1 st.r)
      /\ A.red_45 (as_seq h1 st.h)
      )))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"
let rec blocks log st m len =
  let h0 = ST.get() in
  if U64.(len =^ 0uL) then (
    log
  )
  else (
    cut (U64.v len >= 1);
    let block = Buffer.sub m 0ul 16ul in
    let tail  = Buffer.offset m 16ul in
    let new_log = I.poly1305_update log st block in
    let len = U64.(len -^ 1uL) in
    blocks new_log st tail len
  )



val poly1305_alloc:
  unit -> StackInline I.poly1305_state
    (requires (fun h -> True))
    (ensures (fun h0 st h1 -> modifies_0 h0 h1 /\ I.live_st h1 st))
let poly1305_alloc () = I.alloc ()

private let lemma_div (x:nat) : Lemma (16 * (x / 16) <= x /\ 16 * (x / 16) >= 0) =
  Math.Lemmas.lemma_div_mod x 16

inline_for_extraction
let mul_div_16 (len:U32.t) : Tot (len':U32.t{U32.v len' = 16 * (U32.v len / 16)}) =
  lemma_div (U32.v len); Math.Lemmas.lemma_div_mod (U32.v len) 16;
  assert_norm(pow2 4 = 16);
  U32.(16ul *^ (len >>^ 4ul))

#reset-options "--initial_fuel 0 -max_fuel 0 --z3rlimit 100"

val pad_last:
  log:I.log_t ->
  st:I.poly1305_state ->
  input:uint8_p{disjoint I.(st.r) input /\ disjoint I.(st.h) input} ->
  len:U32.t{U32.v len = length input /\ U32.v len < 16} ->
  Stack I.log_t
    (requires (fun h -> I.live_st h st /\ live h input
      /\ A.red_45 (as_seq h I.(st.h))
      /\ A.red_44 (as_seq h I.(st.r))))
    (ensures (fun h0 log h1 -> I.live_st h1 st /\ live h0 input /\ modifies_1 I.(st.h) h0 h1
      /\ A.red_45 (as_seq h1 I.(st.h))
      /\ A.red_44 (as_seq h1 I.(st.r))
    ))
let pad_last log st input len =
  cut (U32.v len >= 0 /\ U32.v len < 16);
  if U32.(len =^ 0ul) then log
  else (
    cut (U32.v len <> 0);
    cut (U32.v len < 16);
    cut (U32.v len > 0 /\ U32.v len < 16);
    push_frame();
    let h0 = ST.get() in
    let b = pad_16_bytes input len in
    let h = ST.get() in
    let l = I.poly1305_update log st b in
    pop_frame();
    l
  )

#reset-options "--initial_fuel 0 -max_fuel 0 --z3rlimit 100"


val poly1305_blocks_init:
  st:I.poly1305_state ->
  input:uint8_p{disjoint I.(st.r) input /\ disjoint I.(st.h) input} ->
  len:U32.t{U32.v len = length input} ->
  k:uint8_p{length k = 32 /\ disjoint k I.(st.r) /\ disjoint k I.(st.h)} ->
  Stack I.log_t
    (requires (fun h -> I.live_st h st /\ live h input /\ live h k))
    (ensures (fun h0 log h1 -> I.live_st h1 st /\ live h0 input /\ live h0 k /\ modifies_2 I.(st.r) I.(st.h) h0 h1
      /\ A.red_45 (as_seq h1 I.(st.h))
      /\ A.red_44 (as_seq h1 I.(st.r))
    ))
let poly1305_blocks_init st input len k =
  let len_16 = U32.(len >>^ 4ul) in
  let rem_16 = U32.(len &^ 15ul)  in
  assert_norm(pow2 4 = 16);
  UInt.logand_mask (U32.v len) 4;
  Math.Lemmas.lemma_div_mod (U32.v len) 16;
  lemma_div (U32.v len);
  let kr = Buffer.sub k 0ul 16ul in
  let len' = mul_div_16 len in
  let part_input = Buffer.sub input 0ul len' in
  let last_block = Buffer.offset input len' in
  cut (length last_block = U32.v rem_16);
  let l = Poly.poly1305_partial st part_input (Int.Cast.uint32_to_uint64 len_16) kr in
  pad_last l st last_block rem_16


val poly1305_blocks_continue:
  log:I.log_t ->
  st:I.poly1305_state ->
  input:uint8_p{disjoint I.(st.h) input} ->
  len:U32.t{U32.v len = length input} ->
  Stack I.log_t
    (requires (fun h -> I.live_st h st /\ live h input
        /\ A.red_45 (as_seq h I.(st.h))
      /\ A.red_44 (as_seq h I.(st.r))
    ))
    (ensures (fun h0 log' h1 -> I.live_st h1 st /\ live h0 input /\ modifies_1 I.(st.h) h0 h1
      /\ A.red_45 (as_seq h1 I.(st.h))
      /\ A.red_44 (as_seq h1 I.(st.r))
    ))
let poly1305_blocks_continue log st input len =
  let len_16 = U32.(len >>^ 4ul) in
  let rem_16 = U32.(len &^ 15ul)  in
  assert_norm(pow2 4 = 16);
  UInt.logand_mask (U32.v len) 4;
  Math.Lemmas.lemma_div_mod (U32.v len) 16;
  lemma_div (U32.v len);
  let len' = mul_div_16 len in
  let part_input = Buffer.sub input 0ul len' in
  let last_block = Buffer.offset input len' in
  let l = blocks log st part_input (Int.Cast.uint32_to_uint64 len_16) in
  pad_last l st last_block rem_16


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 5"

val poly1305_blocks_finish:
  log:I.log_t ->
  st:I.poly1305_state ->
  input:uint8_p{disjoint I.(st.h) input /\ length input = 16} ->
  mac:uint8_p{disjoint I.(st.h) mac /\ disjoint mac input /\ length mac = 16} ->
  key_s:uint8_p{disjoint key_s I.(st.h) /\ disjoint key_s mac /\ length key_s = 16} ->
  Stack unit
    (requires (fun h -> I.live_st h st /\ live h input /\ live h mac /\ live h key_s
      /\ A.red_45 (as_seq h I.(st.h))
      /\ A.red_44 (as_seq h I.(st.r))
    ))
    (ensures (fun h0 _ h1 -> live h0 input /\ modifies_2 mac I.(st.h) h0 h1 /\ live h1 mac))
let poly1305_blocks_finish log st input mac key_s =
  let log = I.poly1305_update log st input in
  let log = I.poly1305_update_last log st (Buffer.offset input 16ul) 0uL in
  let _ = I.poly1305_finish st mac key_s in
  ()


(* The following values should point to Spec.Chacha20Poly1305 *)
let noncelen = 12
let keylen = 32
let maclen = 16


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 50"

val aead_encrypt:
  c:uint8_p ->
  mac:uint8_p{length mac = maclen /\ disjoint mac c} ->
  m:uint8_p{disjoint c m} ->
  mlen:u32{let len = U32.v mlen in len = length m /\ len = length c}  ->
  aad:uint8_p ->
  aadlen:u32{let len = U32.v aadlen in len = length aad}  ->
  k:uint8_p{length k = keylen} ->
  n:uint8_p{length n = noncelen} ->
  Stack u32
    (requires (fun h -> live h c /\ live h mac /\ live h m /\ live h n /\ live h k /\ live h aad))
    (ensures  (fun h0 z h1 -> modifies_2 c mac h0 h1 /\ live h1 c /\ live h1 mac))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"
let aead_encrypt c mac m mlen aad aadlen k n =
  push_frame();
  let tmp = create (uint8_to_sint8 0uy) 80ul in
  let b = Buffer.sub tmp 0ul 64ul in
  let lb = Buffer.sub tmp 64ul 16ul in
  (* let b = create (uint8_to_sint8 0uy) 64ul in *)
  (* let lb = create (uint8_to_sint8 0uy) 16ul in *)
  Chacha20.chacha20 c m mlen k n 1ul;
  Chacha20.chacha20_key_block b k n 0ul;
  let mk = Buffer.sub b 0ul 32ul in
  let key_s = Buffer.sub mk 16ul 16ul in
  push_frame();
  let st = P.alloc () in
  let log = P.poly1305_blocks_init st aad aadlen mk in
  let log = P.poly1305_blocks_continue log st c mlen in
  Hacl.Endianness.hstore64_le (Buffer.sub lb 0ul 8ul) (uint32_to_sint64 aadlen);
  Hacl.Endianness.hstore64_le (Buffer.sub lb 8ul 8ul) (uint32_to_sint64 mlen);
  let log = P.poly1305_blocks_finish log st lb mac key_s in
  pop_frame();
  pop_frame();
  0ul
