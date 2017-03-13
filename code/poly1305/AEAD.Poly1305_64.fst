module AEAD.Poly1305_64


open FStar.Mul
open FStar.ST
open FStar.Ghost
open FStar.Seq
open FStar.HyperStack
open FStar.Endianness
open FStar.Buffer

open Hacl.Spec.Endianness
open Hacl.Endianness

open Hacl.Cast
open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Spec.Bignum.AddAndMultiply
open Hacl.Spe.Poly1305_64
open Hacl.Bignum.AddAndMultiply
open Hacl.Impl.Poly1305_64

module H8   = Hacl.UInt8
module Limb = Hacl.Bignum.Limb
module Wide = Hacl.Bignum.Wide
module U8   = FStar.UInt8
module U32  = FStar.UInt32
module U64  = FStar.UInt64


module Spec = Spec.Chacha20Poly1305

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"


val pad_16_bytes:
  input:uint8_p ->
  len:U32.t{length input = U32.v len /\ U32.v len < 16 /\ U32.v len > 0} ->
  StackInline (uint8_p)
    (requires (fun h -> live h input))
    (ensures (fun h0 output h1 -> live h0 input /\ live h1 output /\ frameOf output = h1.tip
      /\ modifies_0 h0 h1 /\ length output = 16
      /\ (let o = as_seq h1 output in let i = as_seq h0 input in
         o == Spec.pad_16 i)))
let pad_16_bytes input len =
  let h0 = ST.get() in
  let b = Buffer.create (uint8_to_sint8 0uy) 16ul in
  Buffer.blit input 0ul b 0ul len;
  let h = ST.get() in
  no_upd_lemma_0 h0 h input;
  Seq.lemma_eq_intro (as_seq h input) (Seq.slice (as_seq h input) 0 (U32.v len));
  Seq.lemma_eq_intro (Seq.slice (as_seq h b) (U32.v len) 16) (Seq.create (16 - U32.v len) (uint8_to_sint8 0uy));
  Seq.lemma_eq_intro (as_seq h b) (Spec.pad_16 (as_seq h0 input));
  b

module Poly = Hacl.Standalone.Poly1305_64
module Impl = Hacl.Impl.Poly1305_64


val blocks:
  current_log:Impl.log_t ->
  st:Impl.poly1305_state ->
  m:Impl.uint8_p ->
  len:U64.t{16 * U64.v len = length m} ->
  Stack Impl.log_t
    (requires (fun h -> Impl.(live_st h st /\ live h m /\ disjoint st.r m /\ disjoint st.h m
      /\ red_45 (as_seq h st.h)
      /\ red_44 (as_seq h st.r)
    )))
    (ensures  (fun h0 updated_log h1 -> Impl.(modifies_1 st.h h0 h1 /\ live_st h1 st /\ live_st h0 st /\ live h0 m
      /\ red_45 (as_seq h0 st.h)
      /\ red_44 (as_seq h0 st.r)
      /\ red_44 (as_seq h1 st.r)
      /\ red_45 (as_seq h1 st.h)
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
    let new_log = Impl.poly1305_update log st block in
    let len = U64.(len -^ 1uL) in
    blocks new_log st tail len
  )



val poly1305_alloc:
  unit -> StackInline poly1305_state
    (requires (fun h -> True))
    (ensures (fun h0 st h1 -> modifies_0 h0 h1 /\ live_st h1 st))
let poly1305_alloc () = Impl.alloc ()

private let lemma_div (x:nat) : Lemma (16 * (x / 16) <= x /\ 16 * (x / 16) >= 0) =
  Math.Lemmas.lemma_div_mod x 16

inline_for_extraction
let mul_div_16 (len:U32.t) : Tot (len':U32.t{U32.v len' = 16 * (U32.v len / 16)}) =
  lemma_div (U32.v len); Math.Lemmas.lemma_div_mod (U32.v len) 16;
  assert_norm(pow2 4 = 16);
  U32.(16ul *^ (len >>^ 4ul))

#reset-options "--initial_fuel 0 -max_fuel 0 --z3rlimit 100"

val pad_last:
  log:log_t ->
  st:poly1305_state ->
  input:uint8_p{disjoint st.r input /\ disjoint st.h input} ->
  len:U32.t{U32.v len = length input /\ U32.v len < 16} ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h input
      /\ red_45 (as_seq h st.h)
      /\ red_44 (as_seq h st.r)))
    (ensures (fun h0 log h1 -> live_st h1 st /\ live h0 input/\ modifies_1 st.h h0 h1
      /\ red_45 (as_seq h1 st.h)
      /\ red_44 (as_seq h1 st.r)
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
    let l = poly1305_update log st b in
    pop_frame();
    l
  )

(* val pad_last: *)
(*   log:log_t -> *)
(*   st:poly1305_state -> *)
(*   input:uint8_p{disjoint st.r input /\ disjoint st.h input} -> *)
(*   len:U32.t{U32.v len = length input /\ U32.v len < 16} -> *)
(*   Stack log_t *)
(*     (requires (fun h -> live_st h st /\ live h input *)
(*       /\ red_45 (as_seq h st.h) *)
(*       /\ red_44 (as_seq h st.r) *)
(*         /\ (let r = as_seq h st.r in *)
(*          let acc = as_seq h st.h in *)
(*          let log = Ghost.reveal log in *)
(*          invariant (Hacl.Spec.Poly1305_64.MkState r acc log)))) *)
(*     (ensures (fun h0 log h1 -> live_st h1 st /\ live h0 input/\ modifies_1 st.h h0 h1 *)
(*       /\ red_45 (as_seq h1 st.h) *)
(*       /\ red_44 (as_seq h1 st.r) *)
(*       /\ (let r' = as_seq h1 st.r in *)
(*          let acc' = as_seq h1 st.h in *)
(*          let log = Ghost.reveal log in *)
(*          invariant (Hacl.Spec.Poly1305_64.MkState r' acc' log)) *)
(*     )) *)
(* let pad_last log st input len = *)
(*   cut (U32.v len >= 0 /\ U32.v len < 16); *)
(*   if U32.(len =^ 0ul) then admit() //log *)
(*   else ( *)
(*     cut (U32.v len <> 0); *)
(*     cut (U32.v len < 16); *)
(*     cut (U32.v len > 0 /\ U32.v len < 16); *)
(*     push_frame(); *)
(*     let h0 = ST.get() in *)
(*     let b = pad_16_bytes input len in *)
(*     let h = ST.get() in *)
(*     assume (as_seq h b == Seq.slice (as_seq h b) 0 16); //Seq.lemma_eq_intro (as_seq h b) (Seq.slice (as_seq h b) 0 16); *)
(*     Hacl.Standalone.Poly1305_64.lemma_poly1305_blocks_spec_1 (Hacl.Spec.Poly1305_64.MkState (as_seq h0 (Impl.MkState?.r st)) (as_seq h0 (Impl.MkState?.h st)) (reveal log)) (as_seq h b) 16uL; admit()) *)

(*   (\*   let l = poly1305_update log st b in *\) *)
(*   (\*   let h1 = ST.get() in *\) *)
(*   (\*   cut (modifies_2_1 st.h h0 h1); *\) *)
(*   (\*   pop_frame(); *\) *)
(*   (\*   l *\) *)
(*   (\* ) *\) *)

#reset-options "--initial_fuel 0 -max_fuel 0 --z3rlimit 100"


val poly1305_blocks_init:
  st:poly1305_state ->
  input:uint8_p{disjoint st.r input /\ disjoint st.h input} ->
  len:U32.t{U32.v len = length input} ->
  k:uint8_p{length k = 32 /\ disjoint k st.r /\ disjoint k st.h} ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h input /\ live h k))
    (ensures (fun h0 log h1 -> live_st h1 st /\ live h0 input /\ live h0 k /\ modifies_2 st.r st.h h0 h1
      /\ red_45 (as_seq h1 st.h)
      /\ red_44 (as_seq h1 st.r)
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


(* val poly1305_blocks_init: *)
(*   st:poly1305_state -> *)
(*   input:uint8_p{disjoint st.r input /\ disjoint st.h input} -> *)
(*   len:U32.t{U32.v len = length input} -> *)
(*   k:uint8_p{length k = 32 /\ disjoint k st.r /\ disjoint k st.h} -> *)
(*   Stack log_t *)
(*     (requires (fun h -> live_st h st /\ live h input /\ live h k *)
(*     )) *)
(*     (ensures (fun h0 log h1 -> live_st h1 st /\ live h0 input /\ live h0 k /\ modifies_2 st.r st.h h0 h1 *)
(*       /\ red_45 (as_seq h1 st.h) *)
(*       /\ red_44 (as_seq h1 st.r) *)
(*       /\ (let r' = as_seq h1 st.r in *)
(*          let acc' = as_seq h1 st.h in *)
(*          let log = Ghost.reveal log in *)
(*          invariant (Hacl.Spec.Poly1305_64.MkState r' acc' log)) *)
(*     )) *)
(* let poly1305_blocks_init st input len k = *)
(*   let len_16 = U32.(len >>^ 4ul) in *)
(*   let rem_16 = U32.(len &^ 15ul)  in *)
(*   assert_norm(pow2 4 = 16); *)
(*   UInt.logand_mask (U32.v len) 4; *)
(*   Math.Lemmas.lemma_div_mod (U32.v len) 16; *)
(*   lemma_div (U32.v len); *)
(*   let kr = Buffer.sub k 0ul 16ul in *)
(*   let len' = mul_div_16 len in *)
(*   let part_input = Buffer.sub input 0ul len' in *)
(*   let last_block = Buffer.offset input len' in *)
(*   cut (length last_block = U32.v rem_16); *)
(*   let l = Poly.poly1305_partial st part_input (Int.Cast.uint32_to_uint64 len_16) kr in *)
(*   pad_last l st last_block rem_16 *)


val poly1305_blocks_continue:
  log:log_t ->
  st:poly1305_state ->
  input:uint8_p{disjoint st.h input} ->
  len:U32.t{U32.v len = length input} ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h input
      /\ red_45 (as_seq h st.h)
      /\ red_44 (as_seq h st.r)
    ))
    (ensures (fun h0 log' h1 -> live_st h1 st /\ live h0 input /\ modifies_1 st.h h0 h1
      /\ red_45 (as_seq h1 st.h)
      /\ red_44 (as_seq h1 st.r)
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


(* val poly1305_blocks_continue: *)
(*   log:log_t -> *)
(*   st:poly1305_state -> *)
(*   input:uint8_p{disjoint st.h input} -> *)
(*   len:U32.t{U32.v len = length input} -> *)
(*   Stack log_t *)
(*     (requires (fun h -> live_st h st /\ live h input *)
(*       /\ red_45 (as_seq h st.h) *)
(*       /\ red_44 (as_seq h st.r) *)
(*       /\ (let r = as_seq h st.r in *)
(*          let acc = as_seq h st.h in *)
(*          let log = Ghost.reveal log in *)
(*          invariant (Hacl.Spec.Poly1305_64.MkState r acc log)) *)
(*     )) *)
(*     (ensures (fun h0 log' h1 -> live_st h1 st /\ live h0 input /\ modifies_1 st.h h0 h1 *)
(*       /\ red_45 (as_seq h1 st.h) *)
(*       /\ red_44 (as_seq h1 st.r) *)
(*       /\ (let r = as_seq h1 st.r in *)
(*          let acc = as_seq h1 st.h in *)
(*          let log' = Ghost.reveal log' in *)
(*          invariant (Hacl.Spec.Poly1305_64.MkState r acc log')) *)
(*     )) *)
(* let poly1305_blocks_continue log st input len = *)
(*   let len_16 = U32.(len >>^ 4ul) in *)
(*   let rem_16 = U32.(len &^ 15ul)  in *)
(*   assert_norm(pow2 4 = 16); *)
(*   UInt.logand_mask (U32.v len) 4; *)
(*   Math.Lemmas.lemma_div_mod (U32.v len) 16; *)
(*   lemma_div (U32.v len); *)
(*   let len' = mul_div_16 len in *)
(*   let part_input = Buffer.sub input 0ul len' in *)
(*   let last_block = Buffer.offset input len' in *)
(*   let l = Poly.poly1305_blocks log st part_input (Int.Cast.uint32_to_uint64 len_16) in *)
(*   pad_last l st last_block rem_16 *)
(*   (\* if U32.(rem_16 =^ 0ul) then () *\) *)
(*   (\* else ( *\) *)
(*   (\*   push_frame(); *\) *)
(*   (\*   let b = pad_16_bytes (Buffer.offset input U32.(len -^ rem_16)) rem_16 in *\) *)
(*   (\*   let _ = poly1305_update l st b in *\) *)
(*   (\*   pop_frame() *\) *)
(*   (\* ) *\) *)

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 5"

val poly1305_blocks_finish:
  log:log_t ->
  st:poly1305_state ->
  input:uint8_p{disjoint st.h input /\ length input = 16} ->
  mac:uint8_p{disjoint st.h mac /\ disjoint mac input /\ length mac = 16} ->
  key_s:uint8_p{disjoint key_s st.h /\ disjoint key_s mac /\ length key_s = 16} ->
  Stack unit
    (requires (fun h -> live_st h st /\ live h input /\ live h mac /\ live h key_s
      /\ red_45 (as_seq h st.h)
      /\ red_44 (as_seq h st.r)
    ))
    (ensures (fun h0 _ h1 -> live h0 input /\ modifies_2 mac st.h h0 h1 /\ live h1 mac))
let poly1305_blocks_finish log st input mac key_s =
  let log = Impl.poly1305_update log st input in
  let log = Impl.poly1305_update_last log st (Buffer.offset input 16ul) 0uL in
  let _ = Impl.poly1305_finish st mac key_s in
  ()



(* val poly1305_blocks_finish: *)
(*   log:log_t -> *)
(*   st:poly1305_state -> *)
(*   input:uint8_p{disjoint st.h input /\ length input = 16} -> *)
(*   mac:uint8_p{disjoint st.h mac /\ disjoint mac input} -> *)
(*   key_s:uint8_p{disjoint key_s st.h /\ disjoint key_s mac} -> *)
(*   Stack unit *)
(*     (requires (fun h -> live_st h st /\ live h input /\ live h mac *)
(*       /\ red_45 (as_seq h st.h) *)
(*       /\ red_44 (as_seq h st.r) *)
(*       /\ (let r = as_seq h st.r in *)
(*          let acc = as_seq h st.h in *)
(*          let log = Ghost.reveal log in *)
(*          invariant (Hacl.Spec.Poly1305_64.MkState r acc log)) *)
(*     )) *)
(*     (ensures (fun h0 _ h1 -> live h0 input /\ modifies_2 mac st.h h0 h1 /\ live h1 mac)) *)
(* let poly1305_blocks_finish log st input mac key_s = *)
(*   let log = Impl.poly1305_update log st input in *)
(*   let log = Impl.poly1305_update_last log st (Buffer.offset input 16ul) 0uL in *)
(*   let _ = Impl.poly1305_finish st mac key_s in *)
(*   () *)
