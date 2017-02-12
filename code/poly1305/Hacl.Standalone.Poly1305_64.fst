module Hacl.Standalone.Poly1305_64


open FStar.Mul
open FStar.ST
open FStar.Ghost
open FStar.Seq
open FStar.HyperStack
open FStar.Endianness
open FStar.Buffer

open Hacl.Endianness

open Hacl.Cast
open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Spec.Bignum.AddAndMultiply
open Hacl.Spe.Poly1305_64
open Hacl.Bignum.AddAndMultiply

module H8   = Hacl.UInt8
module Limb = Hacl.Bignum.Limb
module Wide = Hacl.Bignum.Wide
module U8   = FStar.UInt8
module U32  = FStar.UInt32
module U64  = FStar.UInt64

module P    = Hacl.Impl.Poly1305_64
module Spec = Hacl.Spec.Poly1305_64
module Spec2 = Hacl.Spe.Poly1305_64

(* ************************************************ *)
(*                Standalone code                   *)
(* ************************************************ *)

#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 20"

private let lemma_poly1305_blocks_spec_0 (st:Spec.poly1305_state_{invariant st}) (m:Seq.seq H8.t) (len:U64.t{16*U64.v len = Seq.length m /\ U64.v len = 0}) : Lemma
  (poly1305_blocks_spec st m len == st)
  = ()


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"
private val lemma_poly1305_blocks_spec_1
  (st:Spec.poly1305_state_{invariant st})
  (m:Seq.seq H8.t)
  (len:U64.t{16*U64.v len = Seq.length m /\ U64.v len > 0}) : Lemma
  (let block = Seq.slice m 0 16 in
   let m'    = Seq.slice m 16 (Seq.length m) in
   let st'   = poly1305_update_spec st block in
   Seq.length m' = 16*(U64.v len - 1) /\ invariant st' /\
   (let st'':Spec.poly1305_state_  = poly1305_blocks_spec st' m' U64.(len -^ 1uL) in
   poly1305_blocks_spec st m len == st''))
#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 200"
private let lemma_poly1305_blocks_spec_1 st m len =
  let block = Seq.slice m 0 16 in
   let m'    = Seq.slice m 16 (Seq.length m) in
   let st'   = poly1305_update_spec st block in
   cut (Seq.length m' = 16*(U64.v len - 1) /\ invariant st'); admit()


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val poly1305_blocks:
  current_log:log_t ->
  st:poly1305_state ->
  m:uint8_p ->
  len:U64.t{16 * U64.v len = length m} ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h m /\ disjoint st.r m /\ disjoint st.h m
      /\ red_45 (as_seq h st.h)
      /\ red_44 (as_seq h st.r)
      /\ (let r = as_seq h st.r in
         let acc = as_seq h st.h in
         let log = reveal current_log in
         invariant (Spec.MkState r acc log))
      ))
    (ensures  (fun h0 updated_log h1 -> modifies_1 st.h h0 h1 /\ live_st h1 st /\ live_st h0 st /\ live h0 m
      /\ red_45 (as_seq h0 st.h)
      /\ red_44 (as_seq h0 st.r)
      /\ red_44 (as_seq h1 st.r)
      /\ red_45 (as_seq h1 st.h)
      /\ (let r = as_seq h0 st.r in
         let acc = as_seq h0 st.h in
         let log = reveal current_log in
         let r' = as_seq h1 st.r in
         let acc' = as_seq h1 st.h in
         let log' = reveal updated_log in
         let m = as_seq h0 m in
         invariant (Spec.MkState r acc log)
         /\ invariant (Spec.MkState r' acc' log')
         /\ Spec.MkState r acc' log' == Hacl.Spe.Poly1305_64.poly1305_blocks_spec (Spec.MkState r acc log) m len)
      ))
#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 100"


let rec poly1305_blocks log st m len =
  let h0 = ST.get() in
  if U64.(len =^ 0uL) then (
    (* admit() *)
    log
  )
  else (
    cut (U64.v len >= 1);
    let block = Buffer.sub m 0ul 16ul in
    let tail  = Buffer.offset m 16ul in
    cut (let mm = as_seq h0 m in
         let b = slice mm 0 16 in
         let m' = slice mm 16 (length m) in
        b == as_seq h0 block /\ m' == as_seq h0 tail);
    let new_log = poly1305_update log st block in
    (* let h1 = ST.get() in *)
    (* let acc   = MkState?.h st in *)
    (* let r     = MkState?.r st in *)
    (* cut (reveal new_log == Seq.cons ((as_seq h0 block)) (reveal log)); *)
    (* Math.Lemmas.modulo_lemma (seval (as_seq h0 r)) (prime); *)
    (* lemma_poly1305_blocks_spec_1 (as_seq h0 block) (reveal log) (reveal new_log) (Spec.selem (as_seq h0 acc)) (seval (as_seq h0 r)) (Spec.selem (as_seq h1 acc)); *)
    (* append_cons_snoc (Spec.Poly1305.encode_bytes ((as_seq h0 m))) (as_seq h0 block) (reveal log); *)
    (* snoc_encode_bytes (as_seq h0 tail) (as_seq h0 block);     *)
    let len = U64.(len -^ 1uL) in
    poly1305_blocks new_log st tail len
  )


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val poly1305_partial:
  st:poly1305_state ->
  m:uint8_p ->
  len:U64.t{16 * U64.v len = length m} ->
  kr:uint8_p{length kr = 16} ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h m /\ disjoint st.r m /\ disjoint st.h m /\ live h kr))
    (ensures  (fun h0 updated_log h1 -> modifies_1 st.h h0 h1 /\ live_st h1 st /\ live_st h0 st /\ live h0 m
      /\ red_45 (as_seq h0 st.h) /\ red_44 (as_seq h0 st.r) /\ red_44 (as_seq h1 st.r) /\ red_45 (as_seq h1 st.h)
      /\ live h0 kr /\ live h1 kr
      /\ (let r' = as_seq h1 st.r in
         let acc' = as_seq h1 st.h in
         let log' = reveal updated_log in
         let m = as_seq h0 m in
         let k = as_seq h0 kr in
         invariant (Spec.MkState r' acc' log')
         /\ Spec.MkState r' acc' log' == Hacl.Spe.Poly1305_64.poly1305_partial m len k)
    ))
(* let poly1305_partial st input len kr = *)
(*   let partial_log = poly1305_init_ st kr in *)
(*   assert_norm(pow2 128 < pow2 130 - 5); *)
(*   poly_def_0 (MkState?.log init_st) (seval (MkState?.r init_st)); *)
(*   cut (invariant init_st); *)
(*   let partial_st = poly1305_blocks_spec init_st input len in *)
(*   cut (invariant partial_st); *)
(*   lemma_append_empty' (encode_bytes (reveal_sbytes input)) (MkState?.log init_st); *)
(*   partial_st *)




#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 50"

val crypto_onetimeauth:
  output:uint8_p{length output = 16} ->
  input:uint8_p{disjoint input output} ->
  len:U64.t{U64.v len < pow2 32 /\ U64.v len = length input} ->
  k:uint8_p{disjoint output k /\ length k = 32} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input /\ live h k))
    (ensures  (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1 /\ live h0 input /\ live h0 k
      /\ as_seq h1 output == Hacl.Spe.Poly1305_64.crypto_onetimeauth_spec (as_seq h0 input) len (as_seq h0 k)))
let crypto_onetimeauth output input len k =
  push_frame();
  let len16 = U64.(len >>^ 4ul) in
  let rem16 = U64.(len &^ 0xfuL) in
  let partial_input = Buffer.sub input 0ul U32.(16ul *^ Int.Cast.uint64_to_uint32 len16) in
  let last_block    = Buffer.sub input U32.(16ul *^ Int.Cast.uint64_to_uint32 len16) (Int.Cast.uint64_to_uint32 len) in
  let buf = create limb_zero U32.(clen +^ clen) in
  let r = sub buf 0ul clen in
  let h = sub buf clen clen in
  let st = MkState r h in
  let key_r = Buffer.sub k 0ul 16ul in
  let key_s = Buffer.sub k 16ul 16ul in
  let init_log = poly1305_init_ st key_r in
  let partial_log = poly1305_blocks init_log st partial_input len16 in
  let final_log = poly1305_finish_ partial_log st output last_block rem16 key_s in
  pop_frame()
