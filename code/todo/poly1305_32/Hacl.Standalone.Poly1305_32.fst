module Hacl.Standalone.Poly1305_32

open FStar.HyperStack.All

module ST = FStar.HyperStack.ST


open FStar.Mul
open FStar.HyperStack.ST
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
open Hacl.Spe.Poly1305_32
open Hacl.Bignum.AddAndMultiply

module H8   = Hacl.UInt8
module Limb = Hacl.Bignum.Limb
module Wide = Hacl.Bignum.Wide
module U8   = FStar.UInt8
module U32  = FStar.UInt32
module U64  = FStar.UInt64

module P    = Hacl.Impl.Poly1305_32
module Spec = Hacl.Spec.Poly1305_32
module Spec2 = Hacl.Spe.Poly1305_32

(* ************************************************ *)
(*                Standalone code                   *)
(* ************************************************ *)

#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 20"

private noextract let lemma_poly1305_blocks_spec_0 (st:Spec.poly1305_state_{invariant st}) (m:Seq.seq H8.t) (len:U64.t{16*U64.v len = Seq.length m /\ U64.v len = 0}) : Lemma
  (poly1305_blocks_spec st m len == st)
  = ()


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"
private noextract val lemma_poly1305_blocks_spec_1_
  (st:Spec.poly1305_state_{invariant st})
  (m:Seq.seq H8.t)
  (len:U64.t{16*U64.v len = Seq.length m /\ U64.v len > 0}) : Lemma
  (let block = Seq.slice m 0 16 in
   let m'    = Seq.slice m 16 (Seq.length m) in
   let st'   = poly1305_update_spec st block in
   Seq.length m' = 16*(U64.v len - 1) /\ invariant st')
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"
private noextract let lemma_poly1305_blocks_spec_1_ st m len =
  let block = Seq.slice m 0 16 in
  let m'    = Seq.slice m 16 (Seq.length m) in
  let st'   = poly1305_update_spec st block in
  let r = Spec.MkState?.r st in
  let log = Spec.MkState?.log st in
  let log' = Spec.MkState?.log st' in
  let acc = Spec.MkState?.h st in
  let acc' = Spec.MkState?.h st' in
  Math.Lemmas.distributivity_sub_right 16 (U64.v len) 1;
  Math.Lemmas.modulo_lemma (seval r) (prime);
  lemma_poly1305_blocks_spec_1 block log log' (Spec.selem acc) (seval r) (Spec.selem acc')


noextract val lemma_poly1305_blocks_spec_1
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
noextract let lemma_poly1305_blocks_spec_1 st m len =
  lemma_poly1305_blocks_spec_1_ st m len


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val poly1305_blocks:
  current_log:P.log_t ->
  st:P.poly1305_state ->
  m:P.uint8_p ->
  len:U64.t{16 * U64.v len = length m} ->
  Stack P.log_t
    (requires (fun h -> P.(live_st h st /\ live h m /\ disjoint st.r m /\ disjoint st.h m
      /\ red_y (as_seq h st.h)
      /\ red_26 (as_seq h st.r)
      /\ (let r = as_seq h st.r in
         let acc = as_seq h st.h in
         let log = Ghost.reveal current_log in
         invariant (Spec.MkState r acc log)))
      ))
    (ensures  (fun h0 updated_log h1 -> P.(modifies_1 st.h h0 h1 /\ live_st h1 st /\ live_st h0 st /\ live h0 m
      /\ red_y (as_seq h0 st.h)
      /\ red_26 (as_seq h0 st.r)
      /\ red_26 (as_seq h1 st.r)
      /\ red_y (as_seq h1 st.h)
      /\ (let r = as_seq h0 st.r in
         let acc = as_seq h0 st.h in
         let log = Ghost.reveal current_log in
         let r' = as_seq h1 st.r in
         let acc' = as_seq h1 st.h in
         let log' = Ghost.reveal updated_log in
         let m = as_seq h0 m in
         invariant (Spec.MkState r acc log)
         /\ invariant (Spec.MkState r' acc' log')
         /\ Spec.MkState r acc' log' == Hacl.Spe.Poly1305_32.poly1305_blocks_spec (Spec.MkState r acc log) m len))
      ))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"
let rec poly1305_blocks log st m len =
  let h0 = ST.get() in
  if U64.(len =^ 0uL) then (
    lemma_poly1305_blocks_spec_0 (Spec.MkState (as_seq h0 P.(st.r)) (as_seq h0 P.(st.h)) (Ghost.reveal log)) (as_seq h0 m) len;
    log
  )
  else (
    lemma_poly1305_blocks_spec_1 (Spec.MkState (as_seq h0 P.(st.r)) (as_seq h0 P.(st.h)) (Ghost.reveal log)) (as_seq h0 m) len;
    cut (U64.v len >= 1);
    let block = Buffer.sub m 0ul 16ul in
    let tail  = Buffer.offset m 16ul in
    (* cut (let mm = as_seq h0 m in *)
    (*      let b = slice mm 0 16 in *)
    (*      let m' = slice mm 16 (length m) in *)
    (*     b == as_seq h0 block /\ m' == as_seq h0 tail); *)
    let new_log = P.poly1305_update log st block in
    (* let h1 = ST.get() in *)
    (* let acc   = MkState?.h st in *)
    (* let r     = MkState?.r st in *)
    (* cut (Ghost.reveal new_log == Seq.cons ((as_seq h0 block)) (Ghost.reveal log)); *)
    (* Math.Lemmas.modulo_lemma (seval (as_seq h0 r)) (prime); *)
    (* lemma_poly1305_blocks_spec_1 (as_seq h0 block) (Ghost.reveal log) (Ghost.reveal new_log) (Spec.selem (as_seq h0 acc)) (seval (as_seq h0 r)) (Spec.selem (as_seq h1 acc)); *)
    (* append_cons_snoc (Spec.Poly1305.encode_bytes ((as_seq h0 m))) (as_seq h0 block) (Ghost.reveal log); *)
    (* snoc_encode_bytes (as_seq h0 tail) (as_seq h0 block);     *)
    let len = U64.(len -^ 1uL) in
    poly1305_blocks new_log st tail len
  )


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val poly1305_partial:
  st:P.poly1305_state ->
  m:P.uint8_p ->
  len:U64.t{16 * U64.v len = length m} ->
  kr:P.uint8_p{length kr = 16} ->
  Stack P.log_t
    (requires (fun h -> P.(live_st h st /\ live h m /\ disjoint st.r m /\ disjoint st.h m /\ live h kr)))
    (ensures  (fun h0 updated_log h1 -> P.(modifies_2 st.h st.r h0 h1 /\ live_st h1 st /\ live_st h0 st /\ live h0 m
      /\ red_26 (as_seq h1 st.r) /\ red_y (as_seq h1 st.h)
      /\ live h0 kr /\ live h1 kr
      /\ (let r' = as_seq h1 st.r in
         let acc' = as_seq h1 st.h in
         let log' = Ghost.reveal updated_log in
         let m = as_seq h0 m in
         let k = as_seq h0 kr in
         invariant (Spec.MkState r' acc' log')
         /\ Spec.MkState r' acc' log' == Hacl.Spe.Poly1305_32.poly1305_partial m len k))
    ))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"
let poly1305_partial st input len kr =
  let init_log = P.poly1305_init_ st kr in
  let h0 = ST.get() in
  assert_norm(pow2 128 < pow2 130 - 5);
  poly_def_0 (Ghost.reveal init_log) (seval (as_seq h0 P.(st.r)));
  (* cut (invariant (Spec.MkState (as_seq h0 P.(st.r)) (as_seq h0 P.(st.h)) (Ghost.reveal log))); *)
  let partial_log = poly1305_blocks init_log st input len in
  (* cut (invariant partial_st); *)
  (* lemma_append_empty' (encode_bytes (Ghost.reveal_sbytes input)) (MkState?.log init_st); *)
  partial_log

#set-options "--max_fuel 0 --max_ifuel 0"
let sum_modifications (#a:Type) (b1:buffer a) (b2:buffer a) (h0 h1 h2:mem)
  : Lemma (requires (live h0 b1 /\
                     live h0 b2 /\
                     modifies_2 b1 b2 h0 h1 /\
                     modifies_1 b1 h1 h2))
          (ensures modifies_2 b1 b2 h0 h2)
  =
  lemma_reveal_modifies_2 b1 b2 h0 h1;
  lemma_reveal_modifies_1 b1 h1 h2;
  lemma_intro_modifies_2 b1 b2 h0 h2


#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 2 --z3rlimit 50"
val poly1305_complete:
  st:P.poly1305_state ->
  m:P.uint8_p ->
  len:U64.t{U64.v len = length m} ->
  k:P.uint8_p{length k = 32} ->
  Stack unit
    (requires (fun h -> P.(live_st h st /\ live h m /\ disjoint st.r m /\ disjoint st.h m /\ live h k)))
    (ensures  (fun h0 updated_log h1 -> P.(modifies_2 st.h st.r h0 h1 /\ live_st h1 st /\ live_st h0 st /\ live h0 m
      /\ red_26 (as_seq h1 st.r) /\ red_y (as_seq h1 st.h)
      /\ live h0 k
      /\ (let acc' = as_seq h1 st.h in
         let m = as_seq h0 m in
         let k = as_seq h0 k in
         acc' == poly1305_complete m len k)
  )
         (* bounds acc' p44 p44 p42 *)
         (* /\ acc == invariant (Spec.MkState r' acc' log') *)
         (* /\ Spec.MkState r' acc' log' == Hacl.Spe.Poly1305_32.poly1305_partial m len k)) *)
    ))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 226"
let poly1305_complete st m len k =
  let kr = Buffer.sub k 0ul 16ul in
  let len16 = U64.(len >>^  4ul) in
  let rem16 = U64.(len &^ 0xfuL) in
  assert_norm(pow2 4 = 16);
  UInt.logand_mask (U64.v len) 4;
  assert_norm(pow2 4 = 16);
  cut (U64.v len = 16 * U64.v len16 + U64.v rem16);
  Math.Lemmas.lemma_div_mod (U64.v len) 16;
  Math.Lemmas.modulo_lemma (16 * U64.v len16) (pow2 32);
  Math.Lemmas.modulo_lemma (U64.v len) (pow2 32);
  let part_input = Buffer.sub m 0ul (Int.Cast.uint64_to_uint32 (U64.(16uL *^ len16))) in
  let last_block = Buffer.sub m (Int.Cast.uint64_to_uint32 (U64.(16uL *^ len16))) (Int.Cast.uint64_to_uint32 rem16) in
  let h0 = ST.get () in
  lemma_disjoint_sub m part_input P.(st.r);
  lemma_disjoint_sub m part_input P.(st.h);
  let l = poly1305_partial st part_input len16 kr in
  let h1 = ST.get () in
  P.poly1305_update_last l st last_block rem16;
  let h2 = ST.get () in
  P.(sum_modifications st.h st.r h0 h1 h2)


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 50"

val crypto_onetimeauth_:
  output:P.uint8_p{length output = 16} ->
  input:P.uint8_p{disjoint input output} ->
  len:U64.t{U64.v len < pow2 32 /\ U64.v len = length input} ->
  k:P.uint8_p{length k = 32} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input /\ live h k))
    (ensures  (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1 /\ live h0 input /\ live h0 k
      /\ as_seq h1 output == Hacl.Spe.Poly1305_32.crypto_onetimeauth_spec (as_seq h0 input) len (as_seq h0 k)))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"
let crypto_onetimeauth_ output input len k =
  push_frame();
  (* let len16 = U64.(len >>^ 4ul) in *)
  (* let rem16 = U64.(len &^ 0xfuL) in *)
  (* let partial_input = Buffer.sub input 0ul U32.(16ul *^ Int.Cast.uint64_to_uint32 len16) in *)
  (* let last_block    = Buffer.sub input U32.(16ul *^ Int.Cast.uint64_to_uint32 len16) (Int.Cast.uint64_to_uint32 len) in *)
  let buf = create limb_zero U32.(clen +^ clen) in
  let r = sub buf 0ul clen in
  let h = sub buf clen clen in
  let st = P.mk_state r h in
  let key_r = Buffer.sub k 0ul 16ul in
  let key_s = Buffer.sub k 16ul 16ul in
  (* let init_log = poly1305_init_ st key_r in *)
  let partial_log = poly1305_complete st input len k in
  let final_log = P.poly1305_finish st output key_s in
  pop_frame()

open Hacl.Spec.Endianness

val crypto_onetimeauth:
  output:P.uint8_p{length output = 16} ->
  input:P.uint8_p{disjoint input output} ->
  len:U64.t{U64.v len = length input} ->
  k:P.uint8_p{length k = 32} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input /\ live h k))
    (ensures  (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1 /\ live h0 input /\ live h0 k
      /\ reveal_sbytes (as_seq h1 output) == Spec.Poly1305.poly1305 (reveal_sbytes (as_seq h0 input)) (reveal_sbytes (as_seq h0 k))))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"
let crypto_onetimeauth output input len k =
  crypto_onetimeauth_ output input len k
