module Hacl.AES_256_GCM.NI

open FStar.HyperStack
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.IntVector

open Hacl.AES_256.NI
open Hacl.Gf128.NI

module ST = FStar.HyperStack.ST


#set-options "--z3rlimit 50"
type aes_gcm_ctx = lbuffer (vec_t U128 1) 22ul


val aes256_gcm_init:
    ctx: aes_gcm_ctx
  -> key: lbuffer uint8 32ul
  -> nonce: lbuffer uint8 12ul ->
  Stack unit
  (requires (fun h -> live h ctx /\ live h key /\ live h nonce))
  (ensures (fun h0 _ h1 -> modifies1 ctx h0 h1))

let aes256_gcm_init ctx key nonce =
  push_frame();
  let gcm_key = create 16ul (u8 0) in
  let tag_mix = create 16ul (u8 0) in
  let nonce0 = create 12ul (u8 0) in
  let aes_ctx = sub ctx (size 0) (size 16) in
  let gcm_ctx = sub ctx (size 16) (size 5) in
  aes256_init aes_ctx key nonce0;
  aes256_key_block gcm_key aes_ctx (size 0);
  aes256_set_nonce aes_ctx nonce;
  aes256_key_block tag_mix aes_ctx (size 1);
  gcm_init gcm_ctx gcm_key;
  ctx.(21ul) <- vec_load_le U128 1 tag_mix;
  pop_frame()

#reset-options "--z3rlimit 500 --max_fuel 1"

val aes256_gcm_encrypt:
    ctx: aes_gcm_ctx
  -> len: size_t{v len + 16 <= max_size_t}
  -> out: lbuffer uint8 (len +. 16ul)
  -> text: lbuffer uint8 len
  -> aad_len: size_t
  -> aad: lbuffer uint8 aad_len ->
  Stack unit
  (requires (fun h -> live h out /\ live h text /\ live h aad /\ live h ctx
                 /\ disjoint out ctx
                 /\ disjoint out text
                 /\ disjoint out aad
                 /\ disjoint ctx text
                 /\ disjoint ctx aad))
  (ensures (fun h0 _ h1 -> modifies2 out ctx h0 h1))

let aes256_gcm_encrypt ctx len out text aad_len aad =
  push_frame();
  let cip = sub out (size 0) len in
  let aes_ctx = sub ctx (size 0) (size 16) in
  aes256_ctr len cip text aes_ctx (size 2);
  let gcm_ctx = sub ctx (size 16) (size 5) in
  let tag_mix = ctx.(21ul) in
  gcm_update_padded gcm_ctx aad_len aad;
  gcm_update_padded gcm_ctx len cip;
  let tmp = create 16ul (u8 0) in
  uint_to_bytes_be #U64 (sub tmp (size 0) (size 8)) (to_u64 (aad_len *. 8ul));
  uint_to_bytes_be #U64 (sub tmp (size 8) (size 8)) (to_u64 (len *. 8ul));
  gcm_update_blocks gcm_ctx (size 16) tmp;
  gcm_emit tmp gcm_ctx;
  let tmp_vec = vec_load_le U128 1 tmp in
  let tmp_vec = vec_xor tmp_vec tag_mix in
  vec_store_le (sub out len (size 16)) tmp_vec;
  pop_frame()


val aes256_gcm_decrypt:
    ctx: aes_gcm_ctx
  -> len: size_t{v len + 16 <= max_size_t}
  -> out: lbuffer uint8 len
  -> cipher: lbuffer uint8 (len +. 16ul)
  -> aad_len: size_t
  -> aad: lbuffer uint8 aad_len ->
  Stack bool
  (requires (fun h -> live h out /\ live h cipher /\ live h aad /\ live h ctx
                 /\ disjoint out ctx
                 /\ disjoint out cipher
                 /\ disjoint out aad
                 /\ disjoint ctx cipher
                 /\ disjoint ctx aad))
  (ensures (fun h0 r h1 -> modifies2 out ctx h0 h1))

let aes256_gcm_decrypt ctx len out cipher aad_len aad =
  push_frame();
  let scratch = create 18ul (u8 0) in
  let text = sub scratch 0ul 16ul in
  let zero = sub scratch 16ul 1ul in
  let result = sub scratch 17ul 1ul in
  let ciphertext = sub cipher 0ul len in
  let tag = sub cipher len (size 16) in
  let aes_ctx = sub ctx (size 0) (size 16) in
  let gcm_ctx = sub ctx (size 16) (size 5) in
  let tag_mix = ctx.(21ul) in
  let h1 = ST.get () in
  gcm_update_padded gcm_ctx aad_len aad;
  gcm_update_padded gcm_ctx len ciphertext;
  uint_to_bytes_be #U64 (sub text (size 0) (size 8)) (to_u64 (aad_len *. size 8));
  uint_to_bytes_be #U64 (sub text (size 8) (size 8)) (to_u64 (len *. size 8));
  gcm_update_blocks gcm_ctx (size 16) text;
  gcm_emit text gcm_ctx;
  let text_vec = vec_load_le U128 1 text in
  let text_vec = vec_xor text_vec tag_mix in
  vec_store_le text text_vec;
  let h7 = ST.get () in
  loop_nospec #h7 (size 16) result
    (fun i -> result.(0ul) <- result.(0ul) |. (text.(i) ^. tag.(i)));
  let h8 = ST.get () in
  assert(modifies2 ctx scratch h1 h8);
  let res8 = result.(0ul) in
  let r =
    if Lib.RawIntTypes.u8_to_UInt8 res8 = 0uy then (
      aes256_ctr len out ciphertext aes_ctx (size 2);
      true)
    else (
      let h9 = ST.get () in
      modifies2_is_modifies3 ctx scratch out h1 h9;
      assert(modifies3 out ctx scratch h1 h9);
      false)
  in
  pop_frame();
  r
