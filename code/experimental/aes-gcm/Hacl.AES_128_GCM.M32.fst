module Hacl.AES_128_GCM.M32
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.AES_128.BitSlice
open Hacl.Gf128.PreComp

module ST = FStar.HyperStack.ST


#set-options "--z3rlimit 500"

let aes_gcm_ctx_len = 396ul

type aes_gcm_ctx = lbuffer uint64 aes_gcm_ctx_len


val aes128_gcm_init:
    ctx: aes_gcm_ctx
  -> key: lbuffer uint8 16ul
  -> nonce: lbuffer uint8 12ul ->
  Stack unit
  (requires (fun h -> live h ctx /\ live h key /\ live h nonce))
  (ensures (fun h0 _ h1 -> modifies1 ctx h0 h1))

let aes128_gcm_init ctx key nonce =
  push_frame();
  let gcm_key = create 16ul (u8 0) in
  let tag_mix = create 16ul (u8 0) in
  let nonce0 = create 12ul (u8 0) in
  let aes_ctx = sub ctx (size 0) (size 128) in
  let gcm_ctx = sub ctx (size 128) (size 266) in
  aes128_init aes_ctx key nonce0;
  aes128_key_block gcm_key aes_ctx (size 0);
  aes128_set_nonce aes_ctx nonce;
  aes128_key_block tag_mix aes_ctx (size 1);
  gcm_init gcm_ctx gcm_key;
  ctx.(394ul) <- uint_from_bytes_le #U64 (sub tag_mix 0ul 8ul);
  ctx.(395ul) <- uint_from_bytes_le #U64 (sub tag_mix 8ul 8ul);
  pop_frame()


val aes128_gcm_encrypt:
    ctx: aes_gcm_ctx
  -> len: size_t{v len + 16 <= max_size_t}
  -> out: lbuffer uint8 (len +. 16ul)
  -> text: lbuffer uint8 len
  -> aad_len: size_t
  -> aad: lbuffer uint8 aad_len ->
  Stack unit
  (requires (fun h -> live h out /\ live h text /\ live h aad /\ live h ctx
                 /\ disjoint out ctx
                 /\ disjoint ctx text
                 /\ disjoint ctx aad
                 /\ disjoint out text
                 /\ disjoint out aad))
  (ensures (fun h0 _ h1 -> modifies2 out ctx h0 h1))

let aes128_gcm_encrypt ctx len out text aad_len aad =
  push_frame();
  let tmp = create 16ul (u8 0) in
  let cip = sub out (size 0) len in
  let aes_ctx = sub ctx (size 0) (size 128) in
  let gcm_ctx = sub ctx (size 128) (size 266) in
  let tag_mix = sub ctx (size 394) (size 2) in
  aes128_ctr len cip text aes_ctx (size 2);
  gcm_update_blocks_padded gcm_ctx aad_len aad;
  gcm_update_blocks_padded gcm_ctx len cip;
  uint_to_bytes_be #U64 (sub tmp (size 0) (size 8)) (to_u64 (aad_len *. 8ul));
  uint_to_bytes_be #U64 (sub tmp (size 8) (size 8)) (to_u64 (len *. 8ul));
  gcm_update_blocks gcm_ctx (size 16) tmp;
  gcm_emit tmp gcm_ctx;
  let tmp0 = uint_from_bytes_le #U64 (sub tmp 0ul 8ul) in
  let tmp1 = uint_from_bytes_le #U64 (sub tmp 8ul 8ul) in
  let tmp0 = tmp0 ^. tag_mix.(0ul) in
  let tmp1 = tmp1 ^. tag_mix.(1ul) in
  uint_to_bytes_le #U64 (sub out len 8ul) tmp0;
  uint_to_bytes_le #U64 (sub out (len +. 8ul) 8ul) tmp1;
  pop_frame()


val aes128_gcm_decrypt:
    ctx: aes_gcm_ctx
  -> len: size_t{v len + 16 <= max_size_t}
  -> out: lbuffer uint8 len
  -> cipher: lbuffer uint8 (len +. 16ul)
  -> aad_len: size_t
  -> aad: lbuffer uint8 aad_len ->
  Stack bool
  (requires (fun h -> live h out /\ live h cipher /\ live h aad /\ live h ctx
                 /\ disjoint out ctx
                 /\ disjoint ctx cipher
                 /\ disjoint ctx aad
                 /\ disjoint out cipher
                 /\ disjoint out aad))
  (ensures (fun h0 r h1 -> modifies1 out h0 h1))

#reset-options "--z3rlimit 500 --max_fuel 1"

let aes128_gcm_decrypt ctx len out cipher aad_len aad =
  push_frame();
  let scratch = create 16ul (u8 0) in
  let ciphertext = sub cipher 0ul len in
  let aes_ctx = sub ctx (size 0) (size 128) in
  let gcm_ctx = sub ctx (size 128) (size 266) in
  let tag_mix = sub ctx (size 394) (size 2) in
  gcm_update_blocks_padded gcm_ctx aad_len aad;
  gcm_update_blocks_padded gcm_ctx len ciphertext;
  uint_to_bytes_be #U64 (sub scratch (size 0) (size 8)) (to_u64 (aad_len *. size 8));
  uint_to_bytes_be #U64 (sub scratch (size 8) (size 8)) (to_u64 (len *. size 8));
  gcm_update_blocks gcm_ctx (size 16) scratch;
  gcm_emit scratch gcm_ctx;
  let scratch0 = uint_from_bytes_le #U64 (sub scratch 0ul 8ul) in
  let scratch1 = uint_from_bytes_le #U64 (sub scratch 8ul 8ul) in
  let scratch0 = scratch0 ^. tag_mix.(0ul) in
  let scratch1 = scratch1 ^. tag_mix.(1ul) in
  uint_to_bytes_le #U64 (sub scratch 0ul 8ul) scratch0;
  uint_to_bytes_le #U64 (sub scratch 8ul 8ul) scratch1;
  let tag = sub cipher len (size 16) in
  let res = create 1ul (u8 0) in
  let h1 = ST.get() in
  loop_nospec #h1 (size 16) res
    (fun i -> res.(0ul) <- res.(0ul) |. (scratch.(i) ^. tag.(i)));
  let r = res.(size 0) in
  admit();
  if Lib.RawIntTypes.u8_to_UInt8 r = 0uy then (
    let cip = sub cipher (size 0) len in
    aes128_ctr len out cip aes_ctx (size 2);
    pop_frame();
    true)
  else (
    pop_frame();
    false)
