module Hacl.Impl.AES.Core

open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Lib.IntVector

open Hacl.AES.Common

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence


#set-options "--z3rlimit 50"


inline_for_extraction noextract
let create_state (#m:m_spec) =
  match m with
  | M32 -> Hacl.Impl.AES.CoreBitSlice.create_state()
  | MAES -> Hacl.Impl.AES.CoreNI.create_state()

inline_for_extraction noextract
let copy_state (#m:m_spec) (st:state m) (ost:state m) =
  match m with
  | MAES -> Hacl.Impl.AES.CoreNI.copy_state st ost
  | M32 -> let h0 = ST.get() in Hacl.Impl.AES.CoreBitSlice.copy_state st ost; let h1 = ST.get() in assume (as_seq h1 st == as_seq h0 ost)

inline_for_extraction noextract
let load_block0 (#m:m_spec) (st:state m) (b:lbuffer uint8 16ul) =
  match m with
  | MAES -> Hacl.Impl.AES.CoreNI.load_block0 st b
  | M32 -> let h0 = ST.get() in Hacl.Impl.AES.CoreBitSlice.load_block0 st b; let h1 = ST.get() in assume (let st' = as_seq h0 st in let st'' = as_seq h1 st in
      u8_16_to_le (state_to_bytes m st'' 0) == as_seq h0 b /\
      state_to_bytes m st'' 1 == state_to_bytes m st' 1 /\
      state_to_bytes m st'' 2 == state_to_bytes m st' 2 /\
      state_to_bytes m st'' 3 == state_to_bytes m st' 3)

inline_for_extraction noextract
let load_key1 (#m:m_spec) (k:key1 m) (b:lbuffer uint8 16ul) =
  match m with
  | MAES -> Hacl.Impl.AES.CoreNI.load_key1 k b
  | M32 -> let h0 = ST.get() in Hacl.Impl.AES.CoreBitSlice.load_key1 k b; let h1 = ST.get() in assume (u8_16_to_le (key_to_bytes m (as_seq h1 k)) == as_seq h0 b)

inline_for_extraction noextract
let load_nonce #m n b =
  match m with
  | MAES -> Hacl.Impl.AES.CoreNI.load_nonce n b
  | M32 -> let h0 = ST.get() in Hacl.Impl.AES.CoreBitSlice.load_nonce n b; let h1 = ST.get() in assume (u8_16_to_le (nonce_to_bytes m (as_seq h1 n)) == 
      LSeq.update_sub (LSeq.create 16 (u8 0)) 0 12 (as_seq h0 b))

inline_for_extraction noextract
let load_state #m st n counter =
  match m with
  | MAES -> Hacl.Impl.AES.CoreNI.load_state st n counter
  | M32 -> let h0 = ST.get() in Hacl.Impl.AES.CoreBitSlice.load_state st n counter; let h1 = ST.get() in assume (let nonce0 = nonce_to_bytes m (as_seq h0 n) in
      state_to_bytes m (as_seq h1 st) 0 ==
        Spec.AES.aes_ctr32_set_counter_LE nonce0 counter /\
      state_to_bytes m (as_seq h1 st) 1 ==
        Spec.AES.aes_ctr32_set_counter_LE nonce0 (counter +. u32 1) /\
      state_to_bytes m (as_seq h1 st) 2 ==
        Spec.AES.aes_ctr32_set_counter_LE nonce0 (counter +. u32 2) /\
      state_to_bytes m (as_seq h1 st) 3 ==
        Spec.AES.aes_ctr32_set_counter_LE nonce0 (counter +. u32 3))

inline_for_extraction noextract
let store_block0 #m out st =
  match m with
  | MAES -> Hacl.Impl.AES.CoreNI.store_block0 out st
  | M32 -> let h0 = ST.get() in Hacl.Impl.AES.CoreBitSlice.store_block0 out st; let h1 = ST.get() in assume (as_seq h1 out == u8_16_to_le (state_to_bytes m (as_seq h0 st) 0))


inline_for_extraction noextract
let xor_state_key1 #m st key =
  match m with
  | MAES -> Hacl.Impl.AES.CoreNI.xor_state_key1 st key
  | M32 -> let h0 = ST.get() in Hacl.Impl.AES.CoreBitSlice.xor_state_key1 st key; let h1 = ST.get() in assume (let st' = as_seq h0 st in
      let st'' = as_seq h1 st in
      let k = key_to_bytes m (as_seq h0 key) in
    state_to_bytes m st'' 0 == LSeq.map2 ( ^. ) (state_to_bytes m st' 0) k /\
    state_to_bytes m st'' 1 == LSeq.map2 ( ^. ) (state_to_bytes m st' 1) k /\
    state_to_bytes m st'' 2 == LSeq.map2 ( ^. ) (state_to_bytes m st' 2) k /\
    state_to_bytes m st'' 3 == LSeq.map2 ( ^. ) (state_to_bytes m st' 3) k)

inline_for_extraction noextract
let xor_block #m out st b =
  match m with
  | MAES -> Hacl.Impl.AES.CoreNI.xor_block out st b
  | M32 -> let h0 = ST.get() in Hacl.Impl.AES.CoreBitSlice.xor_block out st b; let h1 = ST.get() in assume (let b' = as_seq h0 b in
      let out' = as_seq h1 out in
      let st' = as_seq h0 st in
      LSeq.sub out' 0 16 == u8_16_to_le (LSeq.map2 ( ^. )
        (u8_16_to_le (LSeq.sub b' 0 16)) (state_to_bytes m st' 0)) /\
      LSeq.sub out' 16 16 == u8_16_to_le (LSeq.map2 ( ^. )
        (u8_16_to_le (LSeq.sub b' 16 16)) (state_to_bytes m st' 1)) /\
      LSeq.sub out' 32 16 == u8_16_to_le (LSeq.map2 ( ^. )
        (u8_16_to_le (LSeq.sub b' 32 16)) (state_to_bytes m st' 2)) /\
      LSeq.sub out' 48 16 == u8_16_to_le (LSeq.map2 ( ^. )
        (u8_16_to_le (LSeq.sub b' 48 16)) (state_to_bytes m st' 3)))

inline_for_extraction noextract
let aes_enc #m st key =
  match m with
  | MAES -> Hacl.Impl.AES.CoreNI.aes_enc st key
  | M32 -> let h0 = ST.get() in Hacl.Impl.AES.CoreBitSlice.aes_enc st key; let h1 = ST.get() in assume (let st' = as_seq h0 st in
      let st'' = as_seq h1 st in
      let k = key_to_bytes m (as_seq h0 key) in
    state_to_bytes m st'' 0 == Spec.AES.aes_enc k (state_to_bytes m st' 0) /\
    state_to_bytes m st'' 1 == Spec.AES.aes_enc k (state_to_bytes m st' 1) /\
    state_to_bytes m st'' 2 == Spec.AES.aes_enc k (state_to_bytes m st' 2) /\
    state_to_bytes m st'' 3 == Spec.AES.aes_enc k (state_to_bytes m st' 3))

inline_for_extraction noextract
let aes_enc_last #m st key =
  match m with
  | MAES -> Hacl.Impl.AES.CoreNI.aes_enc_last st key
  | M32 -> let h0 = ST.get() in Hacl.Impl.AES.CoreBitSlice.aes_enc_last st key; let h1 = ST.get() in assume (let st' = as_seq h0 st in
      let st'' = as_seq h1 st in
      let k = key_to_bytes m (as_seq h0 key) in
    state_to_bytes m st'' 0 == Spec.AES.aes_enc_last k (state_to_bytes m st' 0) /\
    state_to_bytes m st'' 1 == Spec.AES.aes_enc_last k (state_to_bytes m st' 1) /\
    state_to_bytes m st'' 2 == Spec.AES.aes_enc_last k (state_to_bytes m st' 2) /\
    state_to_bytes m st'' 3 == Spec.AES.aes_enc_last k (state_to_bytes m st' 3))

inline_for_extraction noextract
let aes_keygen_assist0 #m n p rcon =
  match m with
  | MAES -> Hacl.Impl.AES.CoreNI.aes_keygen_assist0 n p rcon
  | M32 -> let h0 = ST.get() in Hacl.Impl.AES.CoreBitSlice.aes_keygen_assist0 n p rcon; let h1 = ST.get() in assume (key_to_bytes m (as_seq h1 n) == Spec.AES.keygen_assist0 rcon (key_to_bytes m (as_seq h0 p)))

inline_for_extraction noextract
let aes_keygen_assist1 #m n p =
  match m with
  | MAES -> Hacl.Impl.AES.CoreNI.aes_keygen_assist1 n p
  | M32 -> let h0 = ST.get() in Hacl.Impl.AES.CoreBitSlice.aes_keygen_assist1 n p; let h1 = ST.get() in assume (key_to_bytes m (as_seq h1 n) == Spec.AES.keygen_assist1 (key_to_bytes m (as_seq h0 p)))

inline_for_extraction noextract
let key_expansion_step #m n p =
  match m with
  | MAES -> Hacl.Impl.AES.CoreNI.key_expansion_step n p
  | M32 -> let h0 = ST.get() in Hacl.Impl.AES.CoreBitSlice.key_expansion_step n p; let h1 = ST.get() in assume (let p = key_to_bytes m (as_seq h0 p) in
    let n1 = key_to_bytes m (as_seq h0 n) in
    key_to_bytes m (as_seq h1 n) == Spec.AES.key_expansion_step_LE p n1)

