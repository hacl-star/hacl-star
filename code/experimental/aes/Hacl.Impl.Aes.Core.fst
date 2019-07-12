module Hacl.Impl.Aes.Core

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Lib.Vec128

inline_for_extraction
let create_state (#m:m_spec) = 
  match m with
  | M32 -> Hacl.Impl.Aes.CoreBitSlice.create_state() 
  | MAES -> Hacl.Impl.Aes.CoreNI.create_state() 

inline_for_extraction
let copy_state (#m:m_spec) (st:state m) (ost:state m) = 
  match m with
  | MAES -> Hacl.Impl.Aes.CoreNI.copy_state st ost
  | M32 -> Hacl.Impl.Aes.CoreBitSlice.copy_state st ost

inline_for_extraction
let load_block0 (#m:m_spec) (st:state m) (b:lbuffer uint8 16ul) = 
  match m with
  | MAES -> Hacl.Impl.Aes.CoreNI.load_block0 st b
  | M32 -> Hacl.Impl.Aes.CoreBitSlice.load_block0 st b

inline_for_extraction
let load_key1 (#m:m_spec) (k:key1 m) (b:lbuffer uint8 16ul) = 
  match m with
  | MAES -> Hacl.Impl.Aes.CoreNI.load_key1 k b
  | M32 -> Hacl.Impl.Aes.CoreBitSlice.load_key1 k b

inline_for_extraction
let load_nonce #m n b = 
  match m with
  | MAES -> Hacl.Impl.Aes.CoreNI.load_nonce n b
  | M32 -> Hacl.Impl.Aes.CoreBitSlice.load_nonce n b

inline_for_extraction
let load_state #m st n counter = 
  match m with
  | MAES -> Hacl.Impl.Aes.CoreNI.load_state st n counter
  | M32 -> Hacl.Impl.Aes.CoreBitSlice.load_state st n counter

inline_for_extraction
let store_block0 #m out st = 
  match m with
  | MAES -> Hacl.Impl.Aes.CoreNI.store_block0 out st
  | M32 -> Hacl.Impl.Aes.CoreBitSlice.store_block0 out st


inline_for_extraction
let xor_state_key1 #m st key = 
  match m with
  | MAES -> Hacl.Impl.Aes.CoreNI.xor_state_key1 st key
  | M32 -> Hacl.Impl.Aes.CoreBitSlice.xor_state_key1 st key

inline_for_extraction
let xor_block #m out st b = 
  match m with
  | MAES -> Hacl.Impl.Aes.CoreNI.xor_block out st b
  | M32 -> Hacl.Impl.Aes.CoreBitSlice.xor_block out st b

inline_for_extraction
let aes_enc #m st key = 
  match m with
  | MAES -> Hacl.Impl.Aes.CoreNI.aes_enc st key
  | M32 -> Hacl.Impl.Aes.CoreBitSlice.aes_enc st key

inline_for_extraction
let aes_enc_last #m st key = 
  match m with
  | MAES -> Hacl.Impl.Aes.CoreNI.aes_enc_last st key
  | M32 -> Hacl.Impl.Aes.CoreBitSlice.aes_enc_last st key

inline_for_extraction
let aes_keygen_assist #m n p rcon = 
  match m with
  | MAES -> Hacl.Impl.Aes.CoreNI.aes_keygen_assist n p rcon
  | M32 -> Hacl.Impl.Aes.CoreBitSlice.aes_keygen_assist n p rcon

inline_for_extraction
let key_expansion_step #m n p = 
  match m with
  | MAES -> Hacl.Impl.Aes.CoreNI.key_expansion_step n p
  | M32 -> Hacl.Impl.Aes.CoreBitSlice.key_expansion_step n p

inline_for_extraction
let key_expansion_step2 #m n p = 
  match m with
  | MAES -> Hacl.Impl.Aes.CoreNI.key_expansion_step n p
  | M32 -> Hacl.Impl.Aes.CoreBitSlice.key_expansion_step n p





