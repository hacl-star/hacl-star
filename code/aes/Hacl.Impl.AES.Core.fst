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
  | MAES -> Hacl.Impl.AES.CoreNI.create_state()

inline_for_extraction noextract
let copy_state (#m:m_spec) (st:state m) (ost:state m) =
  match m with
  | MAES -> Hacl.Impl.AES.CoreNI.copy_state st ost

inline_for_extraction noextract
let load_block0 (#m:m_spec) (st:state m) (b:lbuffer uint8 16ul) =
  match m with
  | MAES -> Hacl.Impl.AES.CoreNI.load_block0 st b

inline_for_extraction noextract
let load_key1 (#m:m_spec) (k:key1 m) (b:lbuffer uint8 16ul) =
  match m with
  | MAES -> Hacl.Impl.AES.CoreNI.load_key1 k b

inline_for_extraction noextract
let load_nonce #m n b =
  match m with
  | MAES -> Hacl.Impl.AES.CoreNI.load_nonce n b

inline_for_extraction noextract
let load_state #m st n counter =
  match m with
  | MAES -> Hacl.Impl.AES.CoreNI.load_state st n counter

inline_for_extraction noextract
let store_block0 #m out st =
  match m with
  | MAES -> Hacl.Impl.AES.CoreNI.store_block0 out st

inline_for_extraction noextract
let xor_state_key1 #m st key =
  match m with
  | MAES -> Hacl.Impl.AES.CoreNI.xor_state_key1 st key

inline_for_extraction noextract
let xor_block #m out st b =
  match m with
  | MAES -> Hacl.Impl.AES.CoreNI.xor_block out st b

inline_for_extraction noextract
let aes_enc #m st key =
  match m with
  | MAES -> Hacl.Impl.AES.CoreNI.aes_enc st key

inline_for_extraction noextract
let aes_enc_last #m st key =
  match m with
  | MAES -> Hacl.Impl.AES.CoreNI.aes_enc_last st key

inline_for_extraction noextract
let aes_keygen_assist0 #m n p rcon =
  match m with
  | MAES -> Hacl.Impl.AES.CoreNI.aes_keygen_assist0 n p rcon

inline_for_extraction noextract
let aes_keygen_assist1 #m n p =
  match m with
  | MAES -> Hacl.Impl.AES.CoreNI.aes_keygen_assist1 n p

inline_for_extraction noextract
let key_expansion_step #m n p =
  match m with
  | MAES -> Hacl.Impl.AES.CoreNI.key_expansion_step n p

