module Hacl.K256.ECDSA

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

module S = Spec.K256
module SK = Hacl.Impl.K256.Sign
module VK = Hacl.Impl.K256.Verify

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

[@CInline]
let ecdsa_sign_hashed_msg r s m private_key k =
  SK.ecdsa_sign_hashed_msg r s m private_key k


[@CInline]
let ecdsa_verify_hashed_msg m public_key_x public_key_y r s =
  VK.ecdsa_verify_hashed_msg m public_key_x public_key_y r s


[@CInline]
let ecdsa_sign_sha256 r s msg_len msg private_key k =
  push_frame ();
  let mHash = create 32ul (u8 0) in
  Hacl.Hash.SHA2.hash_256 msg msg_len mHash;
  let b = ecdsa_sign_hashed_msg r s mHash private_key k in
  pop_frame ();
  b


[@CInline]
let ecdsa_verify_sha256 msg_len msg public_key_x public_key_y r s =
  push_frame ();
  let mHash = create 32ul (u8 0) in
  Hacl.Hash.SHA2.hash_256 msg msg_len mHash;
  let b = ecdsa_verify_hashed_msg mHash public_key_x public_key_y r s in
  pop_frame ();
  b
