module Hacl.Impl.ECDSA.Setup

open Lib.IntTypes
open Lib.ByteSequence

open FStar.Math.Lemmas
open FStar.Math.Lib

open FStar.HyperStack
open FStar.HyperStack.All
open Lib.Sequence
open Lib.Buffer
open FStar.Mul

open Spec.ECC
open Spec.ECC.Curves

open Hacl.Spec.EC.Definition

open Hacl.Impl.EC.Setup


#set-options "--z3rlimit 100"

inline_for_extraction noextract
let p256_order_inverse_list: x: list uint8 {List.Tot.length x == v (getScalarLenBytes P256) /\ 
  lst_as_nat x == getOrder #P256 - 2} = 
  [@inline_let]
  let x = [
      u8 79;  u8 37;  u8 99;  u8 252; u8 194; u8 202; u8 185; u8 243;
      u8 132; u8 158; u8 23;  u8 167; u8 173; u8 250; u8 230; u8 188;
      u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255;
      u8 0;   u8 0;   u8 0;   u8 0;   u8 255; u8 255; u8 255; u8 255] in 
    assert_norm (List.Tot.length x == v (getScalarLenBytes P256));
    admit();
    x

inline_for_extraction noextract
let p384_order_inverse_list: x: list uint8 {List.Tot.length x == v (getScalarLenBytes P384) /\ 
  lst_as_nat x == getOrder #P384 - 2} = 
  [@inline_let]
  let x = [ 
    u8 113; u8 41;  u8 197; u8 204; u8 106; u8 25;  u8 236; u8 236;
    u8 122; u8 167; u8 176; u8 72;  u8 178; u8 13;  u8 26;  u8 88;
    u8 223; u8 45;  u8 55;  u8 244; u8 129; u8 77;  u8 99;  u8 199;
    u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255;
    u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255;
    u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255] in 
  assert_norm (List.Tot.length x == v (getScalarLenBytes P384));
  admit(); 
  x


inline_for_extraction
let order_inverse_list (c: curve): x: list uint8 {List.Tot.length x == v (getScalarLenBytes c) /\
  lst_as_nat x == getOrder #c - 2} = 
  match c with 
  |P256 -> p256_order_inverse_list
  |P384 -> p384_order_inverse_list



let prime256order_buffer: x: glbuffer uint8 32ul {witnessed #uint8 #(size 32) x (Lib.Sequence.of_list (order_inverse_list P256)) /\ recallable x} = 
  createL_global (p256_order_inverse_list)

inline_for_extraction
let prime384order_buffer: x: glbuffer uint8 48ul {witnessed #uint8 #(size 48) x (Lib.Sequence.of_list (order_inverse_list P384)) /\ recallable x} = 
  createL_global (p384_order_inverse_list)

inline_for_extraction noextract
let order_inverse_buffer (#c: curve): x: glbuffer uint8 (getCoordinateLenU c) {
  witnessed #uint8 #(getCoordinateLenU c) x (Lib.Sequence.of_list (order_inverse_list c)) /\ recallable x} = 
  match c with 
  |P256 -> prime256order_buffer
  |P384 -> prime384order_buffer
