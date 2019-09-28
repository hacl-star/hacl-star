module Spec.QTesla.CShake

open Lib.IntTypes
open Lib.ByteSequence
open Lib.RawIntTypes

open Spec.SHA3

// qTESLA's spec uses natural numbers that it increments as nonces for
// cSHAKE, but the implementation takes uint16s. Instead of junking the
// spec up with statements about the nonces staying within the range of
// a uint16, we encapulsate it here.
val cshake128_qtesla:
    input_len:size_nat
  -> input:lbytes input_len
  -> nonce:nat
  -> output_len:size_nat
  -> lbytes output_len
let cshake128_qtesla input_len input nonce output_len =
  assume(nonce < maxint U16);
  let cstm = u16 nonce in
  cshake128_frodo input_len input cstm output_len

val cshake256_qtesla:
    input_len:size_nat
  -> input:lbytes input_len
  -> nonce:nat
  -> output_len:size_nat
  -> lbytes output_len
let cshake256_qtesla input_len input nonce output_len =
  assume(nonce < maxint U16);
  let cstm = u16 nonce in
  cshake256_frodo input_len input cstm output_len

