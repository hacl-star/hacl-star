module Hacl.HKDF_SHA2_256

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.LoopCombinators

module ST = FStar.HyperStack.ST
module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators

module SpecSHA2 = Spec.SHA2
module SpecHash = Spec.Hash
module SpecHMAC = Spec.HMAC

module Hash = Hacl.Hash.Definitions
module HMAC = Hacl.HMAC


module Impl = Hacl.Impl.HKDF_SHA2_256


let hkdf_extract output salt slen ikm ilen = Impl.hkdf_extract output salt slen ikm ilen

let hkdf_expand output prk plen info ilen len = Impl.hkdf_expand output prk plen info ilen len

let hkdf_build_label output secret label llen context clen len =
  Impl.hkdf_build_label output secret label llen context clen len

let hkdf_expand_label output secret label llen context clen len =
  Impl.hkdf_expand_label output secret label llen context clen len
