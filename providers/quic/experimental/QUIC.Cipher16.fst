module Cipher16

module G = FStar.Ghost
module B = LowStar.Buffer
module U8 = FStar.UInt8
module U32 = FStar.UInt32

open FStar.HyperStack.ST
open EverCrypt.Helpers
open EverCrypt.Error

module AC = EverCrypt.AutoConfig2
module SC = EverCrypt.StaticConfig
module SC16 = Spec.Cipher16

// FIXME: integrate GCTR in Spec.Cipher16 and here
#set-options "--admit_smt_queries true"



val block:
  a:SC16.alg ->
  key: B.lbuffer U8.t (SC16.keylen a) ->
  input: B.lbuffer U8.t 16 ->
  output: B.lbuffer U8.t 16 ->
  Stack unit
  (requires fun h0 ->
    B.live h0 input /\ B.live h0 output /\
    B.disjoint input output /\
    B.disjoint key input /\
    B.disjoint key output)
  (ensures fun h0 _ h1 ->
    B.modifies (B.loc_buffer output) h0 h1 /\
    (let kb = B.as_seq h0 key in
    let inb = B.as_seq h0 input in
    let outb = B.as_seq h1 output in
    outb == SC16.block a kb inb))

