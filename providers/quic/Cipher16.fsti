module Cipher16

module G = FStar.Ghost
module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module HS = FStar.HyperStack

open FStar.HyperStack.ST
open EverCrypt.Helpers
open EverCrypt.Error

module AC = EverCrypt.AutoConfig2
module SC = EverCrypt.StaticConfig
module SC16 = Spec.Cipher16

type alg = SC16.alg
type state (a:alg) (k:G.erased (SC16.key a)) =
  b:IB.libuffer U8.t (SC16.slen a) (SC16.expand a (G.reveal k))

val create:
  a: alg ->
  key: B.lbuffer U8.t (SC16.keylen a) ->
  Stack (IB.ibuffer U8.t)
  (requires fun h0 -> B.live h0 key)
  (ensures fun h0 s h1 ->
    (if B.g_is_null s then
      B.modifies B.loc_none h0 h1
    else
      (B.modifies (B.loc_buffer s) h0 h1 /\
      B.live h1 s /\ IB.length s == SC16.slen a /\
      IB.witnessed s (fun s' -> s' == (SC16.expand a (B.as_seq h0 key))))))

val compute:
  #a: alg ->
  #k: G.erased (SC16.key a) ->
  st: state a k ->
  input: B.lbuffer U8.t 16 ->
  output: B.lbuffer U8.t 16 ->
  Stack unit
  (requires fun h0 ->
    B.live h0 input /\ B.live h0 output /\ B.live h0 st /\
    B.disjoint st input /\ B.disjoint st output /\
    B.disjoint input output)
  (ensures fun h0 _ h1 ->
    B.modifies (B.loc_buffer output) h0 h1 /\
    (let inb = B.as_seq h0 input in
    let outb = B.as_seq h1 output in
    outb == SC16.block a (G.reveal k) inb))

