module EverCrypt.AEAD

module S = FStar.Seq
module G = FStar.Ghost

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer

open FStar.HyperStack.ST
open FStar.Integers

open Spec.AEAD

noextract
let bytes = Seq.seq UInt8.t

let supported_alg =
  a:alg { supported_alg a }

let frozen_preorder (s: bytes): MB.srel UInt8.t = fun (s1 s2: bytes) ->
  S.equal s1 s ==> S.equal s2 s

noeq
type expanded_key (a: alg) =
| EK:
    kv:G.erased (kv a) -> ek:(
    let s = expand (G.reveal kv) in
    let p = frozen_preorder s in
    ek:MB.mbuffer UInt8.t p p { MB.witnessed ek (S.equal s) }) ->
    expanded_key a

val expand_in:
  #a:supported_alg ->
  r:HS.rid ->
  k:B.buffer UInt8.t { B.length k = key_length a } ->
  ST (expanded_key a)
    (requires fun h0 ->
      B.live h0 k)
    (ensures fun h0 ek h1 ->
      let l = B.loc_buffer (EK?.ek ek) in
      Hash.fresh_loc l h0 h1 /\
      B.(modifies loc_none h0 h1) /\
      B.(loc_includes (loc_region_only true r) l) /\
      S.equal (G.reveal (EK?.kv ek)) (B.as_seq h0 k))

let iv_p a = iv:B.buffer UInt8.t { B.length iv = iv_length a }
let ad_p a = ad:B.buffer UInt8.t { B.length ad <= max_length a }
let plain_p a = p:B.buffer UInt8.t { B.length p <= max_length a }

val encrypt:
  #a:supported_alg ->
  ek:expanded_key a ->
  iv:iv_p a ->
  ad:ad_p a ->
  ad_len: UInt32.t { v ad_len = B.length ad } ->
  plain: plain_p a ->
  plain_len: UInt32.t { v plain_len = B.length plain } ->
  dst: B.buffer UInt8.t { B.length dst = B.length plain + tag_length a } ->
  Stack unit
    (requires fun h0 ->
      B.live h0 (EK?.ek ek) /\
      B.live h0 iv /\
      B.live h0 ad /\
      B.live h0 plain /\
      B.live h0 dst)
    (ensures fun h0 _ h1 ->
      B.(modifies (loc_buffer dst) h0 h1) /\
      S.equal (B.as_seq h1 dst)
        (encrypt (G.reveal (EK?.kv ek)) (B.as_seq h0 iv) (B.as_seq h0 ad) (B.as_seq h0 plain)))
