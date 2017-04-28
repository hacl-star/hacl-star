module Crypto.AEAD.Main
open FStar.UInt32
open Crypto.AEAD
module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module I = Crypto.Indexing
module PRF = Crypto.Symmetric.PRF

let aead_state i rw = Invariant.aead_state i rw
let keylen i = PRF.keylen i
let statelen i = PRF.statelen i
let plain i l = Crypto.Plain.plain i l
let plainBuffer i l = Crypto.Plain.plainBuffer i l
let safelen (i:I.id) (n:nat) = Invariant.safelen i n (Invariant.otp_offset i)

let gen (i:I.id) (rgn:eternal_region)
  : ST (aead_state i I.Writer)
    (requires (fun h -> True))
    (ensures (fun _ _ _ -> True))
  = Crypto.AEAD.gen i rgn

let genReader
           (#i: I.id)
           (st: aead_state i I.Writer)
         : ST (aead_state i I.Reader)
  (requires (fun _ -> True))
  (ensures  (fun _ _ _ -> True))
  = Crypto.AEAD.genReader #i st

let coerce
         (i: I.id)
       (rgn: eternal_region)
       (key: lbuffer (v (keylen i)))
      : ST  (aead_state i I.Writer)
  (requires (fun h ->
             ~ (Flag.prf i) /\
             Buffer.live h key))
  (ensures  (fun h0 st h1 -> True))
  = Crypto.AEAD.coerce i rgn key

let leak
      (#i: I.id)
      (st: aead_state i I.Writer)
    : ST (lbuffer (v (statelen i)))
  (requires (fun _ -> ~(Flag.prf i)))
  (ensures  (fun _ _ _ -> True))
  = Crypto.AEAD.leak #i st

let encrypt
          (i: I.id)
         (st: aead_state i I.Writer)
          (n: iv (I.cipherAlg_of_id i))
     (aadlen: aadlen_32)
        (aad: lbuffer (v aadlen))
   (plainlen: ok_plain_len_32 i)
      (plain: plainBuffer i (v plainlen))
 (cipher_tag: lbuffer (v plainlen + v taglen))
            : ST unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
  = assume false;
    Crypto.AEAD.encrypt i st n aadlen aad plainlen plain cipher_tag

let decrypt
          (i: I.id)
         (st: aead_state i I.Reader)
          (n: iv (I.cipherAlg_of_id i))
     (aadlen: aadlen_32)
        (aad: lbuffer (v aadlen))
   (plainlen: ok_plain_len_32 i)
      (plain: plainBuffer i (v plainlen))
 (cipher_tag: lbuffer (v plainlen + v taglen))
            : ST bool
  (requires (fun h -> True))
  (ensures (fun h0 verified h1 -> True))
  = assume false;
    Crypto.AEAD.Decrypt.decrypt i st n aadlen aad plainlen plain cipher_tag
