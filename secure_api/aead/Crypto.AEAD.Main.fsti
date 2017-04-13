module Crypto.AEAD.Main
open FStar.UInt32
module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module I = Crypto.Indexing

(* Several constants that the interface relies on *)
type eternal_region =
     rgn:HH.rid {HS.is_eternal_region rgn}

type lbuffer (l:nat) =
     b:Buffer.buffer UInt8.t {Buffer.length b == l}

let ivlen (a:I.cipherAlg) =
    12ul

let taglen =
    16ul

let iv (alg:I.cipherAlg) =
     let open FStar.Mul in
     n:UInt128.t { UInt128.v n < pow2 (8 * v (ivlen alg)) }

let aadmax =
    assert_norm (2000 <= pow2 32 - 1);
    2000ul // more than enough for TLS

type aadlen_32 =
     l:UInt32.t {l <=^ aadmax}

(* Specification functions, currently all abstract
   Although properties about them should be carefully revealed *)
val aead_state  : I.id -> I.rw -> Type0
val keylen      : I.id -> UInt32.t
val statelen    : I.id -> UInt32.t
val plain       : I.id -> nat -> Type0
val plainBuffer : I.id -> nat -> Type0
val safelen     : I.id -> nat -> bool //Leaving this abstract for now; but it should imply Crypto.AEAD.Invariant.safelen i len (otp_offset i)

let ok_plain_len_32 (i:I.id) = l:UInt32.t{safelen i (v l)}

(*** The main stateful API ***)
//still heavily underspecified in this interface
val gen (i:I.id) (rgn:eternal_region)
  : ST (aead_state i I.Writer)
    (requires (fun h -> True))
    (ensures (fun _ _ _ -> True))

val genReader
           (#i: I.id)
           (st: aead_state i I.Writer)
         : ST (aead_state i I.Reader)
  (requires (fun _ -> True))
  (ensures  (fun _ _ _ -> True))

val coerce
         (i: I.id)
       (rgn: eternal_region)
       (key: lbuffer (v (keylen i)))
      : ST  (aead_state i I.Writer)
  (requires (fun h ->
             ~ (Flag.prf i) /\
             Buffer.live h key))
  (ensures  (fun h0 st h1 -> True))

val leak
      (#i: I.id)
      (st: aead_state i I.Writer)
    : ST (lbuffer (v (statelen i)))
  (requires (fun _ -> ~(Flag.prf i)))
  (ensures  (fun _ _ _ -> True))

val encrypt
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

val decrypt
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
