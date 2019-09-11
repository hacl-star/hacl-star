module Impl.Kyber2.Indcpa

open FStar.Mul
open FStar.IO

open Spec.Kyber2.Params
open Spec.Powtwo.Lemmas
open Lib.Poly
open Lib.Poly.NTT2
open Lib.NumericTypes

open Lib.Arithmetic.Group
open Lib.Arithmetic.Ring
open Lib.Arithmetic.Sums
open Spec.Kyber2.Group
open Spec.Kyber2.Ring

open Lib.Sequence
open Lib.ByteSequence
open Lib.IntTypes
open Lib.NumericTypes

open Lib.ModularArithmetic
open Lib.ModularArithmetic.Lemmas

open Spec.Kyber2.FunctionInstantiation
open Spec.Kyber2.CBD
open Spec.Kyber2.Poly

open Impl.Kyber2.NumericTypes.MontgomeryInt16

open FStar.Math.Lemmas

module Seq = Lib.Sequence
module Buf = Lib.Buffer

let pklen:size_t = size Spec.Kyber2.Indcpa.pklen
let sklen:size_t = size Spec.Kyber2.Indcpa.sklen
let ulen = size Spec.Kyber2.Indcpa.ulen
let vlen = size Spec.Kyber2.Indcpa.vlen
let ciphertextlen:size_t = size Spec.Kyber2.Indcpa.ciphertextlen

val encode:
  l:size_t{(v l)*params_n <= max_size_t}
  -> x:poly
  -> e:lbuffer uint8 (l*! ((size params_n) >>. 3))
  -> Stack unit
    (requires fun h -> live h x /\ live h e /\ Buf.disjoint x e)
    (ensures fun h0 _ h1 -> modifies1 e h0 h1 /\ h1.[|e|] == Spec.Kyber2.Indcpa.encode (v l) (to_spec_poly h0 x))

val decode:
  l:size_t{(v l)*params_n <= max_size_t}
  -> e:lbuffer uint8 (l*! ((size params_n) >>. 3))
  -> x:poly
  -> Stack unit
    (requires fun h -> live h x /\ live h e /\ Buf.disjoint x e)
    (ensures fun h0 _ h1 -> modifies1 x h0 h1 /\ (to_spec_poly h1 x) == Spec.Kyber2.Indcpa.decode (v l) h0.[|e|])

val keygen:
  (coins:lbuffer uint8 32ul)
  -> pk:lbuffer uint8 pklen
  -> sk:lbuffer uint8 sklen
  -> Stack bool
  (requires fun h -> live h coins /\ live h pk /\ live h sk /\ Buf.disjoint coins pk /\ Buf.disjoint coins sk /\ BUf.disjoint pk sk)
  (ensures fun h0 b h1 -> modifies2 pk sk h0 h1 match Spec.Kyber2.Indcpa.keygen h0.[|coins|] with
    |None --> b == false
    |Some (p,s) -> b == true /\ h1.[|pk|] == p /\ h2.[|sk|] == s)

val enc:
  pk:lbuffer uint8 pklen
  -> msg:lbuffer uint8 32ul
  -> msgcoins:lbuffer uint8 32ul
  -> ciphertext:lbuffer uint8 ciphertextlen
  -> Stack bool
    (requires fun h -> live h pk /\ live h msg /\ live h msgcoins /\ live h ciphertext /\
                    Buf.disjoint pk msg /\ Buf.disjoint pk msgcoins /\ Buf.disjoint pk ciphertext /\
                    Buf.disjoint msg msgcoins /\ Buf.disjoint msg ciphertext /\
                    Buf.disjoint msgcoins ciphertext)
    (ensures fun h0 b h1 -> modifies1 ciphertext h0 h1 /\ match Spec.Kyber2.Indcpa.enc h0.[|pk|] h0.[|msg|] h0.[|msgcoins|] with
      |None -> b == false
      |Some c -> b == true /\ h1.[|ciphertext|] == c)

assume val dec
  sk:lbuffer uint8 sklen
  -> ciphertext:lbuffer uint8 ciphertextlen
  -> msg':lbuffer uint8 32ul
  -> Stack unit
    (requires fun h -> live h pk /\ live h msg /\ live h msgcoins /\ live h ciphertext /\
                    Buf.disjoint sk ciphertext /\ Buf.disjoint sk msg' /\
                    Buf.disjoint msg' ciphertext)
    (ensures fun h0 b h1 -> modifies1 msg' h0 h1 /\ h1.[|msg'|] == Spec.Kyber2.Indcpa.dec h0.[|sk|] h0.[|c|])
