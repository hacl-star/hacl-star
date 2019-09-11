module Impl.Kyber2.Kem

open Impl.Kyber2.Indcpa

open FStar.Mul

open Spec.Kyber2.Params
open Spec.Powtwo.Lemmas
open Lib.Poly
open Lib.Poly.NTT2
open Lib.NumericTypes

open Lib.Arithmetic.Group
open Lib.Arithmetic.Ring
open Lib.Arithmetic.Sums
open Lib.Arithmetic.Group.Uint_t
open Lib.Arithmetic.Ring.Uint_t

open Lib.Sequence
open Lib.ByteSequence
open Lib.IntTypes
open Lib.NumericTypes

open Lib.ModularArithmetic
open Lib.ModularArithmetic.Lemmas

open Impl.Kyber2.FunctionInstantiation
open Impl.Kyber2.CBD

open FStar.Math.Lemmas

module Seq = Lib.Sequence
module Buf = Lib.Buffer

let sklen:size_t = size Spec.Kyber2.Kem.sklen
let pklen:size_t = size Spec.Kyber2.Kem.pklen
let ciphertextlen = size Spec.Kyber2.Kem.ciphertextlen

val keygen:
  coins: lbuffer uint8 32ul
  -> indcpacoins:lbuffer uint8 32ul
  -> pk:lbuffer uint8 pklen
  -> sk:lbuffer uint8 sklen
  -> Stack bool
    (requires fun h -> live h coins /\ live h indcpacoins /\ live h pk /\ live h sk /\
                    Buf.disjoint coins indcpacoins /\ Buf.disjoint coins pk /\ Buf.disjoint coins sk /\
                    Buf.disjoint indcpacoins pk /\ Buf.disjoint indcpacoins sk /\
                    Buf.disjoint pk sk)
    (ensures fun h0 b h1 -> modifies2 pk sk h0 h1 /\ match Spec.Kyber2.Kem.keygen h0.[|coins|] h0.[|indcpacoins|] with
      |None -> b == false
      |Some (p, s) -> b == true /\ h1.[|pk|] == p /\ h1.[|sk|] == s)

let keygen coins indcpacoins pk sk =
  push_frame ();
  let b = keygen indcpacoins coins pk (Buf.sub sk 0ul Impl.Kyber2.Indcpa.sklen) in
  if (b == true) then
    (Buf.copy (Buf.sub sk Impl.Kyber2.Indcpa.sklen pklen) pk;
     hash_h pklen pk (Buf.sub sk (Impl.Kyber2.Indcpa.sklen+!pklen) 32ul);
     Buf.copy (Buf.sub sk (Impl.Kyber2.Indcpa.sklen+!pklen+!32ul) 32ul) coins);
  pop_frame ();
  admit();
  b

val enc:
  pk:lbuffer uint8 pklen
  -> msgcoins:lbuffer uint8 32ul
  -> sharedkeylen:size_t
  -> ciphertext:lbuffer uint8 ciphertextlen
  -> sharedkey:lbuffer uint8 sharedkeylen
  -> Stack bool
    (requires fun h -> live h pk /\ live h msgcoins /\ live h ciphertext /\ live h sharedkey /\
                    Buf.disjoint pk msgcoins /\ Buf.disjoint pk ciphertext /\ Buf.disjoint pk sharedkey /\
                    Buf.disjoint msgcoins ciphertext /\ Buf.disjoint msgcoins ciphertext /\
                    Buf.disjoint ciphertext sharedkey)
    (ensures fun h0 b h1 -> modifies2 ciphertext sharedkey h0 h1 /\ match Spec.Kyber2.Kem.enc h0.[|pk|] h0.[|msgcoins|] (v sharedkeylen) with
      |None -> b == false
      |Some (c,k) -> b == true /\ h1.[|ciphertext|] == c /\ h1.[|sharedkey|] == k)

let enc pk msgcoins sharedkeylen ciphertext sharedkey =
  push_frame ()
  let m = Buf.create 64ul 0ul in
  let r = Buf.create 32ul 0ul in
  let kbar = Buf.create 64ul 0ul in
  hash_h 32ul msgcoins (Buf.sub m 0ul 32ul);
  hash_h pklen pk (Buf.sub m 32ul 32ul);
  hash_g 64ul m (Buf.sub kbar 0ul 32ul) r;
  let b = enc pk (Buf.sub m 0ul 32ul) r ciphertext in
  if (b==true) then
    (hash_h ciphertextlen ciphertext (Buf.sub kbar 32ul 32ul);
    kdf 64ul sharedkeylen kbar sharedkey);
  pop_frame ();
  admit();
  b

val dec:
  ciphertext:lbuffer uint8 ciphertextlen
  -> sk:lbuffer uint8 sklen
  -> sharedkeylen:size_t
  -> sharedkey:lbuffer uint8 sharedkeylen
  -> Stack unit
    (requires fun h -> live h ciphertext /\ live h sk /\ live h sharedkey /\
                    Buf.disjoint ciphertext sk /\ Buf.disjoint ciphertext sharedkey /\
                    Buf.disjoint sk sharedkey)
    (ensures fun h0 _ h1 -> modifies1 sharedkey h0 h1 /\ h1.[|sharedkey|] == Spec.Kyber2.Kem.dec h0.[|ciphertext|] h0.[|sk|] (v sharedkeylen))

let dec ciphertext sk sharedkeylen sharedkey =
  push_frame ();
  let sk' = Buf.sub sk 0ul Indcpa.sklen in
  let pk' = Buf.sub sk Indcpa.sklen Indcpa.pklen in
  let h = Buf.sub sk (Indcpa.sklen+!Indcpa.pklen) 32ul in
  let z = Seq.sub sk (Indcpa.sklen+!Indcpa.pklen+!32ul) 32ul in
  let m' = Buf.create 64ul 0ul in
  let kbar' = Buf.create 64ul 0ul in
  let r' = Buf.create 32ul 0ul in
  let c' = Buf.create Indcpa.ciphertextlen 0ul in
  dec sk' ciphertext m';
  Buf.copy (Buf.sub m' 32ul 32ul) h;
  hash_g 64ul m';
  let b = Indcpa.enc pk' m' r' c' in
  hash_h ciphertextlen c (Buf.sub kbar' 32ul 32ul);
  if (b==true && Lib.ByteBuffer.lbytes_eq ciphertext c') then
    kdf 64ul sharedkeylen kbar' sharedkey
  else (
    Buf.copy (Buf.sub kbar' 0ul 32ul) z;
    kdf 64ul sharedkeylen kbar' sharedkey
  );
  admit();
  pop_frame ()
