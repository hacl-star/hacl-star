module Spec.UPKE

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.RandomSequence

module DH = Spec.Agile.DH
module AEAD = Spec.Agile.AEAD.Hacl
module Hash = Spec.Agile.Hash
module HKDF = Spec.Agile.HKDF
module HPKE = Spec.HPKE



/// Mult(a,b) {
///   c = (Clamp(a) * Clamp(b)) mod order
///   if msb(c) = 0
///     c = (order - c) mod order
///   return c
/// }


/// UPKE-Encrypt(pk, m):
///   d'  <-- {0,1}^secpar
///   d   := HKDF(sksize, d', "", "derive UPKE delta")
///   c1, context := HPKE.SetupBaseI(pk, "")
///   c2  <-- context.Seal("", d' || m)
///   pk' := DH(pk, d)
///   return ((c1, c2), pk')


/// UPKE-Decrypt(sk, (c1, c2)):
///   epk, context := HPKE.SetupBaseR(c1, sk, "")
///   d' || m := context.Open("", c2)
///   d := HKDF(sksize, d', "", "derive UPKE delta")
///   sk' := Mult(sk, d)
///   return (m, sk')
