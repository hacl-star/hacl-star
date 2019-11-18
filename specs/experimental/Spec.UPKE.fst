module Spec.UPKE

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence

module DH = Spec.Agile.DH
module AEAD = Spec.Agile.AEAD
module Hash = Spec.Agile.Hash
module HKDF = Spec.Agile.HKDF
module HPKE = Spec.Agile.HPKE


/// Clamp(a)

assume val of_string: string -> bytes
assume val scalar_to_nat: alg:DH.algorithm -> DH.scalar alg -> nat
assume val nat_to_scalar: alg:DH.algorithm -> nat -> DH.scalar alg

/// Mult(a,b) {
///   c = (Clamp(a) * Clamp(b)) mod order
///   if msb(c) = 0
///     c = (order - c) mod order
///   return c
/// }

val mul: alg:DH.algorithm -> DH.scalar alg -> DH.scalar alg -> Tot nat
let mul alg a b =
  let (a, b) = match alg with
    | DH.DH_Curve25519 -> (DH.clamp alg a, DH.clamp alg b)
    | DH.DH_Curve448 -> (DH.clamp alg a, DH.clamp alg b)
    | DH.DH_P256 -> (a, b) in
  let c = ((scalar_to_nat alg a) * (scalar_to_nat alg b)) % (DH.order alg) in
  // BB. Missing a reduction if the msb is = 0 because I can't quickly
  //     implement it in constant time.
  c

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

/// UPKE-Encrypt(pk, m):
///   d'  <-- {0,1}^secpar
///   d   := HKDF(sksize, d', "", "derive UPKE delta")
///   c1, context := HPKE.SetupBaseI(pk, "")
///   c2  <-- context.Seal("", d' || m)
///   pk' := DH(pk, d)
///   return ((c1, c2), pk')

val encrypt:
    cs:HPKE.ciphersuite
  -> deltaE:bytes
  -> skE:HPKE.key_dh_secret_s cs
  -> pkR:HPKE.key_dh_public_s cs
  -> m:bytes ->
  Tot(HPKE.key_dh_public_s cs & bytes & HPKE.key_dh_public_s cs)

let encrypt cs deltaE skE pkR m =
  admit();
  let delta = HKDF.expand (HPKE.hash_of_cs cs) deltaE (of_string "derive UPKE delta") (HPKE.size_dh_key cs) in
  let pkE,k,n = HPKE.setupBaseI cs skE pkR bytes_empty in
  let content = Seq.append deltaE m in
  let c = AEAD.encrypt #(HPKE.aead_of_cs cs) k n content lbytes_empty in
  let pkR' = DH.scalarmult (HPKE.curve_of_cs cs) delta pkR in
  pkE,c,pkR'


/// UPKE-Decrypt(sk, (c1, c2)):
///   epk, context := HPKE.SetupBaseR(c1, sk, "")
///   d' || m := context.Open("", c2)
///   d := HKDF(sksize, d', "", "derive UPKE delta")
///   sk' := Mult(sk, d)
///   return (m, sk')

val decrypt:
    cs:HPKE.ciphersuite
  -> pkE:HPKE.key_dh_public_s cs
  -> skR:HPKE.key_dh_secret_s cs
  -> ct:bytes ->
  Tot(option (bytes & HPKE.key_dh_secret_s cs))

let decrypt cs pkE skR ct =
  admit();
  let k,n = HPKE.setupBaseR cs pkE skR bytes_empty in
  match AEAD.decrypt #(HPKE.aead_of_cs cs) k n ct lbytes_empty with
  | None -> None
  | Some p ->
  let deltaE = Seq.slice p (HPKE.size_dh_key cs) (Seq.length p - (HPKE.size_dh_key cs)) in
  let m = Seq.slice p (Seq.length p - (HPKE.size_dh_key cs)) (Seq.length p) in
  let delta = HKDF.expand (HPKE.hash_of_cs cs) deltaE (of_string "derive UPKE delta") (HPKE.size_dh_key cs) in
  let skR' = DH.scalarmult (HPKE.curve_of_cs cs) skR delta in
  Some (m, skR')
