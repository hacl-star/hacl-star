module Spec.Kyber2.Kem

open Spec.Kyber2.Indcpa

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

open Spec.Kyber2.FunctionInstantiation
open Spec.Kyber2.CBD

open FStar.Math.Lemmas

module Seq = Lib.Sequence

let sklen:size_nat = Indcpa.pklen+Indcpa.sklen+32+32
let pklen:size_nat = Indcpa.pklen
let ciphertextlen = Indcpa.ciphertextlen

val keygen: coins: lbytes_l SEC 32 -> indcpacoins:lbytes_l SEC 32 -> option ((lbytes_l SEC pklen) & (lbytes_l SEC sklen))

let keygen coins indcpacoins =
  match keygen indcpacoins with
  |None -> None
  |Some (pk', sk') -> Some (pk', concat (concat sk' pk') (concat (hash_h pklen pk') coins))

val enc: pk: lbytes_l SEC pklen -> msgcoins: lbytes_l SEC 32 -> sharedkeylen:size_nat -> option ((lbytes_l SEC ciphertextlen) & lbytes_l SEC sharedkeylen)

let enc pk msgcoins sharedkeylen =
  let m = hash_h 32 msgcoins in
  let (kbar, r) = hash_g 64 (concat m (hash_h pklen pk)) in
  match enc pk m r with
  |None -> None
  |Some c -> let k = kdf 64 sharedkeylen (concat kbar (hash_h ciphertextlen c)) in
  Some (c, k)

#reset-options "--z3rlimit 100 --max_fuel 2 --max_ifuel 2 --using_facts_from '* -FStar.Seq'"

val dec: c:(lbytes_l SEC ciphertextlen) -> sk:(lbytes_l SEC sklen) -> sharedkeylen:size_nat -> lbytes_l SEC sharedkeylen

let dec c sk sharedkeylen =
  let sk' = Seq.sub sk 0 Indcpa.sklen in
  let pk' = Seq.sub sk Indcpa.sklen Indcpa.pklen in
  let h = Seq.sub sk (Indcpa.sklen+Indcpa.pklen) 32 in
  let z = Seq.sub sk (Indcpa.sklen+Indcpa.pklen+32) 32 in
  let m' = dec sk' c in
  let (kbar',r') = hash_g 64 (concat m' h) in
  match Spec.Kyber2.Indcpa.enc pk' m' r' with
  |None -> kdf 64 sharedkeylen (concat z (hash_h ciphertextlen c))
  |Some c' -> if (lbytes_eq c c') then
    kdf 64 sharedkeylen (concat kbar' (hash_h ciphertextlen c))
  else 
    kdf 64 sharedkeylen (concat z (hash_h ciphertextlen c))
