module Spec.ECC.Curves

open FStar.Mul

open Lib.ByteSequence
open Lib.IntTypes
open Lib.Sequence

open FStar.Math.Lemmas
open FStar.Math.Lib

#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"


(** The main instantiation of curves **) 
(* https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.186-4.pdf *)
type curve = 
  |P256
  |P384
  |Default


(* the length of each coordinate of the point as uint64 *)
inline_for_extraction noextract
val getCoordinateLenU64: c: curve -> Tot (a: size_t {v a * 20 < maxint U32})

let getCoordinateLenU64 curve = 
  match curve with
  |P256 -> 4ul
  |P384 -> 6ul  
  |_ -> 4ul


