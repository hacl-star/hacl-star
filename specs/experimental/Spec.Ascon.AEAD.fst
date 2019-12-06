module Spec.Ascon.AEAD

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.ByteSequence.Tuples
open Lib.LoopCombinators

open Spec.Ascon


inline_for_extraction
let vsize_key: size_nat = 16

inline_for_extraction
let vsize_tag: size_nat = 16


inline_for_extraction
let rate: size_nat = 128 / 8

inline_for_extraction
let pa_rounds: size_nat = 12

inline_for_extraction
let pb_rounds: size_nat = 8



inline_for_extraction
let iv: uint64 =
  ((u64 (8 * vsize_key)) <<. size 56) |.
  ((u64 (8 * rate)) <<. size 48) |.
  ((u64 pa_rounds) <<. size 40) |.
  ((u64 pb_rounds) <<. size 32)



val encrypt: c:bytes -> m:bytes -> adlen:size_nat -> ad:lbytes adlen -> nsec:bytes -> npub:bytes -> k:bytes -> bytes
let encrypt c m adlen ad nsec npub k =
  let adn = adlen / rate in
  let k0 = uint_from_bytes_be (sub k 0 8) in
  let k1 = uint_from_bytes_be (sub k 8 8) in
  let n0 = uint_from_bytes_be (sub npub 0 8) in
  let n1 = uint_from_bytes_be (sub npub 8 8) in
  // initialization
  let s = collapse (u64 0) (iv,k0,k1,n0,n1) in
  let s = p12 s in
  let s = s.[3] <- s.[3] ^. k0 in
  let s = s.[4] <- s.[4] ^. k1 in
  // process associated data
  let s =
    if adlen = 0 then s else
      let s = repeati adn (fun i s' ->
        let ad0 = sub ad (i * rate) ((i+1) * rate) in
        let ad1 = sub ad ((i+1) * rate) ((i+2) * rate) in
        let s' = s'.[0] <- s'.[0] ^. (uint_from_bytes_be ad0) in
        let s' = s'.[1] <- s'.[1] ^. (uint_from_bytes_be ad1) in s'
      ) s in
      let s =
        if adlen >= 8 then (
          let ad0 = sub ad ((adn+i) * rate) ((adn+i+1) * rate) in
          let ad1 = sub ad ((adn+i+1) * rate) ((adn+i+2) * rate) in
          let z = (u64 0x80) <<. (size 56 -. (size 8) *. (size adlen -. size 8)) in
          let s = s.[0] <- s.[0] ^. (uint_from_bytes_be ad0) in
          let s = s.[1] <- s.[1] ^. (uint_from_bytes_be ad1) in
          let s = s.[1] <- s.[1] ^. z in s)
        else (
          let ad0 = slice ad (adlen - rem) adlen in
          let s = s.[0] <- s.[0] ^. (uint_from_bytes_be ad0) in
          let z = (u64 0x80) <<. (size 56 -. (size 8) *. (size adlen)) in
          let s = s.[1] <- s.[1] ^. z in s)
      in
      p8 s
  in

(*   s.x4 ^= 1; *)
(*   printstate("process associated data:", s); *)

(*   // process plaintext *)
(*   while (mlen >= RATE) { *)
(*     s.x0 ^= BYTES_TO_U64(m, 8); *)
(*     s.x1 ^= BYTES_TO_U64(m + 8, 8); *)
(*     U64_TO_BYTES(c, s.x0, 8); *)
(*     U64_TO_BYTES(c + 8, s.x1, 8); *)
(*     P8(&s); *)
(*     mlen -= RATE; *)
(*     m += RATE; *)
(*     c += RATE; *)
(*   } *)
(*   if (mlen >= 8) { *)
(*     s.x0 ^= BYTES_TO_U64(m, 8); *)
(*     s.x1 ^= BYTES_TO_U64(m + 8, mlen - 8); *)
(*     s.x1 ^= 0x80ull << (56 - 8 * (mlen - 8)); *)
(*     U64_TO_BYTES(c, s.x0, 8); *)
(*     U64_TO_BYTES(c + 8, s.x1, mlen - 8); *)
(*   } else { *)
(*     s.x0 ^= BYTES_TO_U64(m, mlen); *)
(*     s.x0 ^= 0x80ull << (56 - 8 * mlen); *)
(*     U64_TO_BYTES(c, s.x0, mlen); *)
(*   } *)
(*   c += mlen; *)
(*   printstate("process plaintext:", s); *)

(*   // finalization *)
(*   s.x2 ^= K0; *)
(*   s.x3 ^= K1; *)
(*   P12(&s); *)
(*   s.x3 ^= K0; *)
(*   s.x4 ^= K1; *)
(*   printstate("finalization:", s); *)

(*   // set tag *)
(*   U64_TO_BYTES(c, s.x3, 8); *)
(*   U64_TO_BYTES(c + 8, s.x4, 8); *)

(*   return 0; *)
(* } *)

