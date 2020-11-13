module Spec.Dilithium.Packing2

open Spec.Dilithium.Params
open Spec.Dilithium.Poly

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators

// for strange and unknown reasons putting these functions in Packing breaks stuff

val unpack_c: packed_c: lbytes (param_n/8 + 8) -> option poly

let unpack_c packed_c =
  let (signs:uint64) = uint_from_bytes_le (sub packed_c 0 8) in
  if v (signs >>. size 60) > 0 then None else
  let c, signs = (repeati (param_n/8) (fun i (c, signs) ->
    (repeati 8 (fun j (c, signs) ->
      if v ((packed_c.[i] >>. size j) &. (u8 0x01)) > 1
        then let x:uint32 = (if (v signs) % 2 = 0 then u32 1 else u32 (param_q - 1)) in
          ((c.[8*i + j] <- x), signs >>. size 1)
        else (c, signs >>. size 1)
      ) (c, signs))
  ) (new_poly, signs)) in
  Some c


#set-options "--fuel 2 --ifuel 2 --z3rlimit 100"

let polyt1_pack (p:poly) : lbytes polyt1_packedbytes =
  // (create polyt1_packedbytes (u8 0))
  assert (288 = 9 * 256 / 8);
  assert (polyt1_packedbytes = 288);
  // assert (param_n = 256);
  assert (polyt1_packedbytes = 9 * param_n / 8);
  let r:lbytes polyt1_packedbytes = create polyt1_packedbytes (u8 0) in
  repeati (param_n/8) (fun i r ->
    let r = r.[9*i+0] <- to_u8 ((p.[8*i+0] >>. size 0)) in
    let r = r.[9*i+1] <- to_u8 ((p.[8*i+0] >>. size 8) |. (p.[8*i+1] <<. size 1)) in
    let r = r.[9*i+2] <- to_u8 ((p.[8*i+1] >>. size 7) |. (p.[8*i+2] <<. size 2)) in
    let r = r.[9*i+3] <- to_u8 ((p.[8*i+2] >>. size 6) |. (p.[8*i+3] <<. size 3)) in
    let r = r.[9*i+4] <- to_u8 ((p.[8*i+3] >>. size 5) |. (p.[8*i+4] <<. size 4)) in
    let r = r.[9*i+5] <- to_u8 ((p.[8*i+4] >>. size 4) |. (p.[8*i+5] <<. size 5)) in
    let r = r.[9*i+6] <- to_u8 ((p.[8*i+5] >>. size 3) |. (p.[8*i+6] <<. size 6)) in
    let r = r.[9*i+7] <- to_u8 ((p.[8*i+6] >>. size 2) |. (p.[8*i+7] <<. size 7)) in
    let r = r.[9*i+8] <- to_u8 ((p.[8*i+7] >>. size 1)) in
    r) r
