module Spec.AES256


open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators


#set-options "--initial_fuel 0 --max_fuel 0"

(* Parameters for AES-256 *)
inline_for_extraction let nb = 4
inline_for_extraction let nk = 8
inline_for_extraction let nr = 14

inline_for_extraction let wordlen = 4
inline_for_extraction let blocklen  = wordlen * nb
inline_for_extraction let keylen  = wordlen * nk

inline_for_extraction let xkeylen =
  let x = 4 * nb * (nr + 1) in
  assert_norm(x = 240);
  x// 176, 208, or 240


type block = lbytes blocklen
type skey  = lbytes keylen
type xkey  = lbytes xkeylen
type word  = lbytes wordlen

type rnd = r:size_nat{r <= nr}
type idx_16 = ctr:size_nat{ctr <= 16}

val xtime: uint8 -> Tot uint8
let xtime b =
  (b <<. 1ul) ^. (((b >>. 7ul) &. (u8 0x1)) *. (u8 0x1b))

val multiply: a:uint8 -> b:uint8 -> Tot uint8
let multiply a b =
  ((a *. (b &. (u8 0x1)))
  ^. (xtime a *. ((b >>. 1ul) &. (u8 0x1)))
  ^. (xtime (xtime a) *. ((b >>. 2ul) &. (u8 0x1)))
  ^. (xtime (xtime (xtime a)) *. ((b >>. 3ul) &. (u8 0x1)))
  ^. (xtime (xtime (xtime (xtime a))) *. ((b >>. 4ul) &. (u8 0x1)))
  ^. (xtime (xtime (xtime (xtime (xtime a)))) *. ((b >>. 5ul) &. (u8 0x1)))
  ^. (xtime (xtime (xtime (xtime (xtime (xtime a))))) *. ((b >>. 6ul) &. (u8 0x1)))
  ^. (xtime (xtime (xtime (xtime (xtime (xtime (xtime a)))))) *. ((b >>. 7ul) &. (u8 0x1))))

// tables for S-box and inv-S-box, derived from GF256 specification.

[@"opaque_to_smt"]
inline_for_extraction let inv_sbox : lseq uint8 256 =
  [@inline_let]
  let l : list FStar.UInt8.t = [
    0x52uy; 0x09uy; 0x6auy; 0xd5uy; 0x30uy ; 0x36uy; 0xa5uy; 0x38uy;
    0xbfuy; 0x40uy; 0xa3uy; 0x9euy; 0x81uy ; 0xf3uy; 0xd7uy; 0xfbuy;
    0x7cuy; 0xe3uy; 0x39uy; 0x82uy; 0x9buy ; 0x2fuy; 0xffuy; 0x87uy;
    0x34uy; 0x8euy; 0x43uy; 0x44uy; 0xc4uy ; 0xdeuy; 0xe9uy; 0xcbuy;
    0x54uy; 0x7buy; 0x94uy; 0x32uy; 0xa6uy ; 0xc2uy; 0x23uy; 0x3duy;
    0xeeuy; 0x4cuy; 0x95uy; 0x0buy; 0x42uy ; 0xfauy; 0xc3uy; 0x4euy;
    0x08uy; 0x2euy; 0xa1uy; 0x66uy; 0x28uy ; 0xd9uy; 0x24uy; 0xb2uy;
    0x76uy; 0x5buy; 0xa2uy; 0x49uy; 0x6duy ; 0x8buy; 0xd1uy; 0x25uy;
    0x72uy; 0xf8uy; 0xf6uy; 0x64uy; 0x86uy ; 0x68uy; 0x98uy; 0x16uy;
    0xd4uy; 0xa4uy; 0x5cuy; 0xccuy; 0x5duy ; 0x65uy; 0xb6uy; 0x92uy;
    0x6cuy; 0x70uy; 0x48uy; 0x50uy; 0xfduy ; 0xeduy; 0xb9uy; 0xdauy;
    0x5euy; 0x15uy; 0x46uy; 0x57uy; 0xa7uy ; 0x8duy; 0x9duy; 0x84uy;
    0x90uy; 0xd8uy; 0xabuy; 0x00uy; 0x8cuy ; 0xbcuy; 0xd3uy; 0x0auy;
    0xf7uy; 0xe4uy; 0x58uy; 0x05uy; 0xb8uy ; 0xb3uy; 0x45uy; 0x06uy;
    0xd0uy; 0x2cuy; 0x1euy; 0x8fuy; 0xcauy ; 0x3fuy; 0x0fuy; 0x02uy;
    0xc1uy; 0xafuy; 0xbduy; 0x03uy; 0x01uy ; 0x13uy; 0x8auy; 0x6buy;
    0x3auy; 0x91uy; 0x11uy; 0x41uy; 0x4fuy ; 0x67uy; 0xdcuy; 0xeauy;
    0x97uy; 0xf2uy; 0xcfuy; 0xceuy; 0xf0uy ; 0xb4uy; 0xe6uy; 0x73uy;
    0x96uy; 0xacuy; 0x74uy; 0x22uy; 0xe7uy ; 0xaduy; 0x35uy; 0x85uy;
    0xe2uy; 0xf9uy; 0x37uy; 0xe8uy; 0x1cuy ; 0x75uy; 0xdfuy; 0x6euy;
    0x47uy; 0xf1uy; 0x1auy; 0x71uy; 0x1duy ; 0x29uy; 0xc5uy; 0x89uy;
    0x6fuy; 0xb7uy; 0x62uy; 0x0euy; 0xaauy ; 0x18uy; 0xbeuy; 0x1buy;
    0xfcuy; 0x56uy; 0x3euy; 0x4buy; 0xc6uy ; 0xd2uy; 0x79uy; 0x20uy;
    0x9auy; 0xdbuy; 0xc0uy; 0xfeuy; 0x78uy ; 0xcduy; 0x5auy; 0xf4uy;
    0x1fuy; 0xdduy; 0xa8uy; 0x33uy; 0x88uy ; 0x07uy; 0xc7uy; 0x31uy;
    0xb1uy; 0x12uy; 0x10uy; 0x59uy; 0x27uy ; 0x80uy; 0xecuy; 0x5fuy;
    0x60uy; 0x51uy; 0x7fuy; 0xa9uy; 0x19uy ; 0xb5uy; 0x4auy; 0x0duy;
    0x2duy; 0xe5uy; 0x7auy; 0x9fuy; 0x93uy ; 0xc9uy; 0x9cuy; 0xefuy;
    0xa0uy; 0xe0uy; 0x3buy; 0x4duy; 0xaeuy ; 0x2auy; 0xf5uy; 0xb0uy;
    0xc8uy; 0xebuy; 0xbbuy; 0x3cuy; 0x83uy ; 0x53uy; 0x99uy; 0x61uy;
    0x17uy; 0x2buy; 0x04uy; 0x7euy; 0xbauy ; 0x77uy; 0xd6uy; 0x26uy;
    0xe1uy; 0x69uy; 0x14uy; 0x63uy; 0x55uy ; 0x21uy; 0x0cuy; 0x7duy
  ] in
  let l = FStar.List.Tot.Base.map Lib.RawIntTypes.u8_from_UInt8 l in
  assert_norm(FStar.List.Tot.Base.length l = 256);
  of_list l


[@"opaque_to_smt"]
inline_for_extraction let sbox : lseq uint8 256 =
  [@inline_let]
  let l : list FStar.UInt8.t = [
    0x63uy; 0x7cuy; 0x77uy; 0x7buy; 0xf2uy; 0x6buy; 0x6fuy; 0xc5uy;
    0x30uy; 0x01uy; 0x67uy; 0x2buy; 0xfeuy; 0xd7uy; 0xabuy; 0x76uy;
    0xcauy; 0x82uy; 0xc9uy; 0x7duy; 0xfauy; 0x59uy; 0x47uy; 0xf0uy;
    0xaduy; 0xd4uy; 0xa2uy; 0xafuy; 0x9cuy; 0xa4uy; 0x72uy; 0xc0uy;
    0xb7uy; 0xfduy; 0x93uy; 0x26uy; 0x36uy; 0x3fuy; 0xf7uy; 0xccuy;
    0x34uy; 0xa5uy; 0xe5uy; 0xf1uy; 0x71uy; 0xd8uy; 0x31uy; 0x15uy;
    0x04uy; 0xc7uy; 0x23uy; 0xc3uy; 0x18uy; 0x96uy; 0x05uy; 0x9auy;
    0x07uy; 0x12uy; 0x80uy; 0xe2uy; 0xebuy; 0x27uy; 0xb2uy; 0x75uy;
    0x09uy; 0x83uy; 0x2cuy; 0x1auy; 0x1buy; 0x6euy; 0x5auy; 0xa0uy;
    0x52uy; 0x3buy; 0xd6uy; 0xb3uy; 0x29uy; 0xe3uy; 0x2fuy; 0x84uy;
    0x53uy; 0xd1uy; 0x00uy; 0xeduy; 0x20uy; 0xfcuy; 0xb1uy; 0x5buy;
    0x6auy; 0xcbuy; 0xbeuy; 0x39uy; 0x4auy; 0x4cuy; 0x58uy; 0xcfuy;
    0xd0uy; 0xefuy; 0xaauy; 0xfbuy; 0x43uy; 0x4duy; 0x33uy; 0x85uy;
    0x45uy; 0xf9uy; 0x02uy; 0x7fuy; 0x50uy; 0x3cuy; 0x9fuy; 0xa8uy;
    0x51uy; 0xa3uy; 0x40uy; 0x8fuy; 0x92uy; 0x9duy; 0x38uy; 0xf5uy;
    0xbcuy; 0xb6uy; 0xdauy; 0x21uy; 0x10uy; 0xffuy; 0xf3uy; 0xd2uy;
    0xcduy; 0x0cuy; 0x13uy; 0xecuy; 0x5fuy; 0x97uy; 0x44uy; 0x17uy;
    0xc4uy; 0xa7uy; 0x7euy; 0x3duy; 0x64uy; 0x5duy; 0x19uy; 0x73uy;
    0x60uy; 0x81uy; 0x4fuy; 0xdcuy; 0x22uy; 0x2auy; 0x90uy; 0x88uy;
    0x46uy; 0xeeuy; 0xb8uy; 0x14uy; 0xdeuy; 0x5euy; 0x0buy; 0xdbuy;
    0xe0uy; 0x32uy; 0x3auy; 0x0auy; 0x49uy; 0x06uy; 0x24uy; 0x5cuy;
    0xc2uy; 0xd3uy; 0xacuy; 0x62uy; 0x91uy; 0x95uy; 0xe4uy; 0x79uy;
    0xe7uy; 0xc8uy; 0x37uy; 0x6duy; 0x8duy; 0xd5uy; 0x4euy; 0xa9uy;
    0x6cuy; 0x56uy; 0xf4uy; 0xeauy; 0x65uy; 0x7auy; 0xaeuy; 0x08uy;
    0xbauy; 0x78uy; 0x25uy; 0x2euy; 0x1cuy; 0xa6uy; 0xb4uy; 0xc6uy;
    0xe8uy; 0xdduy; 0x74uy; 0x1fuy; 0x4buy; 0xbduy; 0x8buy; 0x8auy;
    0x70uy; 0x3euy; 0xb5uy; 0x66uy; 0x48uy; 0x03uy; 0xf6uy; 0x0euy;
    0x61uy; 0x35uy; 0x57uy; 0xb9uy; 0x86uy; 0xc1uy; 0x1duy; 0x9euy;
    0xe1uy; 0xf8uy; 0x98uy; 0x11uy; 0x69uy; 0xd9uy; 0x8euy; 0x94uy;
    0x9buy; 0x1euy; 0x87uy; 0xe9uy; 0xceuy; 0x55uy; 0x28uy; 0xdfuy;
    0x8cuy; 0xa1uy; 0x89uy; 0x0duy; 0xbfuy; 0xe6uy; 0x42uy; 0x68uy;
    0x41uy; 0x99uy; 0x2duy; 0x0fuy; 0xb0uy; 0x54uy; 0xbbuy; 0x16uy
  ] in
  let l = FStar.List.Tot.Base.map Lib.RawIntTypes.u8_from_UInt8 l in
  assert_norm(FStar.List.Tot.Base.length l = 256);
  of_list l

// ENCRYPTION

let sbox_idx = i:size_nat{i < 256}

let access_sbox (i:sbox_idx) = index sbox i

let access_inv_sbox (i:sbox_idx) = index inv_sbox i

#set-options "--max_fuel 0 --z3rlimit 5"

val subBytes_sbox: state:block -> block
let subBytes_sbox state =
  Lib.LoopCombinators.repeati 16 (fun ctr state ->
    let si = state.[ctr] in
    let si' = access_sbox (uint_to_nat si) in
    let state = state.[ctr] <- si' in
  state) state

#set-options "--z3rlimit 40"

val shiftRows: state:block -> block
let shiftRows state =
  let i = 1 in
  let tmp           = state.[i]                    in
  let state : block = state.[i]    <- state.[i+4]  in
  let state : block = state.[i+4]  <- state.[i+8]  in
  let state : block = state.[i+8]  <- state.[i+12] in
  let state : block = state.[i+12] <- tmp          in

  let i = 2 in
  let tmp           = state.[i]                    in
  let state : block = state.[i]    <- state.[i+8]  in
  let state : block = state.[i+8]  <- tmp          in
  let tmp           = state.[i+4]                  in
  let state : block = state.[i+4]  <- state.[i+12] in
  let state : block = state.[i+12] <- tmp in

  let i = 3 in
  let tmp   =         state.[i]                    in
  let state : block = state.[i]    <- state.[i+12] in
  let state : block = state.[i+12] <- state.[i+8]  in
  let state : block = state.[i+8]  <- state.[i+4]  in
  let state : block = state.[i+4]  <- tmp          in
  state

#set-options "--z3rlimit 10"

val mixColumns_: state:block -> c:size_nat{c < 4} -> block
let mixColumns_ state c =
  let s : lseq uint8 4 = sub state (4*c) 4 in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  let s = s.[0] <- multiply (u8 0x2) s0 ^. multiply (u8 0x3) s1 ^. s2 ^. s3 in
  let s = s.[1] <- multiply (u8 0x2) s1 ^. multiply (u8 0x3) s2 ^. s3 ^. s0 in
  let s = s.[2] <- multiply (u8 0x2) s2 ^. multiply (u8 0x3) s3 ^. s0 ^. s1 in
  let s = s.[3] <- multiply (u8 0x2) s3 ^. multiply (u8 0x3) s0 ^. s1 ^. s2 in
  let state = update_sub state (4*c) 4 s in
  state

#set-options "--z3rlimit 20"

val mixColumns: state:block -> block
let mixColumns state =
  let state = mixColumns_ state 0 in
  let state = mixColumns_ state 1 in
  let state = mixColumns_ state 2 in
  let state = mixColumns_ state 3 in
  state


val addRoundKey_: state:block -> w:xkey -> rnd -> c:size_nat{c < 4} -> block
let addRoundKey_ state w round c =
  let target = sub state (4*c) 4 in
  let offset : n:size_nat{n <= 224} = blocklen * round in
  let offset = offset + 4*c in
  let subkey = sub w offset 4 in
  let target = target.[0] <- target.[0] ^. subkey.[0] in
  let target = target.[1] <- target.[1] ^. subkey.[1] in
  let target = target.[2] <- target.[2] ^. subkey.[2] in
  let target = target.[3] <- target.[3] ^. subkey.[3] in
  let state = update_sub state (4*c) 4 target in
  state

#set-options "--z3rlimit 10"

val addRoundKey: state:block -> w:xkey -> round:rnd  -> block
let addRoundKey state w round =
  let state = addRoundKey_ state w round 0 in
  let state = addRoundKey_ state w round 1 in
  let state = addRoundKey_ state w round 2 in
  let state = addRoundKey_ state w round 3 in
  state

#set-options "--max_fuel 1 --z3rlimit 20"

val cipher_round: state:block -> w:xkey -> round:rnd -> Tot block
let cipher_round state w round =
  let state = subBytes_sbox state in
  let state = shiftRows     state in
  let state = mixColumns    state in
  let state = addRoundKey   state w round in
  state
val cipher: input:block -> w:xkey -> Tot block
let cipher input w =
  // could we use output instead? alignment?
  let state = input in
  let state = addRoundKey    state w 0 in
  let state = Lib.LoopCombinators.repeati (nr - 1) (fun round state ->
    cipher_round state w (round + 1)
  ) state in
  //let state = cipher_loop    state w 1 in
  let state = subBytes_sbox  state in
  let state = shiftRows      state in
  let state = addRoundKey    state w nr in
  state

#set-options "--z3rlimit 5"

// KEY EXPANSION

val rotWord: word -> Tot word
let rotWord word =
  let w0 = word.[0] in
  let w1 = word.[1] in
  let w2 = word.[2] in
  let w3 = word.[3] in
  let word = word.[0] <- w1 in
  let word = word.[1] <- w2 in
  let word = word.[2] <- w3 in
  let word = word.[3] <- w0 in
  word

val subWord: word -> word
let subWord word =
  let word = word.[0] <- access_sbox (uint_to_nat word.[0]) in
  let word = word.[1] <- access_sbox (uint_to_nat word.[1]) in
  let word = word.[2] <- access_sbox (uint_to_nat word.[2]) in
  let word = word.[3] <- access_sbox (uint_to_nat word.[3]) in
  word

#set-options "--max_fuel 1 --z3rlimit 10"

val rcon: i:size_nat{i >= 1} -> uint8 -> Tot uint8 (decreases (i))
let rcon i tmp =
  Lib.LoopCombinators.repeat (i - 1) (fun tmp ->
    multiply (u8 2) tmp
  ) tmp

val keyExpansion_aux_0:
  w:xkey ->
  i:size_nat{i < xkeylen / wordlen /\ i >= nk} ->
  word
let keyExpansion_aux_0 w j =
  let temp : word = sub w (wordlen * (j - 1)) wordlen in
  if j % nk = 0 then begin
    let temp = rotWord temp in
    let temp = subWord temp in
    let t0 = temp.[0] in
    let rc = rcon (j / nk) (u8 1) in
    let z = t0 ^. rc in
    let temp = temp.[0] <- z in
    temp
  end else if j % nk = wordlen then
    subWord temp
  else
    temp

#set-options "--z3rlimit 20"

val keyExpansion_aux_1:
  w:xkey ->
  temp:word ->
  i:size_nat{i < (xkeylen / wordlen) /\ i >= nk} ->
  Tot xkey
let keyExpansion_aux_1 w temp j =
  let i = j * wordlen in
  let w0 = w.[i + 0 - keylen] in
  let w1 = w.[i + 1 - keylen] in
  let w2 = w.[i + 2 - keylen] in
  let w3 = w.[i + 3 - keylen] in
  let t0 = temp.[0] in
  let t1 = temp.[1] in
  let t2 = temp.[2] in
  let t3 = temp.[3] in
  let w = w.[i + 0] <- t0 ^. w0 in
  let w = w.[i + 1] <- t1 ^. w1 in
  let w = w.[i + 2] <- t2 ^. w2 in
  let w = w.[i + 3] <- t3 ^. w3 in
  w

inline_for_extraction let xkeylen_w =
  let x = xkeylen / wordlen in
  assert_norm(x = 60);
  x

val keyExpansion_aux:
  w:xkey ->
  Tot xkey
let keyExpansion_aux w =
  Lib.LoopCombinators.repeati #xkey (xkeylen_w - nk) (fun j w ->
   let j = j + nk in
   let temp = keyExpansion_aux_0 w j in
   keyExpansion_aux_1 w temp j
  ) w

#set-options "--z3rlimit 5"

val keyExpansion: key:skey -> xkey
let keyExpansion key =
  let w = create xkeylen (u8 0) in
  let w = update_sub w 0 keylen key in
  keyExpansion_aux w

// DECRYPTION

#set-options "--z3rlimit 10"

val invSubBytes_sbox: state:block -> block
let invSubBytes_sbox state =
  Lib.LoopCombinators.repeati blocklen (fun ctr state ->
    let si = state.[ctr] in
    let si' = access_inv_sbox (uint_to_nat si) in
    let state = state.[ctr] <- si' in
    state
  ) state

#set-options "--z3rlimit 40"

val invShiftRows: state:block -> block
let invShiftRows state =
  let i = 3 in
  let tmp           = state.[i]                    in
  let state : block = state.[i]    <- state.[i+4]  in
  let state : block = state.[i+4]  <- state.[i+8]  in
  let state : block = state.[i+8]  <- state.[i+12] in
  let state : block = state.[i+12] <- tmp          in

  let i = 2 in
  let tmp           = state.[i] in
  let state : block = state.[i]    <- state.[i+8]  in
  let state : block = state.[i+8]  <- tmp          in
  let tmp           = state.[i+4]                  in
  let state : block = state.[i+4]  <- state.[i+12] in
  let state : block = state.[i+12] <- tmp          in

  let i = 1 in
  let tmp           = state.[i]                    in
  let state : block = state.[i]    <- state.[i+12] in
  let state : block = state.[i+12] <- state.[i+8]  in
  let state : block = state.[i+8]  <- state.[i+4]  in
  let state : block = state.[i+4]  <- tmp          in
  state

#set-options "--z3rlimit 10"

val invMixColumns_: state:block -> c:size_nat{c < 4} -> Tot block
let invMixColumns_ state c =
  let s = sub state (wordlen*c) wordlen in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  let mix x0 x1 x2 x3 =
    multiply (u8 0xe) x0 ^. multiply (u8 0xb) x1 ^.
    multiply (u8 0xd) x2 ^. multiply (u8 0x9) x3
  in
  let s = s.[0] <- mix s0 s1 s2 s3 in
  let s = s.[1] <- mix s1 s2 s3 s0 in
  let s = s.[2] <- mix s2 s3 s0 s1 in
  let s = s.[3] <- mix s3 s0 s1 s2 in
  update_sub state (wordlen*c) wordlen s

val invMixColumns: state:block -> Tot block
let invMixColumns state =
  let state = invMixColumns_ state 0 in
  let state = invMixColumns_ state 1 in
  let state = invMixColumns_ state 2 in
  let state = invMixColumns_ state 3 in
  state

#set-options "--z3rlimit 20"

val inv_cipher_round:
  state:block ->
  w:xkey ->
  round:size_nat{round <= nr - 1} ->
  Tot block
let inv_cipher_round state w round =
  let state = invShiftRows state in
  let state = invSubBytes_sbox state in
  let state = addRoundKey state w round in
  let state = invMixColumns state in
  state

val inv_cipher: input:block -> w:xkey -> block
let inv_cipher input w =
  let state = input in
  let state = addRoundKey      state w nr in
  let state = Lib.LoopCombinators.repeati (nr - 1) (fun i state ->
    let rnd = nr - 1 - i in
    inv_cipher_round state w rnd
  ) state in
  //let state = inv_cipher_loop  state w (nr - 1) in
  let state = invShiftRows     state in
  let state = invSubBytes_sbox state in
  let state = addRoundKey      state w 0 in
  state
