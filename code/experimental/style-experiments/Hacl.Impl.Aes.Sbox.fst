module Hacl.Impl.Aes.Sbox

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

// FIPS197 ?
// TODO factor it out in terms of https://en.wikipedia.org/wiki/AES_instruction_set
// see also https://software.intel.com/sites/default/files/article/165683/aes-wp-2012-09-22-v01.pdf

// TODO this is AES256; 
// we also need AES128 (nk=4ul, nr=10) and maybe AES192 (nk=6ul,nr=12).

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.UInt8
open FStar.Int.Cast
open LowStar.Buffer
module B = LowStar.Buffer

(* Module abbreviations *)

module HS = FStar.HyperStack

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module H8  = FStar.UInt8
module H32  = FStar.UInt32


type bytes = B.buffer U8.t
type lbytes l = b:bytes {length b = l} 
let v (x:UInt32.t) : nat  = UInt32.v x

(* Parameters for AES-128 *)
private inline_for_extraction let nb =  4ul 
private inline_for_extraction let nk =  8ul // 4, 6, or 8
private inline_for_extraction let nr = 14ul // 10, 12, or 14

inline_for_extraction let blocklen = U32.(4ul *^ nb)
inline_for_extraction let keylen   = U32.(4ul *^ nk)
inline_for_extraction let xkeylen  = U32.(4ul *^ nb *^ (nr +^ 1ul)) // 176, 208, or 240

type block = lbytes (v blocklen)
type skey  = lbytes (v keylen)
type xkey  = lbytes (v xkeylen)

type rnd = r:UInt32.t{v r <= v nr}
type idx_16 = ctr:UInt32.t{v ctr <= 16}

private val xtime: b:byte -> Tot byte
let xtime b =
  (b <<^ 1ul) ^^ (((b >>^ 7ul) &^ 1uy) *%^ 0x1buy)

private val multiply: a:byte -> b:byte -> Tot byte
let multiply a b =
  ((a *%^ (b &^ 1uy))
  ^^ (xtime a *%^ ((b >>^ 1ul) &^ 1uy))
  ^^ (xtime (xtime a) *%^ ((b >>^ 2ul) &^ 1uy))
  ^^ (xtime (xtime (xtime a)) *%^ ((b >>^ 3ul) &^ 1uy))
  ^^ (xtime (xtime (xtime (xtime a))) *%^ ((b >>^ 4ul) &^ 1uy))
  ^^ (xtime (xtime (xtime (xtime (xtime a)))) *%^ ((b >>^ 5ul) &^ 1uy))
  ^^ (xtime (xtime (xtime (xtime (xtime (xtime a))))) *%^ ((b >>^ 6ul) &^ 1uy))
  ^^ (xtime (xtime (xtime (xtime (xtime (xtime (xtime a)))))) *%^ ((b >>^ 7ul) &^ 1uy)))

#set-options "--lax"
// tables for S-box and inv-S-box, derived from GF256 specification.

let inv_sbox : (b:B.buffer FStar.UInt8.t{B.recallable b /\ B.length b == 256}) = 
  B.gcmalloc_of_list HS.root  [
    0x52uy; 0x09uy; 0x6auy; 0xd5uy;
    0x30uy; 0x36uy; 0xa5uy; 0x38uy;
    0xbfuy; 0x40uy; 0xa3uy; 0x9euy;
    0x81uy; 0xf3uy; 0xd7uy; 0xfbuy;
    0x7cuy; 0xe3uy; 0x39uy; 0x82uy;
    0x9buy; 0x2fuy; 0xffuy; 0x87uy;
    0x34uy; 0x8euy; 0x43uy; 0x44uy;
    0xc4uy; 0xdeuy; 0xe9uy; 0xcbuy;
    0x54uy; 0x7buy; 0x94uy; 0x32uy;
    0xa6uy; 0xc2uy; 0x23uy; 0x3duy;
    0xeeuy; 0x4cuy; 0x95uy; 0x0buy;
    0x42uy; 0xfauy; 0xc3uy; 0x4euy;
    0x08uy; 0x2euy; 0xa1uy; 0x66uy;
    0x28uy; 0xd9uy; 0x24uy; 0xb2uy;
    0x76uy; 0x5buy; 0xa2uy; 0x49uy;
    0x6duy; 0x8buy; 0xd1uy; 0x25uy;
    0x72uy; 0xf8uy; 0xf6uy; 0x64uy;
    0x86uy; 0x68uy; 0x98uy; 0x16uy;
    0xd4uy; 0xa4uy; 0x5cuy; 0xccuy;
    0x5duy; 0x65uy; 0xb6uy; 0x92uy;
    0x6cuy; 0x70uy; 0x48uy; 0x50uy;
    0xfduy; 0xeduy; 0xb9uy; 0xdauy;
    0x5euy; 0x15uy; 0x46uy; 0x57uy;
    0xa7uy; 0x8duy; 0x9duy; 0x84uy;
    0x90uy; 0xd8uy; 0xabuy; 0x00uy;
    0x8cuy; 0xbcuy; 0xd3uy; 0x0auy;
    0xf7uy; 0xe4uy; 0x58uy; 0x05uy;
    0xb8uy; 0xb3uy; 0x45uy; 0x06uy;
    0xd0uy; 0x2cuy; 0x1euy; 0x8fuy;
    0xcauy; 0x3fuy; 0x0fuy; 0x02uy;
    0xc1uy; 0xafuy; 0xbduy; 0x03uy;
    0x01uy; 0x13uy; 0x8auy; 0x6buy;
    0x3auy; 0x91uy; 0x11uy; 0x41uy;
    0x4fuy; 0x67uy; 0xdcuy; 0xeauy;
    0x97uy; 0xf2uy; 0xcfuy; 0xceuy;
    0xf0uy; 0xb4uy; 0xe6uy; 0x73uy;
    0x96uy; 0xacuy; 0x74uy; 0x22uy;
    0xe7uy; 0xaduy; 0x35uy; 0x85uy;
    0xe2uy; 0xf9uy; 0x37uy; 0xe8uy;
    0x1cuy; 0x75uy; 0xdfuy; 0x6euy;
    0x47uy; 0xf1uy; 0x1auy; 0x71uy;
    0x1duy; 0x29uy; 0xc5uy; 0x89uy;
    0x6fuy; 0xb7uy; 0x62uy; 0x0euy;
    0xaauy; 0x18uy; 0xbeuy; 0x1buy;
    0xfcuy; 0x56uy; 0x3euy; 0x4buy;
    0xc6uy; 0xd2uy; 0x79uy; 0x20uy;
    0x9auy; 0xdbuy; 0xc0uy; 0xfeuy;
    0x78uy; 0xcduy; 0x5auy; 0xf4uy;
    0x1fuy; 0xdduy; 0xa8uy; 0x33uy;
    0x88uy; 0x07uy; 0xc7uy; 0x31uy;
    0xb1uy; 0x12uy; 0x10uy; 0x59uy;
    0x27uy; 0x80uy; 0xecuy; 0x5fuy;
    0x60uy; 0x51uy; 0x7fuy; 0xa9uy;
    0x19uy; 0xb5uy; 0x4auy; 0x0duy;
    0x2duy; 0xe5uy; 0x7auy; 0x9fuy;
    0x93uy; 0xc9uy; 0x9cuy; 0xefuy;
    0xa0uy; 0xe0uy; 0x3buy; 0x4duy;
    0xaeuy; 0x2auy; 0xf5uy; 0xb0uy;
    0xc8uy; 0xebuy; 0xbbuy; 0x3cuy;
    0x83uy; 0x53uy; 0x99uy; 0x61uy;
    0x17uy; 0x2buy; 0x04uy; 0x7euy;
    0xbauy; 0x77uy; 0xd6uy; 0x26uy;
    0xe1uy; 0x69uy; 0x14uy; 0x63uy;
    0x55uy; 0x21uy; 0x0cuy; 0x7duy
  ]


let sbox : (b:B.buffer FStar.UInt8.t{B.recallable b /\ B.length b == 256}) = 
  B.gcmalloc_of_list HS.root  [
  0x63uy; 0x7cuy; 0x77uy; 0x7buy; 0xf2uy; 0x6buy; 0x6fuy; 0xc5uy; 0x30uy; 0x01uy; 0x67uy; 0x2buy; 0xfeuy; 0xd7uy; 0xabuy; 0x76uy;
  0xcauy; 0x82uy; 0xc9uy; 0x7duy; 0xfauy; 0x59uy; 0x47uy; 0xf0uy; 0xaduy; 0xd4uy; 0xa2uy; 0xafuy; 0x9cuy; 0xa4uy; 0x72uy; 0xc0uy;
  0xb7uy; 0xfduy; 0x93uy; 0x26uy; 0x36uy; 0x3fuy; 0xf7uy; 0xccuy; 0x34uy; 0xa5uy; 0xe5uy; 0xf1uy; 0x71uy; 0xd8uy; 0x31uy; 0x15uy;
  0x04uy; 0xc7uy; 0x23uy; 0xc3uy; 0x18uy; 0x96uy; 0x05uy; 0x9auy; 0x07uy; 0x12uy; 0x80uy; 0xe2uy; 0xebuy; 0x27uy; 0xb2uy; 0x75uy;
  0x09uy; 0x83uy; 0x2cuy; 0x1auy; 0x1buy; 0x6euy; 0x5auy; 0xa0uy; 0x52uy; 0x3buy; 0xd6uy; 0xb3uy; 0x29uy; 0xe3uy; 0x2fuy; 0x84uy;
  0x53uy; 0xd1uy; 0x00uy; 0xeduy; 0x20uy; 0xfcuy; 0xb1uy; 0x5buy; 0x6auy; 0xcbuy; 0xbeuy; 0x39uy; 0x4auy; 0x4cuy; 0x58uy; 0xcfuy;
  0xd0uy; 0xefuy; 0xaauy; 0xfbuy; 0x43uy; 0x4duy; 0x33uy; 0x85uy; 0x45uy; 0xf9uy; 0x02uy; 0x7fuy; 0x50uy; 0x3cuy; 0x9fuy; 0xa8uy;
  0x51uy; 0xa3uy; 0x40uy; 0x8fuy; 0x92uy; 0x9duy; 0x38uy; 0xf5uy; 0xbcuy; 0xb6uy; 0xdauy; 0x21uy; 0x10uy; 0xffuy; 0xf3uy; 0xd2uy;
  0xcduy; 0x0cuy; 0x13uy; 0xecuy; 0x5fuy; 0x97uy; 0x44uy; 0x17uy; 0xc4uy; 0xa7uy; 0x7euy; 0x3duy; 0x64uy; 0x5duy; 0x19uy; 0x73uy;
  0x60uy; 0x81uy; 0x4fuy; 0xdcuy; 0x22uy; 0x2auy; 0x90uy; 0x88uy; 0x46uy; 0xeeuy; 0xb8uy; 0x14uy; 0xdeuy; 0x5euy; 0x0buy; 0xdbuy;
  0xe0uy; 0x32uy; 0x3auy; 0x0auy; 0x49uy; 0x06uy; 0x24uy; 0x5cuy; 0xc2uy; 0xd3uy; 0xacuy; 0x62uy; 0x91uy; 0x95uy; 0xe4uy; 0x79uy;
  0xe7uy; 0xc8uy; 0x37uy; 0x6duy; 0x8duy; 0xd5uy; 0x4euy; 0xa9uy; 0x6cuy; 0x56uy; 0xf4uy; 0xeauy; 0x65uy; 0x7auy; 0xaeuy; 0x08uy;
  0xbauy; 0x78uy; 0x25uy; 0x2euy; 0x1cuy; 0xa6uy; 0xb4uy; 0xc6uy; 0xe8uy; 0xdduy; 0x74uy; 0x1fuy; 0x4buy; 0xbduy; 0x8buy; 0x8auy;
  0x70uy; 0x3euy; 0xb5uy; 0x66uy; 0x48uy; 0x03uy; 0xf6uy; 0x0euy; 0x61uy; 0x35uy; 0x57uy; 0xb9uy; 0x86uy; 0xc1uy; 0x1duy; 0x9euy;
  0xe1uy; 0xf8uy; 0x98uy; 0x11uy; 0x69uy; 0xd9uy; 0x8euy; 0x94uy; 0x9buy; 0x1euy; 0x87uy; 0xe9uy; 0xceuy; 0x55uy; 0x28uy; 0xdfuy;
  0x8cuy; 0xa1uy; 0x89uy; 0x0duy; 0xbfuy; 0xe6uy; 0x42uy; 0x68uy; 0x41uy; 0x99uy; 0x2duy; 0x0fuy; 0xb0uy; 0x54uy; 0xbbuy; 0x16uy]


// ENCRYPTION 
let op_Array_Access a b = B.index a b
let op_Array_Assignment a b c = B.upd a b c

let access_sbox i = sbox.(uint8_to_uint32 i)
let access_inv_sbox i = inv_sbox.(uint8_to_uint32 i)

private val subBytes_aux_sbox: state:block -> ctr:idx_16 -> STL unit
  (requires (fun h -> live h state))
  (ensures  (fun h0 _ h1 -> live h1 state))
let rec subBytes_aux_sbox state ctr =
  if ctr <> 16ul then 
  begin
    let si = state.(ctr) in
    let si' = access_sbox si in
    state.(ctr) <- si';
    subBytes_aux_sbox state (U32.(ctr +^ 1ul))
  end

private val subBytes_sbox: state:block -> STL unit
  (requires (fun h -> live h state /\ live h sbox))
  (ensures  (fun h0 _ h1 -> live h1 state))
let subBytes_sbox state =
  subBytes_aux_sbox state 0ul

private val shiftRows: state:block -> STL unit
  (requires (fun h -> live h state))
  (ensures  (fun h0 _ h1 -> live h1 state /\ B.modifies (loc_buffer state) h0 h1))
let shiftRows state =
  let open FStar.UInt32 in
  let i = 1ul in
  let tmp = state.(i) in
  state.(i)       <- state.(i+^ 4ul);
  state.(i+^ 4ul) <- state.(i+^ 8ul);
  state.(i+^ 8ul) <- state.(i+^12ul);
  state.(i+^12ul) <- tmp;

  let i = 2ul in
  let tmp = state.(i) in
  state.(i)       <- state.(i+^8ul);
  state.(i+^ 8ul) <- tmp;
  let tmp = state.(i+^4ul) in
  state.(i+^ 4ul) <- state.(i+^12ul);
  state.(i+^12ul) <- tmp;

  let i = 3ul in
  let tmp = state.(i) in
  state.(i)       <- state.(i+^12ul);
  state.(i+^12ul) <- state.(i+^ 8ul);
  state.(i+^ 8ul) <- state.(i+^ 4ul);
  state.(i+^ 4ul) <- tmp

private val mixColumns_: state:block -> c:UInt32.t{v c < 4} -> STL unit
  (requires (fun h -> live h state))
  (ensures  (fun h0 _ h1 -> live h1 state /\ B.modifies (loc_buffer state) h0 h1))
let mixColumns_ state c =
  let s = B.sub state (H32.(4ul*^c)) 4ul in 
  let s0 = s.(0ul) in
  let s1 = s.(1ul) in
  let s2 = s.(2ul) in
  let s3 = s.(3ul) in
  s.(0ul) <- H8.(multiply 0x2uy s0 ^^ multiply 0x3uy s1 ^^ s2 ^^ s3);
  s.(1ul) <- H8.(multiply 0x2uy s1 ^^ multiply 0x3uy s2 ^^ s3 ^^ s0);
  s.(2ul) <- H8.(multiply 0x2uy s2 ^^ multiply 0x3uy s3 ^^ s0 ^^ s1);
  s.(3ul) <- H8.(multiply 0x2uy s3 ^^ multiply 0x3uy s0 ^^ s1 ^^ s2)

#reset-options "--initial_fuel 0 --max_fuel 0"

private val mixColumns: state:block -> STL unit
  (requires (fun h -> live h state))
  (ensures  (fun h0 _ h1 -> live h1 state /\ B.modifies (loc_buffer state) h0 h1))
let mixColumns state =
  mixColumns_ state 0ul;
  mixColumns_ state 1ul;
  mixColumns_ state 2ul;
  mixColumns_ state 3ul

#reset-options "--z3rlimit 10 --initial_fuel 0 --max_fuel 0"

private val addRoundKey_: state:block -> w:xkey{disjoint state w} -> rnd -> c:UInt32.t{v c < 4} -> STL unit
  (requires (fun h -> live h state /\ live h w))
  (ensures  (fun h0 _ h1 -> live h1 state /\ B.modifies (loc_buffer state) h0 h1))
let addRoundKey_ state w round c =
  let open FStar.UInt32 in
  let target = B.sub state (4ul*^c) 4ul in 
  let subkey = B.sub w (blocklen*^round +^ 4ul*^c) 4ul in
  let open FStar.UInt8 in 
  target.(0ul) <- target.(0ul) ^^ subkey.(0ul);
  target.(1ul) <- target.(1ul) ^^ subkey.(1ul);
  target.(2ul) <- target.(2ul) ^^ subkey.(2ul);
  target.(3ul) <- target.(3ul) ^^ subkey.(3ul)

private val addRoundKey: state:block -> w:xkey{disjoint state w} -> round:rnd  -> STL unit
  (requires (fun h -> live h state /\ live h w))
  (ensures  (fun h0 _ h1 -> live h1 state /\ B.modifies (loc_buffer state) h0 h1))
let addRoundKey state w round =
  addRoundKey_ state w round 0ul;
  addRoundKey_ state w round 1ul;
  addRoundKey_ state w round 2ul;
  addRoundKey_ state w round 3ul

private val cipher_loop: state:block -> w:xkey{disjoint state w} -> round:rnd -> STL unit
  (requires (fun h -> live h state /\ live h w))
  (ensures  (fun h0 _ h1 -> live h1 state /\ B.modifies (loc_buffer state) h0 h1))
let rec cipher_loop state w round =
  let open FStar.UInt32 in
  if round <> nr then 
  begin
    subBytes_sbox state;   
    shiftRows     state;
    mixColumns    state;
    addRoundKey   state w round;
    cipher_loop   state w (round+^1ul)
  end

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val cipher: out:block -> input:block -> w:xkey -> STL unit
  (requires (fun h -> live h out /\ live h input /\ live h w /\ 
                   disjoint out input /\ disjoint out w))
  (ensures  (fun h0 _ h1 -> live h1 out /\ B.modifies (loc_buffer out) h0 h1))
let cipher out input w =
  push_frame();
  let state = B.alloca 0uy blocklen in // could we use output instead? alignment? 
  blit input 0ul state 0ul blocklen;
  addRoundKey    state w 0ul;
  cipher_loop    state w 1ul;
  subBytes_sbox  state;
  shiftRows      state;
  addRoundKey    state w nr;
  blit state 0ul out 0ul blocklen;
  pop_frame()


// KEY EXPANSION

private val rotWord: word:lbytes 4 -> STL unit
  (requires (fun h -> live h word))
  (ensures  (fun h0 _ h1 -> live h1 word /\ B.modifies (loc_buffer word) h0 h1))
let rotWord word =
  let w0 = word.(0ul) in
  let w1 = word.(1ul) in
  let w2 = word.(2ul) in
  let w3 = word.(3ul) in
  word.(0ul) <- w1;
  word.(1ul) <- w2;
  word.(2ul) <- w3;
  word.(3ul) <- w0

private val subWord: word:lbytes 4 -> STL unit
  (requires (fun h -> live h word))
  (ensures  (fun h0 _ h1 -> live h1 word /\ B.modifies (loc_buffer word) h0 h1))
let subWord word =
  word.(0ul) <- access_sbox word.(0ul);
  word.(1ul) <- access_sbox word.(1ul);
  word.(2ul) <- access_sbox word.(2ul);
  word.(3ul) <- access_sbox word.(3ul)

#reset-options "--z3rlimit 40 --initial_fuel 0 --max_fuel 0"

private val rcon: i:UInt32.t{v i >= 1} -> byte -> Tot byte (decreases (v i))
let rec rcon i tmp =
  if i = 1ul then tmp
  else begin
    let tmp = multiply 0x2uy tmp in
    rcon (U32.(i-^1ul)) tmp
  end

#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

private val keyExpansion_aux_0:w:xkey -> temp:lbytes 4 -> i:UInt32.t{v i < (v xkeylen / 4) /\ v i >= v nk} -> STL unit
  (requires (fun h -> live h w /\ live h temp /\ 
                   disjoint w temp))
  (ensures  (fun h0 _ h1 -> live h1 temp /\ B.modifies (loc_buffer temp) h0 h1))
let keyExpansion_aux_0 w temp j =
  let open FStar.UInt32 in
  let h0 = ST.get() in
  blit w (4ul *^ j -^ 4ul) temp 0ul 4ul;
  if j %^ nk = 0ul then (
    rotWord temp;
    subWord temp;
    let t0 = temp.(0ul) in
    let rc = rcon (j/^nk) 1uy in
    let z = H8.(t0 ^^ rc) in
    temp.(0ul) <- z ) 
  else if j %^ nk = 4ul then 
    subWord temp
  

#reset-options "--z3rlimit 50 --initial_fuel 0 --max_fuel 0"

private val keyExpansion_aux_1: w:xkey -> temp:lbytes 4 -> i:UInt32.t{v i < (v xkeylen / 4) /\ v i >= v nk} -> STL unit
  (requires (fun h -> live h w /\ live h temp /\ disjoint w temp))
  (ensures  (fun h0 _ h1 -> live h1 w /\ B.modifies (loc_buffer w) h0 h1))
let keyExpansion_aux_1 w temp j =
  let open FStar.UInt32 in
  let i = 4ul *^ j in
  let w0 = w.(i +^ 0ul -^ keylen) in
  let w1 = w.(i +^ 1ul -^ keylen) in
  let w2 = w.(i +^ 2ul -^ keylen) in
  let w3 = w.(i +^ 3ul -^ keylen) in
  let t0 = temp.(0ul) in
  let t1 = temp.(1ul) in
  let t2 = temp.(2ul) in
  let t3 = temp.(3ul) in
  w.(i+^0ul) <- H8.(t0 ^^ w0);
  w.(i+^1ul) <- H8.(t1 ^^ w1);
  w.(i+^2ul) <- H8.(t2 ^^ w2);
  w.(i+^3ul) <- H8.(t3 ^^ w3)

private val keyExpansion_aux: w:xkey -> temp:lbytes 4 -> i:UInt32.t{v i <= (v xkeylen / 4) /\ v i >= v nk} -> STL unit
  (requires (fun h -> live h w /\ live h temp /\ disjoint w temp))
  (ensures  (fun h0 _ h1 -> live h1 temp /\ live h1 w /\ B.modifies (loc_union (loc_buffer temp) (loc_buffer w)) h0 h1))
let rec keyExpansion_aux w temp j =
  let open FStar.UInt32 in
  let h0 = ST.get() in
  if j <^ (xkeylen /^ 4ul) then
  begin
    keyExpansion_aux_0 w temp j;
    keyExpansion_aux_1 w temp j;
    keyExpansion_aux w temp (j +^ 1ul)
  end

val keyExpansion: key:skey -> w:xkey -> STL unit
  (requires (fun h -> live h key /\ live h w /\ disjoint key w))
  (ensures  (fun h0 _ h1 -> live h1 w /\ B.modifies (loc_buffer w) h0 h1))
let keyExpansion key w =
  let open FStar.UInt32 in
  push_frame();
  let temp = B.alloca 0uy 4ul in
  blit key 0ul w 0ul keylen;
  keyExpansion_aux w temp nk;
  pop_frame()


// DECRYPTION

private val invSubBytes_aux_sbox: state:block -> ctr:idx_16 -> STL unit
  (requires (fun h -> live h state))
  (ensures  (fun h0 _ h1 -> live h1 state /\ B.modifies (loc_buffer state) h0 h1))
let rec invSubBytes_aux_sbox state ctr =
  if ctr = 16ul then ()
  else begin
    let si = state.(ctr) in
    let si' = access_inv_sbox si in
    state.(ctr) <- si';
    invSubBytes_aux_sbox state (U32.(ctr+^1ul))
  end

private val invSubBytes_sbox: state:block -> STL unit
  (requires (fun h -> live h state))
  (ensures  (fun h0 _ h1 -> live h1 state /\ B.modifies (loc_buffer state) h0 h1))
let invSubBytes_sbox state =
  invSubBytes_aux_sbox state 0ul

private val invShiftRows: state:block -> STL unit
  (requires (fun h -> live h state))
  (ensures  (fun h0 _ h1 -> live h1 state /\ B.modifies (loc_buffer state) h0 h1))
let invShiftRows state =
  let open FStar.UInt32 in
  let i = 3ul in
  let tmp = state.(i) in
  state.(i)       <- state.(i+^4ul);
  state.(i+^4ul)  <- state.(i+^8ul);
  state.(i+^8ul)  <- state.(i+^12ul);
  state.(i+^12ul) <- tmp;

  let i = 2ul in
  let tmp = state.(i) in
  state.(i)       <- state.(i+^8ul);
  state.(i+^8ul)  <- tmp;
  let tmp = state.(i+^4ul) in
  state.(i+^4ul)  <- state.(i+^12ul);
  state.(i+^12ul) <- tmp;

  let i = 1ul in
  let tmp = state.(i) in
  state.(i)       <- state.(i+^12ul);
  state.(i+^12ul) <- state.(i+^8ul);
  state.(i+^8ul)  <- state.(i+^4ul);
  state.(i+^4ul)  <- tmp

private val invMixColumns_: state:block -> c:UInt32.t{v c < 4} -> STL unit
  (requires (fun h -> live h state))
  (ensures  (fun h0 _ h1 -> live h1 state /\ B.modifies (loc_buffer state) h0 h1 ))
let invMixColumns_ state c =
  let s = B.sub state (H32.(4ul*^c)) 4ul in 
  let s0 = s.(0ul) in
  let s1 = s.(1ul) in
  let s2 = s.(2ul) in
  let s3 = s.(3ul) in
  let mix x0 x1 x2 x3 = H8.(multiply 0xeuy x0 ^^ multiply 0xbuy x1 ^^ multiply 0xduy x2 ^^ multiply 0x9uy x3) in
  s.(0ul) <- mix s0 s1 s2 s3;
  s.(1ul) <- mix s1 s2 s3 s0;
  s.(2ul) <- mix s2 s3 s0 s1;
  s.(3ul) <- mix s3 s0 s1 s2

#reset-options "--initial_fuel 0 --max_fuel 0"

private val invMixColumns: state:block -> STL unit
  (requires (fun h -> live h state))
  (ensures  (fun h0 _ h1 -> live h1 state /\ B.modifies (loc_buffer state) h0 h1 ))
let invMixColumns state =
  invMixColumns_ state 0ul;
  invMixColumns_ state 1ul;
  invMixColumns_ state 2ul;
  invMixColumns_ state 3ul

private val inv_cipher_loop: state:block -> w:xkey -> round:UInt32.t{v round <= v nr - 1} -> STL unit
  (requires (fun h -> live h state /\ live h w /\ disjoint state w))
  (ensures  (fun h0 _ h1 -> live h1 state /\ B.modifies (loc_buffer state) h0 h1 ))
let rec inv_cipher_loop state w round =
  let open FStar.UInt32 in
  if round <> 0ul then
  begin
    invShiftRows state;
    invSubBytes_sbox state;
    addRoundKey state w round;
    invMixColumns state;
    inv_cipher_loop state w (round -^ 1ul)
  end

val inv_cipher: out:block -> input:block -> w:xkey -> STL unit
  (requires (fun h -> live h out /\ live h input /\ live h w /\ disjoint out input /\ disjoint out w)) 
  (ensures  (fun h0 _ h1 -> live h1 out /\ B.modifies (loc_buffer out) h0 h1))
let inv_cipher out input w  =
  push_frame();
  let state = B.alloca 0uy blocklen in
  blit input 0ul   state 0ul blocklen;
  addRoundKey      state w nr;
  inv_cipher_loop  state w (U32.(nr -^ 1ul));
  invShiftRows     state;
  invSubBytes_sbox state;
  addRoundKey      state w 0ul;
  blit state 0ul out 0ul blocklen;
  pop_frame()


