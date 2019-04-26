module Hacl.Impl.AES_256

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

// FIPS197 ?
// TODO factor it out in terms of https://en.wikipedia.org/wiki/AES_instruction_set
// see also https://software.intel.com/sites/default/files/article/165683/aes-wp-2012-09-22-v01.pdf

// TODO this is AES256;
// we also need AES128 (nk=4ul, nr=10) and maybe AES192 (nk=6ul,nr=12).


#set-options "--max_fuel 0 --initial_fuel 0 --max_ifuel 0 --initial_ifuel 0"

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

(* Parameters for AES-128 *)
private inline_for_extraction let nb = size 4
private inline_for_extraction let nk = size 8 // 4, 6, or 8
private inline_for_extraction let nr = size 14 // 10, 12, or 14

inline_for_extraction let blocklen = (size 4) *. nb
inline_for_extraction let keylen   = size 4 *. nk
inline_for_extraction let xkeylen  = size 4 *. nb *. (nr +. size 1) // 176, 208, or 240

let lbytes len = lbuffer uint8 len

type block = lbytes blocklen
type skey  = lbytes keylen
type xkey  = lbytes xkeylen

type rnd = r:size_t{v r <= v nr}
type idx_16 = ctr:size_t{v ctr <= 16}

private val xtime: b:uint8 -> Tot uint8
let xtime b =
  (b <<. size 1) ^. (((b >>. size 7) &. u8 1) *. u8 0x1b)

private val multiply: a:uint8 -> b:uint8 -> Tot uint8
let multiply a b =
  ((a *. (b &. u8 1))
  ^. (xtime a *. ((b >>. size 1) &. u8 1))
  ^. (xtime (xtime a) *. ((b >>. size 2) &. u8 1))
  ^. (xtime (xtime (xtime a)) *. ((b >>. size 3) &. u8 1))
  ^. (xtime (xtime (xtime (xtime a))) *. ((b >>. size 4) &. u8 1))
  ^. (xtime (xtime (xtime (xtime (xtime a)))) *. ((b >>. size 5) &. u8 1))
  ^. (xtime (xtime (xtime (xtime (xtime (xtime a))))) *. ((b >>. size 6) &. u8 1))
  ^. (xtime (xtime (xtime (xtime (xtime (xtime (xtime a)))))) *. ((b >>. size 7) &. u8 1)))

// tables for S-box and inv-S-box, derived from GF256 specification.

#set-options "--z3rlimit 20"

inline_for_extraction noextract let inv_sbox_list : l:list uint8{List.Tot.Base.length l == 256} =
  [@ inline_let]
  let l : list FStar.UInt8.t = [
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
  ] in
  [@ inline_let]
  let l = FStar.List.Tot.Base.map Lib.RawIntTypes.u8_from_UInt8 l in
  assert_norm(List.Tot.length l == 256);
  normalize_term(l)

noextract let inv_sbox_seq : Lib.Sequence.lseq uint8 256 =
  Lib.Sequence.createL inv_sbox_list

let inv_sbox : (b:ilbuffer uint8 (size 256){
  recallable b /\ witnessed b inv_sbox_seq
}) =
  createL_global inv_sbox_list

inline_for_extraction noextract let sbox_list : l:list uint8{List.Tot.Base.length l == 256} =
  [@ inline_let]
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
  [@ inline_let]
  let l = FStar.List.Tot.Base.map Lib.RawIntTypes.u8_from_UInt8 l in
  assert_norm(List.Tot.length l == 256);
  normalize_term(l)

noextract let sbox_seq : Lib.Sequence.lseq uint8 256 =
  Lib.Sequence.createL sbox_list

let sbox : (b:ilbuffer uint8 (size 256){
 recallable b /\ witnessed b sbox_seq
}) =
  createL_global sbox_list


// ENCRYPTION
inline_for_extraction noextract
let op_Array_Access #t #u #v a b = index #t #u #v a b
inline_for_extraction noextract
let op_Array_Assignment #t #u a b c = upd #t #u a b c

// Our implementation is not constant time...
let access_sbox (i: uint8) : Stack uint8 (requires (fun _ -> True)) (ensures (fun h0 _ h1 -> modifies0 h0 h1)) =
  let idx = Lib.RawIntTypes.size_from_UInt32
    (FStar.Int.Cast.uint8_to_uint32
      (Lib.RawIntTypes.u8_to_UInt8 i)) in
  assert(v idx <= 256);
  recall_contents sbox sbox_seq;

  sbox.(idx)

let access_inv_sbox (i: uint8) : Stack uint8 (requires (fun _ -> True)) (ensures (fun h0 _ h1 -> modifies0 h0 h1)) =
 let idx = Lib.RawIntTypes.size_from_UInt32
    (FStar.Int.Cast.uint8_to_uint32
      (Lib.RawIntTypes.u8_to_UInt8 i)) in
  assert(v idx <= 256);
  recall_contents inv_sbox inv_sbox_seq;
  inv_sbox.(idx)

private val subBytes_aux_sbox: state:block -> ctr:idx_16 -> Stack unit
  (requires (fun h -> live h state))
  (ensures  (fun h0 _ h1 -> modifies1 state h0 h1))
let rec subBytes_aux_sbox state ctr =
  if ctr <> 16ul then
  begin
    let si = state.(ctr) in
    let si' = access_sbox si in
    state.(ctr) <- si';
    subBytes_aux_sbox state (ctr +. size 1)
  end

private val subBytes_sbox: state:block -> Stack unit
  (requires (fun h -> live h state))
  (ensures  (fun h0 _ h1 -> modifies1 state h0 h1))
let subBytes_sbox state =
  subBytes_aux_sbox state 0ul

private val shiftRows: state:block -> Stack unit
  (requires (fun h -> live h state))
  (ensures  (fun h0 _ h1 -> modifies1 state h0 h1))
let shiftRows state =
  let i = size 1 in
  let tmp = state.(i) in
  state.(i)       <- state.(i+. size 4);
  state.(i+. size 4) <- state.(i+. size 8);
  state.(i+. size 8) <- state.(i+. size 12);
  state.(i+. size 12) <- tmp;

  let i = size 2 in
  let tmp = state.(i) in
  state.(i)       <- state.(i+. size 8);
  state.(i+. size 8) <- tmp;
  let tmp = state.(i+. size 4) in
  state.(i+. size 4) <- state.(i+. size 12);
  state.(i+. size 12) <- tmp;

  let i = size 3 in
  let tmp = state.(i) in
  state.(i)       <- state.(i+. size 12);
  state.(i+. size 12) <- state.(i+. size 8);
  state.(i+. size 8) <- state.(i+. size 4);
  state.(i+. size 4) <- tmp

private val mixColumns_: state:block -> c:size_t{v c < 4} -> Stack unit
  (requires (fun h -> live h state))
  (ensures  (fun h0 _ h1 -> modifies1 state h0 h1))
let mixColumns_ state c =
  let s = sub state (size 4 *. c) (size 4) in
  let s0 = s.(size 0) in
  let s1 = s.(size 1) in
  let s2 = s.(size 2) in
  let s3 = s.(size 3) in
  s.(size 0) <- (multiply (u8 0x2) s0 ^. multiply (u8 0x3) s1 ^. s2 ^. s3);
  s.(size 1) <- (multiply (u8 0x2) s1 ^. multiply (u8 0x3) s2 ^. s3 ^. s0);
  s.(size 2) <- (multiply (u8 0x2) s2 ^. multiply (u8 0x3) s3 ^. s0 ^. s1);
  s.(size 3) <- (multiply (u8 0x2) s3 ^. multiply (u8 0x3) s0 ^. s1 ^. s2)

private val mixColumns: state:block -> Stack unit
  (requires (fun h -> live h state))
  (ensures  (fun h0 _ h1 -> modifies1 state h0 h1))
let mixColumns state =
  mixColumns_ state (size 0);
  mixColumns_ state (size 1);
  mixColumns_ state (size 2);
  mixColumns_ state (size 3)

private val addRoundKey_: state:block -> w:xkey{disjoint state w} -> rnd -> c:size_t{v c < 4}
  -> Stack unit
  (requires (fun h -> live h state /\ live h w))
  (ensures  (fun h0 _ h1 -> modifies1 state h0 h1))
let addRoundKey_ state w round c =
  let target = sub state (size 4 *. c) (size 4) in
  let subkey = sub w (blocklen*.round +. (size 4)*.c) 4ul in
  target.(size 0) <- target.(size 0) ^. subkey.(size 0);
  target.(size 1) <- target.(size 1) ^. subkey.(size 1);
  target.(size 2) <- target.(size 2) ^. subkey.(size 2);
  target.(size 3) <- target.(size 3) ^. subkey.(size 3)

private val addRoundKey: state:block -> w:xkey{disjoint state w} -> round:rnd  -> Stack unit
  (requires (fun h -> live h state /\ live h w))
  (ensures  (fun h0 _ h1 -> modifies1 state h0 h1))
let addRoundKey state w round =
  addRoundKey_ state w round (size 0);
  addRoundKey_ state w round (size 1);
  addRoundKey_ state w round (size 2);
  addRoundKey_ state w round (size 3)

private val cipher_loop: state:block -> w:xkey{disjoint state w} -> round:rnd -> Stack unit
  (requires (fun h -> live h state /\ live h w))
  (ensures  (fun h0 _ h1 -> modifies1 state h0 h1))
let rec cipher_loop state w round =
  if round <> nr then
  begin
    subBytes_sbox state;
    shiftRows     state;
    mixColumns    state;
    addRoundKey   state w round;
    cipher_loop   state w (round+. size 1)
  end

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val cipher: out:block -> input:block -> w:xkey -> Stack unit
  (requires (fun h -> live h out /\ live h input /\ live h w /\
                   disjoint out input /\ disjoint out w))
  (ensures  (fun h0 _ h1 -> modifies1 out h0 h1))
let cipher out input w =
  push_frame();
  let state = create blocklen (u8 0) in // could we use output instead? alignment?
  copy state input;//blit input 0ul state 0ul blocklen;
  addRoundKey    state w 0ul;
  cipher_loop    state w 1ul;
  subBytes_sbox  state;
  shiftRows      state;
  addRoundKey    state w nr;
  copy out state;//blit state 0ul out 0ul blocklen;
  pop_frame()


// KEY EXPANSION

private val rotWord: word:lbytes (size 4) -> Stack unit
  (requires (fun h -> live h word))
  (ensures  (fun h0 _ h1 -> modifies1 word h0 h1))
let rotWord word =
  let w0 = word.(size 0) in
  let w1 = word.(size 1) in
  let w2 = word.(size 2) in
  let w3 = word.(size 3) in
  word.(size 0) <- w1;
  word.(size 1) <- w2;
  word.(size 2) <- w3;
  word.(size 3) <- w0

private val subWord: word:lbytes (size 4) -> Stack unit
  (requires (fun h -> live h word))
  (ensures  (fun h0 _ h1 -> modifies1 word h0 h1))
let subWord word =
  word.(size 0) <- access_sbox word.(size 0);
  word.(size 1) <- access_sbox word.(size 1);
  word.(size 2) <- access_sbox word.(size 2);
  word.(size 3) <- access_sbox word.(size 3)

#reset-options "--z3rlimit 40 --initial_fuel 0 --max_fuel 0"

private val rcon: i:size_t{v i >= 1} -> uint8 -> Tot uint8 (decreases (v i))
let rec rcon i tmp =
  if i = 1ul then tmp
  else begin
    let tmp = multiply (u8 0x2) tmp in
    rcon (i-. size 1) tmp
  end

#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

private val keyExpansion_aux_0:w:xkey -> temp:lbytes (size 4) -> i:size_t{v i < (v xkeylen / 4) /\ v i >= v nk} -> Stack unit
  (requires (fun h -> live h w /\ live h temp /\
                   disjoint w temp))
  (ensures  (fun h0 _ h1 -> modifies1 temp h0 h1))
let keyExpansion_aux_0 w temp j =
  let h0 = ST.get() in
  //blit w (4ul *^ j -^ 4ul) temp 0ul 4ul;
  copy temp (sub w (size 4 *. j -. size 4) (size 4));
  if j %. nk = size 0 then (
    rotWord temp;

    subWord temp;
    let t0 = temp.(size 0) in
    let rc = rcon (j/.nk) (u8 1) in
    let z = t0 ^. rc in
    temp.(size 0) <- z )
  else if j %. nk = size 4 then
    subWord temp


#reset-options "--z3rlimit 50 --initial_fuel 0 --max_fuel 0"

private val keyExpansion_aux_1: w:xkey -> temp:lbytes (size 4) -> i:UInt32.t{v i < (v xkeylen / 4) /\ v i >= v nk} -> Stack unit
  (requires (fun h -> live h w /\ live h temp /\ disjoint w temp))
  (ensures  (fun h0 _ h1 -> modifies1 w h0 h1))
let keyExpansion_aux_1 w temp j =
  let open FStar.UInt32 in
  let i = size 4 *. j in
  let w0 = w.(i +. 0ul -. keylen) in
  let w1 = w.(i +. 1ul -. keylen) in
  let w2 = w.(i +. 2ul -. keylen) in
  let w3 = w.(i +. 3ul -. keylen) in
  let t0 = temp.(size 0) in
  let t1 = temp.(size 1) in
  let t2 = temp.(size 2) in
  let t3 = temp.(size 3) in
  w.(i+. size 0) <- t0 ^. w0;
  w.(i+. size 1) <- t1 ^. w1;
  w.(i+. size 2) <- t2 ^. w2;
  w.(i+. size 3) <- t3 ^. w3

private val keyExpansion_aux: w:xkey -> temp:lbytes (size 4) -> i:size_t{v i <= (v xkeylen / 4) /\ v i >= v nk} -> Stack unit
  (requires (fun h -> live h w /\ live h temp /\ disjoint w temp))
  (ensures  (fun h0 _ h1 -> modifies2 temp w h0 h1))
let rec keyExpansion_aux w temp j =
  if j <. (xkeylen /. size 4) then
  begin
    keyExpansion_aux_0 w temp j;
    keyExpansion_aux_1 w temp j;
    keyExpansion_aux w temp (j +. size 1)
  end

val keyExpansion: key:skey -> w:xkey -> Stack unit
  (requires (fun h -> live h key /\ live h w /\ disjoint key w))
  (ensures  (fun h0 _ h1 -> modifies1 w h0 h1))
let keyExpansion key w =
  push_frame();
  let temp = create (size 4) (u8 0) in
  update_sub w (size 0) keylen key;//blit key 0ul w 0ul keylen;
  keyExpansion_aux w temp nk;
  pop_frame()


// DECRYPTION

private val invSubBytes_aux_sbox: state:block -> ctr:idx_16 -> Stack unit
  (requires (fun h -> live h state))
  (ensures  (fun h0 _ h1 -> modifies1 state h0 h1))
let rec invSubBytes_aux_sbox state ctr =
  if ctr = 16ul then ()
  else begin
    let si = state.(ctr) in
    let si' = access_inv_sbox si in
    state.(ctr) <- si';
    invSubBytes_aux_sbox state (ctr+. size 1)
  end

private val invSubBytes_sbox: state:block -> Stack unit
  (requires (fun h -> live h state))
  (ensures  (fun h0 _ h1 -> modifies1 state h0 h1))
let invSubBytes_sbox state =
  invSubBytes_aux_sbox state 0ul

private val invShiftRows: state:block -> Stack unit
  (requires (fun h -> live h state))
  (ensures  (fun h0 _ h1 -> modifies1 state h0 h1))
let invShiftRows state =
  let i = size 3 in
  let tmp = state.(i) in
  state.(i)       <- state.(i+. size 4);
  state.(i+. size 4)  <- state.(i+. size 8);
  state.(i+. size 8)  <- state.(i+. size 12);
  state.(i+. size 12) <- tmp;

  let i = size 2 in
  let tmp = state.(i) in
  state.(i)       <- state.(i+. size 8);
  state.(i+. size 8)  <- tmp;
  let tmp = state.(i+. size 4) in
  state.(i+. size 4)  <- state.(i+. size 12);
  state.(i+. size 12) <- tmp;

  let i = size 1 in
  let tmp = state.(i) in
  state.(i)       <- state.(i+. size 12);
  state.(i+. size 12) <- state.(i+. size 8);
  state.(i+. size 8)  <- state.(i+. size 4);
  state.(i+. size 4)  <- tmp

private val invMixColumns_: state:block -> c:size_t{v c < 4} -> Stack unit
  (requires (fun h -> live h state))
  (ensures  (fun h0 _ h1 -> modifies1 state h0 h1 ))
let invMixColumns_ state c =
  let s = sub state (size 4 *. c) (size 4) in
  let s0 = s.(size 0) in
  let s1 = s.(size 1) in
  let s2 = s.(size 2) in
  let s3 = s.(size 3) in
  let mix x0 x1 x2 x3 = multiply (u8 0xe) x0 ^. multiply (u8 0xb) x1 ^. multiply (u8 0xd) x2 ^. multiply (u8 0x9) x3 in
  s.(size 0) <- mix s0 s1 s2 s3;
  s.(size 1) <- mix s1 s2 s3 s0;
  s.(size 2) <- mix s2 s3 s0 s1;
  s.(size 3) <- mix s3 s0 s1 s2

#reset-options "--initial_fuel 0 --max_fuel 0"

private val invMixColumns: state:block -> Stack unit
  (requires (fun h -> live h state))
  (ensures  (fun h0 _ h1 -> modifies1 state h0 h1 ))
let invMixColumns state =
  invMixColumns_ state (size 0);
  invMixColumns_ state (size 1);
  invMixColumns_ state (size 2);
  invMixColumns_ state (size 3)

private val inv_cipher_loop: state:block -> w:xkey -> round:size_t{v round <= v nr - 1} -> Stack unit
  (requires (fun h -> live h state /\ live h w /\ disjoint state w))
  (ensures  (fun h0 _ h1 -> modifies1 state h0 h1 ))
let rec inv_cipher_loop state w round =
  if round <> size 0 then
  begin
    invShiftRows state;
    invSubBytes_sbox state;
    addRoundKey state w round;
    invMixColumns state;
    inv_cipher_loop state w (round -. size 1)
  end

#set-options "--z3rlimit 10"

val inv_cipher: out:block -> input:block -> w:xkey -> Stack unit
  (requires (fun h -> live h out /\ live h input /\ live h w /\ disjoint out input /\ disjoint out w))
  (ensures  (fun h0 _ h1 -> modifies1 out h0 h1))
let inv_cipher out input w  =
  push_frame();
  let state = create blocklen (u8 0) in
  copy state input;//blit input 0ul   state 0ul blocklen;
  addRoundKey      state w nr;
  inv_cipher_loop  state w (nr -. size 1);
  invShiftRows     state;
  invSubBytes_sbox state;
  addRoundKey      state w 0ul;
  copy out state;//blit state 0ul out 0ul blocklen;
  pop_frame()
