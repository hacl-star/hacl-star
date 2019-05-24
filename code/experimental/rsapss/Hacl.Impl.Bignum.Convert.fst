module Hacl.Impl.Bignum.Convert

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.Bignum.Core

module Seq = Lib.Sequence
module B = FStar.Bytes
module ST = FStar.HyperStack.ST

#reset-options "--z3rlimit 150 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
val bytes_to_bignum_:
    len:size_t
  -> input:lbuffer8 len
  -> resLen:size_t{v len = 8 * v resLen}
  -> res:lbignum resLen
  -> Stack unit
    (requires fun h -> live h input /\ live h res /\ disjoint res input)
    (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1)
let bytes_to_bignum_ len input resLen res =
  let h0 = ST.get () in
  let inv h1 i = modifies (loc res) h0 h1 in
  Lib.Loops.for 0ul resLen inv
  (fun i ->
    res.(resLen -. i -. 1ul) <- uint_from_bytes_be (sub input (8ul *. i) 8ul)
  )

val bytes_to_bignum:
    len:size_t{v len > 0}
  -> input:lbuffer8 len
  -> res:lbignum (blocks len 8ul){8 * v (blocks len 8ul) < max_size_t}
  -> Stack unit
    (requires fun h -> live h input /\ live h res /\ disjoint res input)
    (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1)
[@"c_inline"]
let bytes_to_bignum len input res =
  push_frame ();
  let num_words = blocks len 8ul in
  let tmpLen = 8ul *. num_words in
  let m = len %. 8ul in
  let ind = if m =. 0ul then 0ul else 8ul -. m in

  let tmp = create tmpLen (u8 0) in
  let tmpLen1 = tmpLen -. ind in
  let tmp1 = sub tmp ind tmpLen1 in
  copy tmp1 input;
  bytes_to_bignum_ tmpLen tmp num_words res;
  pop_frame ()

inline_for_extraction noextract
val bignum_to_bytes_:
    len:size_t
  -> input:lbignum len
  -> resLen:size_t{v resLen = 8 * v len}
  -> res:lbuffer8 resLen
  -> Stack unit
    (requires fun h -> live h input /\ live h res /\ disjoint res input)
    (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1)
let bignum_to_bytes_ len input resLen res =
  let h0 = ST.get () in
  let inv h1 i = modifies (loc res) h0 h1 in
  Lib.Loops.for 0ul len inv
  (fun i ->
    let tmp = input.(len -. i -. 1ul) in
    uint_to_bytes_be (sub res (8ul *. i) 8ul) tmp
  )

val bignum_to_bytes:
    len:size_t{v len > 0}
  -> input:lbignum (blocks len 8ul){8 * v (blocks len 8ul) < max_size_t}
  -> res:lbuffer8 len
  -> Stack unit
    (requires fun h -> live h input /\ live h res /\ disjoint res input)
    (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1)
[@"c_inline"]
let bignum_to_bytes len input res = admit();
  push_frame ();
  let num_words = blocks len 8ul in
  let tmpLen = 8ul *. num_words in
  let m = len %. 8ul in
  let ind = if m =. 0ul then 0ul else 8ul -. m in

  let tmp = create tmpLen (u8 0) in
  bignum_to_bytes_ num_words input tmpLen tmp;
  let tmpLen1 = tmpLen -. ind in
  let tmp1 = sub tmp ind tmpLen1 in
  copy res tmp1;
  pop_frame ()

// This version does not work, because of the internal rec I think.
//
//inline_for_extraction noextract
//val nat_to_list64: nat -> list pub_uint64
//let nat_to_list64 x =
//  [@inline_let]
//  let rec go (y: nat) =
//    if y <= maxint U64
//    then [uint y]
//    else uint (y % 64) :: go (y / 64)kin
//  go x


inline_for_extraction noextract
val nat_to_list64: nat -> list pub_uint64
let rec nat_to_list64 y = admit();
    if y <= maxint U64
    then [uint y]
    else uint (y % 64) :: nat_to_list64 (y / 64)

inline_for_extraction noextract
val nat_to_list64_sec: nat -> list uint64
let nat_to_list64_sec x = List.Tot.map secret (nat_to_list64 x)

inline_for_extraction noextract
val nat_bytes_num: nat -> size_t
let nat_bytes_num x = admit(); normalize_term (size (List.Tot.length (nat_to_list64_sec x)))


inline_for_extraction noextract
val nat_to_bignum_exact:
     input:nat
  -> StackInline (lbignum (nat_bytes_num input))
    (requires fun _ -> true)
    (ensures  fun h0 b h1 -> modifies (loc b) h0 h1)
let nat_to_bignum_exact input =
  [@inline_let]
  let l: list uint64 = normalize_term (nat_to_list64_sec input) in
  assume (List.Tot.length l <= max_size_t);
  assume (normalize (List.Tot.length l <= max_size_t));
  [@inline_let]
  let len: size_t = nat_bytes_num input in
  admit();
  createL l


inline_for_extraction noextract
val nat_to_bignum:
     #k:size_t{v k > 0}
  -> input:nat { v (nat_bytes_num input) <= v k }
  -> StackInline (lbignum k)
    (requires fun _ -> true)
    (ensures  fun h0 b h1 -> modifies (loc b) h0 h1)
let nat_to_bignum #k input =
  admit();
  push_frame ();

  let len: size_t = nat_bytes_num input in
  let created: lbignum len = nat_to_bignum_exact input in
  let res: lbignum k = create k (u64 0) in
  let res_sub: lbignum len = sub res 0ul len in

  let h0 = ST.get () in
  copy res_sub created;
  pop_frame ();
  res
