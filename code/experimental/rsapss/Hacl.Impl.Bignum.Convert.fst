module Hacl.Impl.Bignum.Convert

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.PrintBuffer

open Hacl.Impl.Bignum.Core

module Seq = Lib.Sequence
module FSeq = FStar.Seq
module B = FStar.Bytes
module L = FStar.List.Tot
module ST = FStar.HyperStack.ST



#reset-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
val bytes_to_bignum_:
     #len:bn_len
  -> #resLen:bn_len{v len = 8 * v resLen}
  -> input:lbuffer8 len
  -> res:lbignum resLen
  -> Stack unit
    (requires fun h -> live h input /\ live h res /\ disjoint res input)
    (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1)
let bytes_to_bignum_ #len #resLen input res =
  let h0 = ST.get () in
  let inv h1 i = modifies (loc res) h0 h1 in
  Lib.Loops.for 0ul resLen inv
  (fun i ->
    res.(resLen -. i -. 1ul) <- uint_from_bytes_be (sub input (8ul *. i) 8ul)
  )

val bytes_to_bignum:
     #len:bn_len
  -> input:lbuffer8 len
  -> res:lbignum (blocks len 8ul){8 * v (blocks len 8ul) < max_size_t}
  -> Stack unit
    (requires fun h -> live h input /\ live h res /\ disjoint res input)
    (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1)
[@"c_inline"]
let bytes_to_bignum #len input res =
  push_frame ();
  let num_words = blocks len 8ul in
  let tmpLen = 8ul *. num_words in
  let m = len %. 8ul in
  let ind = if m =. 0ul then 0ul else 8ul -. m in

  let tmp = create tmpLen (u8 0) in
  let tmpLen1 = tmpLen -. ind in
  let tmp1 = sub tmp ind tmpLen1 in
  copy tmp1 input;
  bytes_to_bignum_ tmp res;
  pop_frame ()

inline_for_extraction noextract
val bignum_to_bytes_:
     #len:bn_len
  -> #resLen:bn_len{v resLen = 8 * v len}
  -> input:lbignum len
  -> res:lbuffer8 resLen
  -> Stack unit
    (requires fun h -> live h input /\ live h res /\ disjoint res input)
    (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1)
let bignum_to_bytes_ #len #resLen input res =
  let h0 = ST.get () in
  let inv h1 i = modifies (loc res) h0 h1 in
  Lib.Loops.for 0ul len inv
  (fun i ->
    let tmp = input.(len -. i -. 1ul) in
    uint_to_bytes_be (sub res (8ul *. i) 8ul) tmp
  )

val bignum_to_bytes:
     #len:bn_len{v len > 0}
  -> input:lbignum (blocks len 8ul){8 * v (blocks len 8ul) < max_size_t}
  -> res:lbuffer8 len
  -> Stack unit
    (requires fun h -> live h input /\ live h res /\ disjoint res input)
    (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1)
[@"c_inline"]
let bignum_to_bytes #len input res = admit();
  push_frame ();
  let num_words = blocks len 8ul in
  let tmpLen = 8ul *. num_words in
  let m = len %. 8ul in
  let ind = if m =. 0ul then 0ul else 8ul -. m in

  let tmp = create tmpLen (u8 0) in
  bignum_to_bytes_ input tmp;
  let tmpLen1 = tmpLen -. ind in
  let tmp1 = sub tmp ind tmpLen1 in
  copy res tmp1;
  pop_frame ()

// Prints uints64 chunks in little-endian, though inner uint64 chunks
// in big-endian.
val bignum_to_bytes_direct:
     #len:bn_len{8 * v len < max_size_t}
  -> input:lbignum len
  -> res:lbuffer8 (8ul *. len)
  -> Stack unit
    (requires fun h -> live h input /\ live h res /\ disjoint res input)
    (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1)
[@"c_inline"]
let bignum_to_bytes_direct #len input res =
  push_frame ();

  let h0 = ST.get () in
  let inv h1 i = modifies (loc res) h0 h1 in
  Lib.Loops.for 0ul len inv
  (fun i ->
    let tmp = input.(i) in
    uint_to_bytes_be (sub res (8ul *. i) 8ul) tmp
  );

  pop_frame ()

#reset-options



//////// Some debugging, at least for the time being
// Couldn't place it into core as it requires bytes conversion

noextract inline_for_extraction
let debugOn = false

// Prints in big endian, both with respect to uint64 chunks, and within them.
val print_lbignum:
     #aLen:bn_len
  -> a:lbignum aLen
  -> ST unit (requires fun h -> live h a) (ensures fun h0 _ h1 -> h0 == h1)
let print_lbignum #aLen a =
  assume (8 * v aLen < max_size_t);
  push_frame ();
  let bytes_n = aLen *! 8ul in
  let bytes = create bytes_n (uint 0) in
  assume (8 * v aLen < max_size_t);
  let a' = bignum_to_bytes a bytes in
  print_bytes bytes_n bytes;
  pop_frame ();
  admit()

noextract inline_for_extraction
val trace_lbignum:
     #aLen:bn_len
  -> a:lbignum aLen
  -> ST unit (requires fun h -> live h a) (ensures fun h0 _ h1 -> h0 == h1)
let trace_lbignum #aLen a = if debugOn then print_lbignum a else ()

noextract inline_for_extraction
let trace (s:string) = if debugOn then C.String.print (C.String.of_literal s) else ()
