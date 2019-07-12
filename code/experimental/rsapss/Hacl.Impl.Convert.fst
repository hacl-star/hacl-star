module Hacl.Impl.Convert

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.Lib

module ST = FStar.HyperStack.ST

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
val text_to_nat_:
    len:size_t
  -> input:lbytes len
  -> resLen:size_t{v len = 8 * v resLen}
  -> res:lbignum resLen
  -> Stack unit
    (requires fun h -> live h input /\ live h res /\ disjoint res input)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer res) h0 h1)
let text_to_nat_ len input resLen res =
  let h0 = ST.get () in
  let inv h1 i = modifies (loc_buffer res) h0 h1 in
  Lib.Loops.for 0ul resLen inv
  (fun i ->
    res.(resLen -. i -. 1ul) <- uint_from_bytes_be (sub input (8ul *. i) 8ul)
  )

val text_to_nat:
    len:size_t{v len > 0}
  -> input:lbytes len
  -> res:lbignum (blocks len 8ul){8 * v (blocks len 8ul) < max_size_t}
  -> Stack unit
    (requires fun h -> live h input /\ live h res /\ disjoint res input)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer res) h0 h1)
[@"c_inline"]
let text_to_nat len input res =
  push_frame ();
  let num_words = blocks len 8ul in
  let tmpLen = 8ul *. num_words in
  let m = len %. 8ul in
  let ind = if m =. 0ul then 0ul else 8ul -. m in

  let tmp = create tmpLen (u8 0) in
  let tmpLen1 = tmpLen -. ind in
  let tmp1 = sub tmp ind tmpLen1 in
  copy tmp1 len input;
  text_to_nat_ tmpLen tmp num_words res;
  pop_frame ()

inline_for_extraction noextract
val nat_to_text_:
    len:size_t
  -> input:lbignum len
  -> resLen:size_t{v resLen = 8 * v len}
  -> res:lbytes resLen
  -> Stack unit
    (requires fun h -> live h input /\ live h res /\ disjoint res input)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer res) h0 h1)
let nat_to_text_ len input resLen res =
  let h0 = ST.get () in
  let inv h1 i = modifies (loc_buffer res) h0 h1 in
  Lib.Loops.for 0ul len inv
  (fun i ->
    let tmp = input.(len -. i -. 1ul) in
    uint_to_bytes_be (sub res (8ul *. i) 8ul) tmp
  )

val nat_to_text:
    len:size_t{v len > 0}
  -> input:lbignum (blocks len 8ul){8 * v (blocks len 8ul) < max_size_t}
  -> res:lbytes len
  -> Stack unit
    (requires fun h -> live h input /\ live h res /\ disjoint res input)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer res) h0 h1)
[@"c_inline"]
let nat_to_text len input res =
  push_frame ();
  let num_words = blocks len 8ul in
  let tmpLen = 8ul *. num_words in
  let m = len %. 8ul in
  let ind = if m =. 0ul then 0ul else 8ul -. m in

  let tmp = create tmpLen (u8 0) in
  nat_to_text_ num_words input tmpLen tmp;
  let tmpLen1 = tmpLen -. ind in
  let tmp1 = sub tmp ind tmpLen1 in
  copy res len tmp1;
  pop_frame ()
