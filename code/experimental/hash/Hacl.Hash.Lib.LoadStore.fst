module Hacl.Hash.Lib.LoadStore

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.ST
open FStar.Buffer

open Hacl.Spec.Endianness

open Hacl.Cast
open Hacl.UInt8
open Hacl.UInt32
open FStar.UInt32


(* Definition of aliases for modules *)
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64

module H8 = Hacl.UInt8
module H32 = Hacl.UInt32
module H64 = Hacl.UInt64

module Cast = Hacl.Cast


(* Definition of base types *)
let uint8_t   = FStar.UInt8.t
let uint32_t  = FStar.UInt32.t
let uint64_t  = FStar.UInt64.t

let huint8_t  = Hacl.UInt8.t
let huint32_t = Hacl.UInt32.t
let huint64_t = Hacl.UInt64.t

let huint8_p  = Buffer.buffer huint8_t
let huint32_p = Buffer.buffer huint32_t
let huint64_p = Buffer.buffer huint64_t


(* Definitions of aliases for functions *)
inline_for_extraction let u8_to_s8 = Cast.uint8_to_sint8
inline_for_extraction let u32_to_s32 = Cast.uint32_to_sint32
inline_for_extraction let u32_to_s64 = Cast.uint32_to_sint64
inline_for_extraction let s32_to_s8  = Cast.sint32_to_sint8
inline_for_extraction let s32_to_s64 = Cast.sint32_to_sint64
inline_for_extraction let u64_to_s64 = Cast.uint64_to_sint64


val load32s_be:
  buf_32 :Buffer.buffer Hacl.UInt32.t ->
  buf_8  :Buffer.buffer Hacl.UInt8.t {length buf_8 = 4 * length buf_32} ->
  len_8 :FStar.UInt32.t{v len_8 = length buf_8} ->
  Stack unit
        (requires (fun h0 -> live h0 buf_32 /\ live h0 buf_8))
        (ensures  (fun h0 _ h1 -> live h0 buf_32 /\ live h0 buf_8 /\ live h1 buf_32 /\ modifies_1 buf_32 h0 h1
                  /\ (reveal_h32s (as_seq h1 buf_32) == Spec.Lib.uint32s_from_be (length buf_32) (reveal_sbytes (as_seq h0 buf_8)))))

let rec load32s_be buf_32 buf_8 len_8 =
  admit();
  if FStar.UInt32.(len_8 =^ 0ul) then ()
  else
    begin
      let x_8 = Buffer.sub buf_8 FStar.UInt32.(len_8 -^ 4ul) 4ul in
      let i_32 = len_8 /^ 4ul in
      let x_32 = Hacl.Endianness.hload32_be x_8 in
      Buffer.upd buf_32 FStar.UInt32.(i_32 -^ 1ul) x_32;
      load32s_be buf_32 buf_8 FStar.UInt32.(len_8 -^ 4ul)
    end

#set-options "--max_fuel 1 --max_ifuel 0 --z3rlimit 100"

val store32s_be:
  buf_8  :Buffer.buffer Hacl.UInt8.t ->
  buf_32 :Buffer.buffer Hacl.UInt32.t {length buf_32 * 4 = length buf_8}->
  len_32 :FStar.UInt32.t{FStar.UInt32.v len_32 = length buf_32 } ->
  Stack unit
        (requires (fun h0 -> live h0 buf_8 /\ live h0 buf_32))
        (ensures  (fun h0 _ h1 -> live h0 buf_32 /\ live h0 buf_8 /\ live h1 buf_8 /\ modifies_1 buf_8 h0 h1
                  /\ (reveal_sbytes (as_seq h1 buf_8) == Spec.Lib.uint32s_to_be (length buf_32) (reveal_h32s (as_seq h0 buf_32)))))

let rec store32s_be buf_8 buf_32 len_32 =
  admit();
  if FStar.UInt32.(len_32 =^ 0ul) then ()
  else
    begin
      let x_32 = Buffer.index buf_32 FStar.UInt32.(len_32 -^ 1ul) in
      let x_8 = Buffer.sub buf_8 FStar.UInt32.((len_32 -^ 1ul) *^ 4ul) 4ul in
      Hacl.Endianness.hstore32_be x_8 x_32;
      store32s_be buf_8 buf_32 FStar.UInt32.(len_32 -^ 1ul)
    end


#set-options "--max_fuel 1 --max_ifuel 0 --z3rlimit 50"
val load64s_be:
  buf_64 :Buffer.buffer Hacl.UInt64.t ->
  buf_8  :Buffer.buffer Hacl.UInt8.t {length buf_8 = 8 * length buf_64} ->
  len_8 :FStar.UInt32.t{v len_8 = length buf_8} ->
  Stack unit
        (requires (fun h0 -> live h0 buf_64 /\ live h0 buf_8))
        (ensures  (fun h0 _ h1 -> live h0 buf_64 /\ live h0 buf_8 /\ live h1 buf_64 /\ modifies_1 buf_64 h0 h1
                  /\ (reveal_h64s (as_seq h1 buf_64) == Spec.Lib.uint64s_from_be (length buf_64) (reveal_sbytes (as_seq h0 buf_8)))))

#set-options "--max_fuel 1 --max_ifuel 0 --z3rlimit 100"

let rec load64s_be buf_64 buf_8 len_8 =
  admit();
  if FStar.UInt32.(len_8 =^ 0ul) then ()
  else
    begin
      let x_8 = Buffer.sub buf_8 FStar.UInt32.(len_8 -^ 8ul) 8ul in
      let i_64 = len_8 /^ 8ul in
      let x_64 = Hacl.Endianness.hload64_be x_8 in
      Buffer.upd buf_64 FStar.UInt32.(i_64 -^ 1ul) x_64;
      load64s_be buf_64 buf_8 FStar.UInt32.(len_8 -^ 8ul)
    end


#set-options "--max_fuel 1 --max_ifuel 0 --z3rlimit 100"

val store64s_be:
  buf_8  :Buffer.buffer Hacl.UInt8.t ->
  buf_64 :Buffer.buffer Hacl.UInt64.t {length buf_64 * 8 = length buf_8}->
  len_64 :FStar.UInt32.t{FStar.UInt32.v len_64 = length buf_64 } ->
  Stack unit
        (requires (fun h0 -> live h0 buf_8 /\ live h0 buf_64))
        (ensures  (fun h0 _ h1 -> live h0 buf_64 /\ live h0 buf_8 /\ live h1 buf_8 /\ modifies_1 buf_8 h0 h1
                  /\ (reveal_sbytes (as_seq h1 buf_8) == Spec.Lib.uint64s_to_be (length buf_64) (reveal_h64s (as_seq h0 buf_64)))))

let rec store64s_be buf_8 buf_64 len_64 =
  admit();
  if FStar.UInt32.(len_64 =^ 0ul) then ()
  else
    begin
      let x_64 = Buffer.index buf_64 FStar.UInt32.(len_64 -^ 1ul) in
      let x_8 = Buffer.sub buf_8 FStar.UInt32.((len_64 -^ 1ul) *^ 8ul) 8ul in
      Hacl.Endianness.hstore64_be x_8 x_64;
      store64s_be buf_8 buf_64 FStar.UInt32.(len_64 -^ 1ul)
    end
