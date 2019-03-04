module Hacl.Endianness

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Old.Endianness
open Hacl.Spec.Endianness
open FStar.Buffer


module U8   = FStar.UInt8
module U16  = FStar.UInt16
module U32  = FStar.UInt32
module U64  = FStar.UInt64
module U128 = FStar.UInt128

module H8   = Hacl.UInt8
module H16  = Hacl.UInt16
module H32  = Hacl.UInt32
module H64  = Hacl.UInt64
module H128 = Hacl.UInt128

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 5"

open C.Compat.Endianness

// Byte-level functions
unfold inline_for_extraction let htole16 x = htole16 x
unfold inline_for_extraction let le16toh x = le16toh x
unfold inline_for_extraction let htole32 x = htole32 x
unfold inline_for_extraction let le32toh x = le32toh x
unfold inline_for_extraction let htole64 x = htole64 x
unfold inline_for_extraction let le64toh x = le64toh x

unfold inline_for_extraction let htobe16 x = htobe16 x
unfold inline_for_extraction let be16toh x = be16toh x
unfold inline_for_extraction let htobe32 x = htobe32 x
unfold inline_for_extraction let be32toh x = be32toh x
unfold inline_for_extraction let htobe64 x = htobe64 x
unfold inline_for_extraction let be64toh x = be64toh x


[@"substitute" ]
val store32_le:
  b:buffer U8.t{length b = 4} ->
  z:U32.t ->
  Stack unit
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ Buffer.live h1 b
      /\ little_endian (as_seq h1 b) = U32.v z))

[@"substitute" ]
val load32_le:
  b:buffer U8.t{length b = 4} ->
  Stack U32.t
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ live h1 b
      /\ little_endian (as_seq h0 b) = U32.v z))

[@"substitute" ]
val store32_be:
  b:buffer U8.t{length b = 4} ->
  z:U32.t ->
  Stack unit
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ Buffer.live h1 b
      /\ big_endian (as_seq h1 b) = U32.v z))

[@"substitute" ]
val load32_be:
  b:buffer U8.t{length b = 4} ->
  Stack U32.t
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ live h1 b
      /\ big_endian (as_seq h0 b) = U32.v z))

[@"substitute" ]
val store64_le:
  b:buffer U8.t{length b = 8} ->
  z:U64.t ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b /\ little_endian (as_seq h1 b) = U64.v z))

[@"substitute" ]
val load64_le:
  b:buffer U8.t{length b = 8} ->
  Stack U64.t
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ live h1 b /\ little_endian (as_seq h0 b) = U64.v z))

[@"substitute" ]
val store64_be:
  b:buffer U8.t{length b = 8} ->
  z:U64.t ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b /\ big_endian (as_seq h1 b) = U64.v z))

[@"substitute" ]
val load64_be:
  b:buffer U8.t{length b = 8} ->
  Stack U64.t
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ live h0 b /\ big_endian (as_seq h0 b) = U64.v z))

[@"substitute" ]
val load128_le:
  b:buffer U8.t{length b = 16} ->
  Stack U128.t
    (requires (fun h -> live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ live h0 b /\ little_endian (as_seq h0 b) = U128.v z))

[@"substitute" ]
val store128_le:
  b:buffer U8.t{length b = 16} ->
  z:U128.t ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b /\ little_endian (as_seq h1 b) = U128.v z))

[@"substitute" ]
val load128_be:
  b:buffer U8.t{length b = 16} ->
  Stack U128.t
    (requires (fun h -> live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ live h0 b /\ big_endian (as_seq h0 b) = U128.v z))

[@"substitute" ]
val store128_be:
  b:buffer U8.t{length b = 16} ->
  z:U128.t ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b /\ big_endian (as_seq h1 b) = U128.v z))

[@"substitute" ]
val hstore32_le:
  b:buffer H8.t{length b = 4} ->
  z:H32.t ->
  Stack unit
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ Buffer.live h1 b
      /\ hlittle_endian (as_seq h1 b) = H32.v z))

[@"substitute" ]
val hload32_le:
  b:buffer H8.t{length b = 4} ->
  Stack H32.t
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ live h1 b
      /\ hlittle_endian (as_seq h0 b) = H32.v z))

[@"substitute" ]
val hstore32_be:
  b:buffer H8.t{length b = 4} ->
  z:H32.t ->
  Stack unit
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ Buffer.live h1 b
      /\ hbig_endian (as_seq h1 b) = H32.v z))

[@"substitute" ]
val hload32_be:
  b:buffer H8.t{length b = 4} ->
  Stack H32.t
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ live h1 b
      /\ hbig_endian (as_seq h0 b) = H32.v z))

[@"substitute" ]
val hstore64_le:
  b:buffer H8.t{length b = 8} ->
  z:H64.t ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b /\ hlittle_endian (as_seq h1 b) = H64.v z))

[@"substitute" ]
val hload64_le:
  b:buffer H8.t{length b = 8} ->
  Stack H64.t
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ live h1 b /\ hlittle_endian (as_seq h0 b) = H64.v z))

[@"substitute" ]
val hstore64_be:
  b:buffer H8.t{length b = 8} ->
  z:H64.t ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b /\ hbig_endian (as_seq h1 b) = H64.v z))

[@"substitute" ]
val hload64_be:
  b:buffer H8.t{length b = 8} ->
  Stack H64.t
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ live h0 b /\ hbig_endian (as_seq h0 b) = H64.v z))

[@"substitute" ]
val hstore128_le:
  b:buffer H8.t{length b = 16} ->
  z:H128.t ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b /\ hlittle_endian (as_seq h1 b) = H128.v z))
    
[@"substitute" ]
val hload128_le:
  b:buffer H8.t{length b = 16} ->
  Stack H128.t
    (requires (fun h -> live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ live h0 b /\ hlittle_endian (as_seq h0 b) = H128.v z))

[@"substitute" ]
val hstore128_be:
  b:buffer H8.t{length b = 16} ->
  z:H128.t ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b /\ hbig_endian (as_seq h1 b) = H128.v z))
    
[@"substitute" ]
val hload128_be:
  b:buffer H8.t{length b = 16} ->
  Stack H128.t
    (requires (fun h -> live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ live h0 b /\ hbig_endian (as_seq h0 b) = H128.v z))

#set-options "--lax"

(**
 * REMARK
 * These functions are implemented in C in Kremlin's library and trusted.
 * Their assumed specifications in Kremlin's C.fst only specify their memory
 * footprint and not their functional behaviour, so we can't prove the richer
 * specifications given here.
**)

[@"substitute" ]
let store32_le b z  = store32_le b z
[@"substitute" ]
let store32_be b z  = store32_be b z
[@"substitute" ]
let store64_le b z  = store64_le b z
[@"substitute" ]
let store64_be b z  = store64_be b z
[@"substitute" ]
let store128_le b z = store128_le b z
[@"substitute" ]
let store128_be b z = store128_be b z


[@"substitute" ]
let load32_le b  = load32_le b
[@"substitute" ]
let load32_be b  = load32_be b
[@"substitute" ]
let load64_le b  = load64_le b
[@"substitute" ]
let load64_be b  = load64_be b
[@"substitute" ]
let load128_le b = load128_le b
[@"substitute" ]
let load128_be b = load128_be b

#reset-options

[@"substitute" ]
let hstore32_le b z  = store32_le b z
[@"substitute" ]
let hstore32_be b z  = store32_be b z
[@"substitute" ]
let hstore64_le b z  = store64_le b z
[@"substitute" ]
let hstore64_be b z  = store64_be b z
[@"substitute" ]
let hstore128_le b z = store128_le b z
[@"substitute" ]
let hstore128_be b z = store128_be b z

[@"substitute" ]
let hload32_le b  = load32_le b
[@"substitute" ]
let hload32_be b  = load32_be b
[@"substitute" ]
let hload64_le b  = load64_le b
[@"substitute" ]
let hload64_be b  = load64_be b
[@"substitute" ]
let hload128_le b = load128_le b
[@"substitute" ]
let hload128_be b = load128_be b
