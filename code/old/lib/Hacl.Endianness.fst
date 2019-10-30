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

// Byte-level functions
assume val htole16: UInt16.t -> Tot UInt16.t
assume val le16toh: UInt16.t -> Tot UInt16.t

assume val htole32: UInt32.t -> Tot UInt32.t
assume val le32toh: UInt32.t -> Tot UInt32.t

assume val htole64: UInt64.t -> Tot UInt64.t
assume val le64toh: UInt64.t -> Tot UInt64.t

assume val htobe16: UInt16.t -> Tot UInt16.t
assume val be16toh: UInt16.t -> Tot UInt16.t

assume val htobe32: UInt32.t -> Tot UInt32.t
assume val be32toh: UInt32.t -> Tot UInt32.t

assume val htobe64: UInt64.t -> Tot UInt64.t
assume val be64toh: UInt64.t -> Tot UInt64.t

assume val store32_le:
  b:buffer U8.t{length b = 4} ->
  z:U32.t ->
  Stack unit
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ Buffer.live h1 b
      /\ little_endian (as_seq h1 b) = U32.v z))

assume val load32_le:
  b:buffer U8.t{length b = 4} ->
  Stack U32.t
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ live h1 b
      /\ little_endian (as_seq h0 b) = U32.v z))

assume val store32_be:
  b:buffer U8.t{length b = 4} ->
  z:U32.t ->
  Stack unit
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ Buffer.live h1 b
      /\ big_endian (as_seq h1 b) = U32.v z))

assume val load32_be:
  b:buffer U8.t{length b = 4} ->
  Stack U32.t
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ live h1 b
      /\ big_endian (as_seq h0 b) = U32.v z))

assume val load64_le:
  b:buffer U8.t{length b = 8} ->
  Stack U64.t
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ live h1 b /\ little_endian (as_seq h0 b) = U64.v z))

assume val store64_le:
  b:buffer U8.t{length b = 8} ->
  z:U64.t ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b /\ little_endian (as_seq h1 b) = U64.v z))

assume val load64_be:
  b:buffer U8.t{length b = 8} ->
  Stack U64.t
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ live h0 b /\ big_endian (as_seq h0 b) = U64.v z))

assume val store64_be:
  b:buffer U8.t{length b = 8} ->
  z:U64.t ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b /\ big_endian (as_seq h1 b) = U64.v z))

assume val load128_le:
  b:buffer U8.t{length b = 16} ->
  Stack U128.t
    (requires (fun h -> live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ live h0 b /\ little_endian (as_seq h0 b) = U128.v z))

assume val store128_le:
  b:buffer U8.t{length b = 16} ->
  z:U128.t ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b /\ little_endian (as_seq h1 b) = U128.v z))

assume val load128_be:
  b:buffer U8.t{length b = 16} ->
  Stack U128.t
    (requires (fun h -> live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ live h0 b /\ big_endian (as_seq h0 b) = U128.v z))

assume val store128_be:
  b:buffer U8.t{length b = 16} ->
  z:U128.t ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b /\ big_endian (as_seq h1 b) = U128.v z))

assume val hstore32_le:
  b:buffer H8.t{length b = 4} ->
  z:H32.t ->
  Stack unit
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ Buffer.live h1 b
      /\ hlittle_endian (as_seq h1 b) = H32.v z))

assume val hload32_le:
  b:buffer H8.t{length b = 4} ->
  Stack H32.t
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ live h1 b
      /\ hlittle_endian (as_seq h0 b) = H32.v z))

assume val hstore32_be:
  b:buffer H8.t{length b = 4} ->
  z:H32.t ->
  Stack unit
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ Buffer.live h1 b
      /\ hlittle_endian (as_seq h1 b) = H32.v z))

assume val hload32_be:
  b:buffer H8.t{length b = 4} ->
  Stack H32.t
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ live h1 b
      /\ hlittle_endian (as_seq h0 b) = H32.v z))

assume val hload64_le:
  b:buffer H8.t{length b = 8} ->
  Stack H64.t
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ live h1 b /\ hlittle_endian (as_seq h0 b) = H64.v z))

assume val hstore64_le:
  b:buffer H8.t{length b = 8} ->
  z:H64.t ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b /\ hlittle_endian (as_seq h1 b) = H64.v z))

assume val hload64_be:
  b:buffer H8.t{length b = 8} ->
  Stack H64.t
    (requires (fun h -> Buffer.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ live h0 b /\ hbig_endian (as_seq h0 b) = H64.v z))

assume val hstore64_be:
  b:buffer H8.t{length b = 8} ->
  z:H64.t ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b /\ hbig_endian (as_seq h1 b) = H64.v z))

assume val hload128_le:
  b:buffer H8.t{length b = 16} ->
  Stack H128.t
    (requires (fun h -> live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ live h0 b /\ hlittle_endian (as_seq h0 b) = H128.v z))

assume val hstore128_le:
  b:buffer H8.t{length b = 16} ->
  z:H128.t ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b /\ hlittle_endian (as_seq h1 b) = H128.v z))

assume val hload128_be:
  b:buffer H8.t{length b = 16} ->
  Stack H128.t
    (requires (fun h -> live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ live h0 b /\ hbig_endian (as_seq h0 b) = H128.v z))

assume val hstore128_be:
  b:buffer H8.t{length b = 16} ->
  z:H128.t ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b /\ hbig_endian (as_seq h1 b) = H128.v z))
