module Hacl.Types

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

type u8    = FStar.UInt8.t
type u16   = FStar.UInt16.t
type u32   = FStar.UInt32.t
type u64   = FStar.UInt64.t
type u128  = FStar.UInt128.t

type h8    = Hacl.UInt8.t
type h16   = Hacl.UInt16.t
type h32   = Hacl.UInt32.t
type h64   = Hacl.UInt64.t
type h128  = Hacl.UInt128.t

type uint8_p = FStar.Buffer.buffer h8
type uint8_pl (l:nat) = b:FStar.Buffer.buffer h8{FStar.Buffer.length b = l}
type uint32_p = FStar.Buffer.buffer h32
type uint32_pl (l:nat) = b:FStar.Buffer.buffer h32{FStar.Buffer.length b = l}
type uint64_p = FStar.Buffer.buffer h64
type uint64_pl (l:nat) = b:FStar.Buffer.buffer h64{FStar.Buffer.length b = l}
