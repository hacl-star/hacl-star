module MerkleTree.New.Low.Hashes

module B = LowStar.Buffer
module U32 = FStar.UInt32

open FStar.Integers
open EverCrypt.Helpers
open Lib.IntTypes

type hash_size_t = n:uint32_t{n > 0ul}
type hash (#hsz:hash_size_t) = b:B.buffer uint8 { B.len b = hsz \/ B.g_is_null b }

