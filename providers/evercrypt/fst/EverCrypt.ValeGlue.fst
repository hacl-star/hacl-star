(** Wrappers around Vale functions *)
module EverCrypt.ValeGlue

open EverCrypt.Helpers
open C.Failure
open C.Endianness

module U32 = FStar.UInt32

///  SHA256

/// Incremental API
let sha256_init state =
  Vale.Hash.SHA2_256.init state

let sha256_update state data =
  Vale.Hash.SHA2_256.update state data

let sha256_update_multi state data n =
  admit();
  C.Loops.for 0ul n (fun _ _ -> True) (fun i ->
    let b = Buffer.offset data U32.(i *^ 64ul) in
    Vale.Hash.SHA2_256.update state b)

let sha256_update_last state data n =
  Vale.Hash.SHA2_256.update_last state data n

let sha256_finish state hash =
  Vale.Hash.SHA2_256.finish state hash;
  // Reverse byte-order in little-endian hosts
  admit();
  C.Loops.for 0ul 8ul (fun _ _ -> True) (fun i ->
    let out = Buffer.sub hash U32.(i *^ 4ul) 4ul in
    store32_le out (htole32 (load32_be out)))

/// All-in one
let sha256_hash state data len =
  failwith !$"TODO: sha256_hash/Vale"
