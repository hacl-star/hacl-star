(* Agile HMAC *)
module EverCrypt.HMAC

open Hacl.HMAC

let compute_sha1 =
  let open Hacl.Hash.SHA1 in
  mk_compute SHA1 legacy_hash legacy_alloca legacy_init legacy_update_multi legacy_update_last legacy_finish

(* This implementation calls into EverCrypt.Hash, which multiplexes
   between Hacl and Vale implementations of SHA2_256 functions depending on
   the static configuration and CPUID *)
let compute_sha2_256 =
  let open Hacl.Hash.SHA2 in
  mk_compute SHA2_256 EverCrypt.Hash.hash_256 alloca_256 init_256 EverCrypt.Hash.update_multi_256
    EverCrypt.Hash.update_last_256 finish_256

let compute_sha2_384 =
  let open Hacl.Hash.SHA2 in
  mk_compute SHA2_384 hash_384 alloca_384 init_384 update_multi_384 update_last_384 finish_384

let compute_sha2_512 =
  let open Hacl.Hash.SHA2 in
  mk_compute SHA2_512 hash_512 alloca_512 init_512 update_multi_512 update_last_512 finish_512

let compute a mac key keylen data datalen =
  match a with
  | SHA1 -> compute_sha1 mac key keylen data datalen
  | SHA2_256 -> compute_sha2_256 mac key keylen data datalen
  | SHA2_384 -> compute_sha2_384 mac key keylen data datalen
  | SHA2_512 -> compute_sha2_512 mac key keylen data datalen
