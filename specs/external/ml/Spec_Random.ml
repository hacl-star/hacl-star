open Cryptokit


let generate len =
  let buf = Bytes.create (Z.to_int len) in
  let rng = Random.system_rng () in
  rng#random_bytes buf 0 (Z.to_int len);
  buf

let write len buf =
  let rng = Random.system_rng () in
  rng#random_bytes buf 0 (Z.to_int len)
