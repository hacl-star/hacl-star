open Cryptokit


let generate len =
  let buf = Bytes.create len in
  let rng = Random.system_rng () in
  rng#random_bytes buf 0 len

let write len buf =
  let rng = Random.system_rng () in
  rng#random_bytes buf 0 len
