open Cryptokit

let uint8s_to_bytes s =
  let b = Bytes.create (List.length s) in
  List.iteri (fun i c -> Bytes.set b i (Char.chr c)) s;
  b

let uint8s_from_bytes s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) ((Char.code (Bytes.get s i)) :: l) in
  exp (Bytes.length s - 1) []


let crypto_random len =
  let buf = Bytes.create (Z.to_int len) in
  let rng = Random.hardware_rng () in
  rng#random_bytes buf 0 (Z.to_int len);
  FStar_Pervasives_Native.Some (uint8s_from_bytes buf)

let crypto_random3 len =
  let buf = Bytes.create (Z.to_int len) in
  let rng = Random.hardware_rng () in
  rng#random_bytes buf 0 (Z.to_int len);
  (uint8s_from_bytes buf)

(* let write len buf =
 *   let rng = Random.system_rng () in
 *   rng#random_bytes (uint8s_to_bytes buf) 0 (Z.to_int len);
 *   true *)
