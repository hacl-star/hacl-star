open Cryptokit

type entropy = int

let uint8s_to_bytes s =
  let b = Bytes.create (List.length s) in
  List.iteri (fun i c -> Bytes.set b i (Char.chr c)) s;
  b

let uint8s_from_bytes: bytes -> (FStar_UInt8.t, unit) Lib_Sequence.lseq =
  fun s ->
  let rec exp i l =
    if i < 0 then l else exp (i - 1) ((Char.code (Bytes.get s i)) :: l) in
  FStar_Seq_Properties.seq_of_list (exp (Bytes.length s - 1) [])

let entropy0 = 0

let crypto_random : entropy -> Prims.int -> (entropy * (FStar_UInt8.t, unit) Lib_Sequence.lseq) =
  fun _ ->
    fun len ->
      let buf = Bytes.create (Z.to_int len) in
      let rng = Random.hardware_rng () in
      rng#random_bytes buf 0 (Z.to_int len);
      0,(uint8s_from_bytes buf)


let unsound_crypto_random1 : Prims.int -> (FStar_UInt8.t, unit) Lib_Sequence.lseq
                                  FStar_Pervasives_Native.option =
  fun len ->
    let buf = Bytes.create (Z.to_int len) in
    let rng = Random.hardware_rng () in
    rng#random_bytes buf 0 (Z.to_int len);
    FStar_Pervasives_Native.Some (uint8s_from_bytes buf)

let unsound_crypto_random2 : Prims.int -> (FStar_UInt8.t, unit) Lib_Sequence.lseq =
  fun len ->
    let buf = Bytes.create (Z.to_int len) in
    let rng = Random.hardware_rng () in
    rng#random_bytes buf 0 (Z.to_int len);
    (uint8s_from_bytes buf)
