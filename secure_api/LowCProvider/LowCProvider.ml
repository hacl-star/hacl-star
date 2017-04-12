type bytes = Platform.Bytes.bytes
let string_of_bytes b = Platform.Bytes.get_cbytes b
let bytes_of_string s = Platform.Bytes.abytes s
let (@|) = Platform.Bytes.(@|)

(* -------------------------------------------------------------------- *)

type aead_cipher = CoreCrypto.aead_cipher
let aeadKeySize = CoreCrypto.aeadKeySize
let aeadRealIVSize = CoreCrypto.aeadRealIVSize
let aeadTagSize = CoreCrypto.aeadTagSize

type aead_state
type aes_impl =
  | HaclAES
  | ValeAES

external ocaml_AEAD_create: aead_cipher -> aes_impl -> string -> aead_state = "ocaml_AEAD_create"
external ocaml_AEAD_encrypt: aead_state -> string -> string -> string -> string = "ocaml_AEAD_encrypt"
external ocaml_AEAD_decrypt: aead_state -> string -> string -> string -> string option = "ocaml_AEAD_decrypt"

let aead_create (c:aead_cipher) (i:aes_impl) (k:bytes) =
  ocaml_AEAD_create c i (string_of_bytes k)

let aead_encrypt (st:aead_state) (iv:bytes) (ad:bytes) (d:bytes) =
  let c = ocaml_AEAD_encrypt st (string_of_bytes iv) (string_of_bytes ad) (string_of_bytes d) in
  bytes_of_string c

let aead_decrypt (st:aead_state) (iv:bytes) (ad:bytes) (c:bytes) =
  match ocaml_AEAD_decrypt st (string_of_bytes iv) (string_of_bytes ad) (string_of_bytes c) with
  | None -> None
  | Some plain -> Some (bytes_of_string plain)

