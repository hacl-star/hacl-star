open Prims
open Yojson
open Yojson.Basic.Util
module HPKE = Spec_Agile_HPKE

(* Structure of test vector JSON file:
mode: 0
kem_id: 32
kdf_id: 1
aead_id: 1
info: 4f6465206f6e2061204772656369616e2055726e
ikmE: 1dacee520c81ade608f4fa3e5ccae0ecedcc7880e3fc6f3e5afd2e4af8396571
pkEm: 890e346283bf75af9d786a526c4a191b84d0110c794b6aa7e9a0b6205fe2c10c
skEm: ee9fcf08d07241b13b93f2cf6dbdd56f94e940d788c3e4c860f757a08974a883
ikmR: 0a3367dadc97e200074936b5adedcd5680f30672d1ec7158fdfcb795040ec909
pkRm: 8bd766c487fa9266ce3ac898827439aea2fa9c0099ab62da954b06f979f2141b
skRm: c867f27c253f720c7074f9b4a495f2c690060629e249f86991bb55edf804f7bd
enc: 890e346283bf75af9d786a526c4a191b84d0110c794b6aa7e9a0b6205fe2c10c
shared_secret:
85a44c9238b103cdaa67ec6ffde55d8f2e75e49aefcf1ade3c65900bddd503f2
key_schedule_context: 00725611c9d98c07c03f60095cd32d400d8347d45ed67097bb
ad50fc56da742d07cb6cffde367bb0565ba28bb02c90744a20f5ef37f30523526106f637
abb05449
secret: aa2c8768a36ce56c54a50a4ef93bdf42c225fa5cdf68a1f65c76b30358cdc478
key: 96d0b503c045e18f6e9f62a52d7f59d2
base_nonce: aa39425b7270fcaf1c7b69ec
exporter_secret:
304296751e7583846d4ec1d49f78b511dee838a32e18dd1bfa44a30a1c1012e0

sequence number: 0
pt: 4265617574792069732074727574682c20747275746820626561757479
aad: 436f756e742d30
nonce: aa39425b7270fcaf1c7b69ec
ct: 1d2ae93bff2fc322a909669c94372cdd2ac0da261face2a706e417a95227
2f6e5eaa20d0cd15fc28ee52026c4d

exporter_context: 00
L: 32
exported_value:
8bfcbf37919c5ee14028640b7eace4e6de00fc39acf073e74cbd9712c9da7beb
*)

exception ParseError of string

let to_mode i = match i with
    0 -> Ok (HPKE.Base)
  | 1 -> Ok (HPKE.PSK)
  | 2 -> Ok (HPKE.Auth)
  | 3 -> Ok (HPKE.AuthPSK)
  | _ -> Error ("Unsupported mode: " ^ Int.to_string i)

let mode_to_str i = match i with
    HPKE.Base    -> "Base   "
  | HPKE.PSK     -> "PSK    "
  | HPKE.Auth    -> "Auth   "
  | HPKE.AuthPSK -> "AuthPSK"

let to_kem i = match i with
    16 -> Ok (Spec_Agile_DH.DH_P256, Spec_Hash_Definitions.SHA2_256)
  | 17 -> Error ("Unsupported KEM: P384")
  | 18 -> Error ("Unsupported KEM: P512")
  | 32 -> Ok (Spec_Agile_DH.DH_Curve25519, Spec_Hash_Definitions.SHA2_256)
  | 33 -> Error ("Unsupported KEM: Curve448")
  | _ -> Error ("Unsupported KEM: " ^ Int.to_string i)

let to_kdf i = match i with
    1 -> Ok (Spec_Hash_Definitions.SHA2_256)
  | 2 -> Ok (Spec_Hash_Definitions.SHA2_384)
  | 3 -> Ok (Spec_Hash_Definitions.SHA2_512)
  | _ -> Error ("Unsupported KDF: " ^ Int.to_string i)

let to_aead i = match i with
    1 -> Error ("Unsupported AEAD: AES-128-GCM")
  | 2 -> Error ("Unsupported AEAD: AES-256-GCM")
(* The AES spec in HACL* is currently not correct, so
 * we do not test it from OCaml *)
(*    1 -> Ok (HPKE.Seal Spec_Agile_AEAD.AES128_GCM)
  | 2 -> Ok (HPKE.Seal Spec_Agile_AEAD.AES256_GCM) *)
  | 3 -> Ok (HPKE.Seal Spec_Agile_AEAD.CHACHA20_POLY1305)
  | 65535 -> Ok (HPKE.ExportOnly)
  | _ -> Error ("Unsupported AEAD: " ^ Int.to_string i)

type bytes = FStar_UInt8.t Lib_Sequence.seq

let to_bytes s =
  let bytes = FStar_Bytes.string_of_hex s in (* l is of type Bytes, which contains Char items *)
  let list_char = List.of_seq (Bytes.to_seq bytes) in (* FStar_UInt8.t = int, so this should work *)
  let list_int = List.map Char.code list_char in
  Lib_Sequence.of_list list_int

let bytes_empty = Lib_Sequence.of_list []

let oopt o = match o with
    FStar_Pervasives_Native.Some s -> Some s
  | FStar_Pervasives_Native.None -> None

let get_bytes js key =
  js |> member key |> to_string |> to_bytes

let rec run_encryptions cs enc_ctx js_list =
  match js_list with
    [] -> Ok enc_ctx
  | js::cons ->
      let aad        = get_bytes js "aad" in
      let ciphertext = get_bytes js "ct" in
      let nonce      = get_bytes js "nonce" in
      let plaintext  = get_bytes js "pt" in

      match HPKE.context_seal cs enc_ctx aad plaintext with
        None -> Error "Seal failed"
      | Some (new_enc_ctx, comp_ciphertext) ->
          if not (comp_ciphertext = ciphertext) then Error "Ciphertexts differ"
          else run_encryptions cs new_enc_ctx cons

let rec run_decryptions cs dec_ctx js_list =
  match js_list with
    [] -> Ok dec_ctx
  | js::cons ->
      let aad        = get_bytes js "aad" in
      let ciphertext = get_bytes js "ct" in
      let nonce      = get_bytes js "nonce" in
      let plaintext  = get_bytes js "pt" in

      match HPKE.context_open cs dec_ctx aad ciphertext with
        None -> Error "Open failed"
      | Some (new_dec_ctx, comp_plaintext) ->
          if not (comp_plaintext = plaintext) then Error "Plaintexts differ"
          else run_decryptions cs new_dec_ctx cons

let rec run_exports cs enc_ctx js_list =
  match js_list with
    [] -> Ok true
  | js::cons ->
      let l = js |> member "L" |> to_int in
      let exported_value = get_bytes js "exported_value" in
      let exporter_context = get_bytes js "exporter_context" in

      let comp_exported_value = HPKE.context_export cs enc_ctx exporter_context (Prims.of_int l) in
      if not (comp_exported_value = exported_value) then Error "Exported values differ"
      else run_exports cs enc_ctx cons

let run_derive_key_pair cs ikm sk pk =
  match oopt (HPKE.derive_key_pair cs ikm) with
    None ->
      (*print_string "derive_key_pair returned None\n";*)
      false, bytes_empty, bytes_empty
  | Some (comp_sk, comp_pk) ->
      (*print_string "derive_key_pair returned Some\n";*)
      comp_sk = sk && comp_pk = pk, comp_sk, comp_pk

let rec run_testcase js =
  match js |> member "mode" |> to_int |> to_mode with
    Error e -> Error e
  | Ok mode ->
      print_string ("mode " ^ mode_to_str mode ^ ", ");
      let is_auth = (mode = HPKE.Auth || mode = HPKE.AuthPSK) in
      let is_psk = (mode = HPKE.PSK || mode = HPKE.AuthPSK) in
      match js |> member "kem_id" |> to_int |> to_kem with
        Error e -> Error e
      | Ok (kem_dh, kem_kdf) ->
          match js |> member "kdf_id" |> to_int |> to_kdf with
            Error e -> Error e
          | Ok kdf ->
              match js |> member "aead_id" |> to_int |> to_aead with
                Error e -> Error e
              | Ok aead ->
                  let cs = (kem_dh, kem_kdf, aead, kdf) in
                  let info = get_bytes js "info" in
                  let ikmE = get_bytes js "ikmE" in
                  let pkEm = get_bytes js "pkEm" in
                  let skEm = get_bytes js "skEm" in
                  let ikmR = get_bytes js "ikmR" in
                  let pkRm = get_bytes js "pkRm" in
                  let skRm = get_bytes js "skRm" in

                  let ikmS = if is_auth then js |> member "ikmS" |> to_string |> to_bytes else bytes_empty in
                  let pkSm = if is_auth then js |> member "pkSm" |> to_string |> to_bytes else bytes_empty in
                  let skSm = if is_auth then js |> member "skSm" |> to_string |> to_bytes else bytes_empty in

                  let psk = if is_psk then js |> member "psk" |> to_string |> to_bytes else bytes_empty in
                  let psk_id = if is_psk then js |> member "psk_id" |> to_string |> to_bytes else bytes_empty in

                  let enc  = js |> member "enc" |> to_string |> to_bytes in
                  let shared_secret = js |> member "shared_secret" |> to_string |> to_bytes in
                  let key_schedule_context = js |> member "key_schedule_context" |> to_string |> to_bytes in
                  let secret = js |> member "secret" |> to_string |> to_bytes in
                  let key = js |> member "key" |> to_string |> to_bytes in
                  let base_nonce = js |> member "base_nonce" |> to_string |> to_bytes in
                  let exporter_secret = js |> member "exporter_secret" |> to_string |> to_bytes in

                  let rE, comp_skE, comp_pkE = run_derive_key_pair cs ikmE skEm pkEm in
                  let rR, comp_skR, comp_pkR = run_derive_key_pair cs ikmR skRm pkRm in
                  let rS, comp_skS, comp_pkS = if is_auth then run_derive_key_pair cs ikmS skSm pkSm else false, bytes_empty, bytes_empty in

                  if not rE then Error "parsing ikmE returned smth different" else
                  if not rR then Error "parsing ikmR returned smth different" else
                  if is_auth && not rS then Error "parsing ikmS returned smth different" else (
                  (*print_string "derive_key_pair were all successfull\n";*)

                  (* call the setup function according to the mode *)
                  let osetup =
                    begin match mode with
                      HPKE.Base    -> HPKE.setupBaseS    cs comp_skE (HPKE.deserialize_public_key cs comp_pkR) info
                    | HPKE.PSK     -> HPKE.setupPSKS     cs comp_skE (HPKE.deserialize_public_key cs comp_pkR) info psk psk_id
                    | HPKE.Auth    -> HPKE.setupAuthS    cs comp_skE (HPKE.deserialize_public_key cs comp_pkR) info comp_skS
                    | HPKE.AuthPSK -> HPKE.setupAuthPSKS cs comp_skE (HPKE.deserialize_public_key cs comp_pkR) info psk psk_id comp_skS
                    end in
                  match osetup with
                    None -> Error "setup failed"
                  | Some (comp_enc, comp_enc_ctx) ->

                      let (comp_key, comp_base_nonce, _, comp_exp_sec) = comp_enc_ctx in

                      if not (comp_enc = enc) then Error "setup eph key different" else
                      if not (comp_key = key && comp_base_nonce = base_nonce && comp_exp_sec = exporter_secret) then
                        begin
                          (* try encap separately then *)
                          let oencap =
                            begin match mode with
                              HPKE.Base | HPKE.PSK     -> HPKE.encap cs comp_skE (HPKE.deserialize_public_key cs comp_pkR)
                            | HPKE.Auth | HPKE.AuthPSK -> HPKE.auth_encap cs comp_skE (HPKE.deserialize_public_key cs comp_pkR) comp_skS
                            end in
                          match oencap with
                            None -> Error "encap failed"
                          | Some (comp_shared_secret, comp_enc2) ->
                              if not (comp_enc2 = enc) then Error "encap eph different" else
                              if not (comp_shared_secret = shared_secret) then (
                                Lib_PrintSequence.print_label_lbytes true "comp_shared_secret" (Z.of_int 32) comp_shared_secret;
                                Lib_PrintSequence.print_label_lbytes true "shared_secret" (Z.of_int 32) shared_secret;
                                Error "shared_secret different")
                              else Error "encap seems fine. Error in key_schedule?"
                        end
                      else
                        (* if there are any in the json, test encryptions and decryptions using the context *)
                        let encryptions = js |> member "encryptions" |> to_list in
                        print_string (" #enc: " ^ Int.to_string (List.length encryptions) ^ " ");

                        match run_encryptions cs comp_enc_ctx encryptions with
                          Error e -> print_string (e ^ " "); Error e
                        | Ok _ ->
                            print_string ("enc OK. ");

                            match run_decryptions cs comp_enc_ctx encryptions with
                              Error e -> print_string (e ^ " "); Error e
                            | Ok _ ->
                                print_string ("dec OK. ");

                                (* do exports using the context *)
                                let exports = js |> member "exports" |> to_list in
                                print_string (" #exp: " ^ Int.to_string (List.length exports) ^ " ");
                                match run_exports cs comp_enc_ctx exports with
                                  Error e -> print_string (e ^ " "); Error e
                                | Ok b ->
                                    print_string (" OK. ");

                                    Ok b)


let test_one v =
  match run_testcase v with
    | Ok b -> print_string "Ok\n"; flush stdout; true
    | Error e -> print_string ("Error " ^ e ^ "\n"); flush stdout; false


let test () : bool =
  let json = Yojson.Basic.from_file "hpke/test-vectors-supported.json" in
  let testcases = json |> Yojson.Basic.Util.to_list in
  print_string ("Number of testcases: " ^ Int.to_string (List.length testcases) ^ "\n");
  List.for_all test_one testcases

let (main : unit) = if not (test ()) then (print_endline "Test_Spec_Agile_HPKE failed"; exit 1)
