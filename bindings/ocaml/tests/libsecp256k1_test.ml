(* Property-based tests which check the compatibility of K256.Libsecp256k1
   with `libsecp256k1` (https://github.com/bitcoin-core/secp256k1) *)

open Hacl
open QCheck2
open Test_utils
open Libsecp256k1.External

let ctx =
  let ctx = Context.create () in
  let seed = Option.get (RandomBuffer.randombytes ~size:32) in
  match Context.randomize ctx (Bigstring.of_bytes seed) with
  | false -> assert false
  | true -> ctx

let generate_key_libsecp256k1 seed =
  let sk = Key.read_sk_exn ctx (Bigstring.of_bytes seed) in
  let pk = Key.neuterize_exn ctx sk in
  (pk, sk)

let sign_libsecp256k1 msg sk = Sign.sign_exn ctx ~sk (Bigstring.of_bytes msg)

let rec get_valid_k () =
  let k = Option.get (RandomBuffer.randombytes ~size:32) in
  if K256.valid_sk ~sk:k then k else get_valid_k ()

let generate_key seed =
  let sk = if K256.valid_sk ~sk:seed then seed else get_valid_k () in
  match K256.secret_to_public ~sk with
  | Some pk ->
    assert (K256.valid_pk ~pk);
    (pk, sk)
  | None -> assert false

let sign msg sk =
  let k = get_valid_k () in
  K256.Libsecp256k1.sign ~sk ~msg ~k

(* Generate a key pair and sign a message using libsecp256k1 and check that
   it can be verified using the verification function in HACL*. *)
let signature_test_libsecp256k1 (msg, seed) =
  let pk, sk = generate_key_libsecp256k1 seed in
  let signature = Sign.sign_exn ctx ~sk (Bigstring.of_bytes msg) in
  assert (Sign.verify_exn ctx ~pk ~msg:(Bigstring.of_bytes msg) ~signature);
  let signature = Bigstring.to_bytes (Sign.to_bytes ctx signature) in
  let pk = Bigstring.to_bytes (Key.to_bytes ctx pk) in
  match K256.compressed_to_raw pk with
  | Some pk ->
    K256.valid_pk ~pk &&
    K256.Libsecp256k1.is_signature_normalized ~signature &&
    K256.Libsecp256k1.verify ~pk ~msg ~signature
  | None -> false

(* Generate a key pair and sign a message using HACL* and check that
   it can be verified using the verification function in libsecp256k1. *)
let signature_test_hacl (msg, seed) =
  let pk, sk = generate_key seed in
  let pk = K256.raw_to_uncompressed pk in
  let pk = Key.read_pk_exn ctx (Bigstring.of_bytes pk) in
  match sign msg sk with
  | Some signature ->
    let signature = Sign.read_exn ctx (Bigstring.of_bytes signature) in
    Sign.verify_exn ctx ~pk ~msg:(Bigstring.of_bytes msg) ~signature
  | None -> false

let make_tests tests =
  let gen_32_bytes = Gen.(bytes_size (int_range 32 32)) in
  let gen_tuple_bytes = Gen.tup2 gen_32_bytes gen_32_bytes in
  List.map (fun (name, f) ->
      (name, `Quick,
       make_qcheck_test ~print:(Print.(pair bytes bytes)) gen_tuple_bytes f))
    tests

let tests = make_tests [
    ("HACL* verifies libsecp256k1 signature", signature_test_libsecp256k1);
    ("libsecp256k1 verifies HACL* signature", signature_test_hacl);
  ]

let () =
  Alcotest.run "K-256: compatibility with libsecp256k1" [ ("ECDSA", tests) ]
