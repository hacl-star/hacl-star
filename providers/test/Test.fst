module Test

module B = FStar.Buffer
module U32 = FStar.UInt32

open FStar.HyperStack.ST
open EverCrypt.Helpers

open Test.Vectors

#set-options "--admit_smt_queries true"

type lbuffer (l:nat) = b:B.buffer UInt8.t {Buffer.length b == l}
open FStar.UInt32

open FStar.Bytes

private val store_bytes_aux: len:UInt32.t -> buf:lbuffer (UInt32.v len)
  -> i:UInt32.t{i <=^ len} -> b:lbytes (v len) -> St unit
let rec store_bytes_aux len buf i b =
  if i <^ len then
   begin
   B.upd buf i (Bytes.index b (v i));
   store_bytes_aux len buf (i +^ 1ul) b
   end

val store_bytes: l:UInt32.t -> buf:lbuffer (v l) -> b:lbytes (v l) -> St unit
let store_bytes l buf b = store_bytes_aux l buf 0ul b

val buffer_of_hex: string -> StackInline (B.buffer UInt8.t)
 (requires fun _ -> True)
 (ensures  fun _ _ _ -> True)
let buffer_of_hex s =
  let b = bytes_of_hex s in
  let l = Bytes.len b in
  let buf = B.create 0x00uy l in
  store_bytes l buf b;
  buf

val buffer_of_string: string -> StackInline (B.buffer UInt8.t)
 (requires fun _ -> True)
 (ensures  fun _ _ _ -> True)
let buffer_of_string s =
  let b = bytes_of_string s in
  let l = Bytes.len b in
  let buf = B.create 0x00uy l in
  store_bytes l buf b;
  buf

val buffer_of_strings: UInt32.t -> string -> StackInline (B.buffer UInt8.t)
 (requires fun _ -> True)
 (ensures  fun _ _ _ -> True)
let buffer_of_strings n s =
  let b = bytes_of_string s in
  let l = Bytes.len b in
  let buf = B.rcreate HyperStack.root 0x00uy (l *^ n) in
  C.Loops.for 0ul n (fun _ _ -> True)
    (fun i -> store_bytes l (B.offset buf (i *^ l)) b);
  buf

val test_sha256: v:hash_vector{v.hash_alg == SHA256} -> St unit
let test_sha256 v =
  push_frame();

  let output_len = 32ul in
  let output = B.create 0uy output_len in

  let repeat   = U32.uint_to_t v.repeat in
  let len      = U32.mul (Bytes.len (bytes_of_string v.input)) repeat in
  let input    = buffer_of_strings repeat v.input in
  let expected = buffer_of_hex v.output in

  (* Allocate memory for state *)
  let ctx = B.create 0ul U32.(64ul +^ 64ul +^ 8ul +^ 1ul) in

  (* Compute the number of blocks to process *)
  let size_block = 64ul in
  let n = U32.div len size_block in
  let r = U32.rem len size_block in

  (* Get all full blocks and the last block *)
  let input_blocks = B.sub input 0ul (n *%^ size_block) in
  let input_last   = B.sub input (n *%^ size_block) r in

  (* Call the hash function incrementally *)
  EverCrypt.sha256_init ctx;
  EverCrypt.sha256_update_multi ctx input_blocks n;
  EverCrypt.sha256_update_last ctx input_last r;
  EverCrypt.sha256_finish ctx output;

  // Non-incrementally:
  // EverCrypt.sha256_hash output input len

  (* Display the result *)
  TestLib.compare_and_print !$"of SHA256" expected output 32ul;

  pop_frame()


val test_chacha20_poly1305: v:aead_vector{v.cipher == CHACHA20_POLY1305} -> St unit
let test_chacha20_poly1305 v =
  push_frame();

  (* Tests: RFC7539 *)
  let key        = buffer_of_hex v.key in
  let iv         = buffer_of_hex v.iv in
  let aad        = buffer_of_hex v.aad in
  let tag        = buffer_of_hex v.tag in
  let plaintext  = buffer_of_hex v.plaintext in
  let ciphertext = buffer_of_hex v.ciphertext in

  let plaintext_len = Bytes.len (bytes_of_hex v.ciphertext) in
  let aad_len       = Bytes.len (bytes_of_hex v.aad) in
  let ciphertext'   = B.create 0uy plaintext_len in
  let tag'          = B.create 0uy 16ul in
  match EverCrypt.chacha20_poly1305_encrypt
    ciphertext' tag' plaintext plaintext_len aad aad_len key iv with
  | 0ul ->
    begin
    TestLib.compare_and_print !$"of Chacha20-Poly1305 cipher" ciphertext ciphertext' plaintext_len;
    TestLib.compare_and_print !$"of Chacha20-Poly1305 tag" tag tag' 16ul
    end
  | _ ->
    C.String.print !$"Encryption failed";

  pop_frame()


val test_aead: list aead_vector -> St unit
let rec test_aead v =
  match v with
  | [] -> ()
  | v :: vs ->
    match v.cipher with
    | CHACHA20_POLY1305 ->
      let this = test_chacha20_poly1305 v in
      let rest = test_aead vs in
      ()
    | _ -> test_aead vs

val test_hash: list hash_vector -> St unit
let rec test_hash v =
  match v with
  | [] -> ()
  | v :: vs ->
    match v.hash_alg with
    | SHA256 ->
      let this = test_sha256 v in
      let rest = test_hash vs in
      ()
    | _ -> test_hash vs


let main (): St C.exit_code =
  let open EverCrypt in
  push_frame ();
/// Hacl tests
  Test.Bytes.print "===========Hacl===========" "";
  init (Prefer Hacl);
  test_hash hash_vectors;
  test_aead aead_vectors;
  Test.Bytes.main ();
/// Vale tests
  Test.Bytes.print "===========Vale===========" "";
  init (Prefer Vale);
  test_hash hash_vectors;
  pop_frame ();
  C.EXIT_SUCCESS

// fstar.exe --include $KREMLIN_HOME/kremlib --include ../multiplexer --codegen OCaml --odir out Test.fst
// ocamlfind opt -package ctypes,ctypes.foreign -linkpkg EverCrypt_Bytes.ml
// ocamlfind opt -package ctypes,ctypes.foreign -linkpkg EverCrypt_Native.ml
// OCAMLPATH=~/everest/FStar/bin ocamlfind opt -package fstarlib,ctypes,ctypes.foreign -linkpkg -I ../../multiplexer/ml -I $KREMLIN_HOME/kremlib -cclib -L../../out -cclib -levercrypt ../../multiplexer/ml/EverCrypt_Native.cmx ../../multiplexer/ml/EverCrypt_Bytes.cmx Test.ml
// DYLD_LIBRARY_PATH=../../out:~/everest/MLCrypto/openssl:$DYLD_LIBRARY_PATH ./a.out
