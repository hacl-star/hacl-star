module Hacl.Test.Hash.SHA2

open FStar.Buffer

module SHA2 = Hacl.Hash.SHA2.L256


val main: unit -> ST FStar.Int32.t
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> True))
let main () =

  (* Push a new memory frame *)
  (**) push_frame();

  let output_len = 32ul in
  let output = FStar.Buffer.create 0uy output_len in

  let plaintext_len = 3ul in
  let plaintext = FStar.Buffer.createL [
      0x61uy; 0x62uy; 0x63uy;
    ] in

  (* Allocate memory for state *)
  let ctx = FStar.Buffer.create 0ul 137ul in

  (* Call the hash function *)
  SHA2.init ctx;
  SHA2.update_last ctx plaintext plaintext_len;
  SHA2.finish ctx output;

  (* Display the result *)
  C.print_bytes output 32ul;

  (* Pop the memory frame *)
  (**) pop_frame();

  (* Exit the program *)
  C.exit_success
