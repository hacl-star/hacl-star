module Spec.Random.Test

open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence

open Lib.RandomSequence


let test () =
  let len: size_nat = 32 in
  let e, output = crypto_random Lib.RandomSequence.entropy0 len in
  Lib.PrintSequence.print_label_lbytes #32 "\nResult [crypto_random len]" output;
  IO.print_newline ();
  (match unsound_crypto_random1 len with
  | None -> IO.print_string "\nError: crypto_random Failed !\n"
  | Some output ->
    Lib.PrintSequence.print_label_lbytes #32 "\nResult [unsound_crypto_random1 len]" output;
    IO.print_newline ()
  );
  let output = unsound_crypto_random2 len in
  Lib.PrintSequence.print_label_lbytes #32 "\nResult [unsound_crypto_random2 len]" output;
  IO.print_newline ()
