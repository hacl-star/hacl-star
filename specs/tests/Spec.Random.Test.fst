module Spec.Random.Test

open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence

open Lib.RandomSequence

assume val entropy_init: Lib.RandomSequence.entropy

let test () =
  let len: size_nat = 32 in
  (match crypto_random len with
  | None -> IO.print_string "\nError: crypto_random Failed !\n"
  | Some output ->
    Lib.PrintSequence.print_label_lbytes #32 "Result [crypto_random len]" output;
    IO.print_newline ()
  );
  let e, output = crypto_random2 entropy_init len in
  Lib.PrintSequence.print_label_lbytes #32 "Result [crypto_random2 len]" output;
  IO.print_newline ();
  let output = crypto_random3 len in
  Lib.PrintSequence.print_label_lbytes #32 "Result [crypto_random3 len]" output;
  IO.print_newline ()
