module Hacl.Ocaml.Argmax.Functest

open FStar.All
open FStar.IO
open FStar.Mul
open FStar.UInt

open Hacl.Argmax.Common

module GM = Hacl.Argmax.GM
module P = Hacl.Argmax.Paillier
module U64 = FStar.UInt64

val print_nat: c:nat{c < pow2 64} -> ML unit
let print_nat c =
  let c': uint_t 64 = c in
  print_uint64 (U64.uint_to_t c)

val print_bool: b:bool -> ML unit
let print_bool b = print_string (if b then "true" else "false")

val test_gm: unit -> ML unit
let test_gm () =
  let q:prm = (assume(isprm 7); 7) in
  let p:prm = (assume(isprm 11); 11) in
  let n:comp = mkcomp p q in
  assert (n = p * q);
  let y:fe n = 5 in
  // 6 is nonsquare modulo both 11 and 7
  assume (GM.is_nonsqr #p y /\ GM.is_nonsqr #q y);
  let sec = GM.Secret p q y in
  let pub = GM.s2p sec in
  let r:fe n = 6 in
  assert (sqr r = 36);
  assert (36 < n);
  assert ((36 * 6) % n = 62);
  assert (sqr r *% r = 62);
  assert (sqr r > 0 /\ sqr r *% y > 0);
  let m = false in

  print_string "GM:\n";
  print_string "* mesage: ";
  print_bool m;

  print_string "\n* ciphertext: ";
  let c = GM.encrypt pub r m in
  print_nat c;

  print_string "\n* decrypted: ";
  let m' = GM.decrypt sec c in
  print_bool m';

  print_string "\nGM test done\n\n"

val test_paillier: unit -> ML unit
let test_paillier () =
  let q:prm = (assume(isprm 7); 7) in
  let p:prm = (assume(isprm 11); 11) in
  let n:comp = mkcomp p q in
  assert (n = p * q);
  assert (n = 77);
  // filter (\(x,o) -> o `mod` 77 == 0) $ catMaybes $ map (\x -> (x,) <$> order x (77*77)) [1..77*77-1]
  // order of 617 is exactly 77, and gcd 617 (77*77) = 1
  assert (617 < 77 * 77);
  let g:P.fen2 n = 617 in
  assume (isunit g /\ mult_order g = 77);
  let sec = P.Secret p q g in
  let pub = P.s2p sec in
  let m:fe n = 22 in
  let r:fe n = 40 in
  assert (gcd r n = 1);
  inv_as_gcd1 #n r;

  print_string "Paillier:\n";
  print_string "* mesage: ";
  print_nat m;

  print_string "\n* ciphertext: ";
  let c = P.encrypt pub r m in
  print_nat c;

  print_string "\n* decrypted: ";
  let m' = P.decrypt sec c in
  print_nat m';

  print_string "\nPaillier test done\n"

val main: unit
let main =
  test_gm ();
  test_paillier ()
