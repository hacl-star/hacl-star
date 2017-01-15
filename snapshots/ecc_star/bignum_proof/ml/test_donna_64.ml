open Parameters
open UInt
open Big_int
open Stdint
open Bignum
       
let to_limb = to_uint_limb       

let template_donna_64 = fun x -> 51
let template_donna = fun x -> 26 - (x mod 2)
let template_448 = fun x -> 56

let t = template_donna_64
			      
let rec bitweight t i =
  match i with
  | 0 -> 0
  | _ -> t i + bitweight t (i-1)
			      
let rnd_bigint_donna_64 () =
  let a = Bigint.create_limb 5 in
  let b = ref zero_big_int in
  for i = 0 to 4 do
    let r = (Random.int64 (Int64.of_int 0x7ffffffffffff)) in
    Bigint.upd 64 a i 64 (of_int64 r);
    b := add_big_int !b (mult_int_big_int (Int64.to_int r) (power_int_positive_int 2 (bitweight t i)));
  done;
  print_string "\n";
  (a, !b)
        
let print_bigint_64 b =
  for i = 0 to norm_length-1 do
    print_string (to_string (Bigint.index 64 b i));
    print_string " ";
  done;
  print_string "\n"
   
let print_bigint_donna_128 b =
  for i = 0 to Array.length (Bigint.getRef b) - 1 do
    print_string (wide_to_string (Bigint.index 128 b i));
    print_string " ";
  done;
  print_string "\n"

let print_big_int b =
  for i = 0 to (norm_length-1) do
    print_string (string_of_big_int (mod_big_int (div_big_int b (power_int_positive_int 2 (bitweight t i))) (power_int_positive_int 2 (t i))));
    print_string " ";
  done;
  print_string "\n"
	       
let modulo b =
  let prime = sub_big_int (power_int_positive_int 2 255) (big_int_of_int 19) in
  mod_big_int b prime

let time f x s n =
  let t = Sys.time() in
  for i = 1 to n do 
    let _ = f x in
    ()
  done;
  Printf.printf "Ellapsed time for %s : %fs\n" s (Sys.time() -. t)
              
let test () =
  Random.self_init();
  let output = Bigint.create_limb norm_length in
  let tmp = Bigint.create_wide (2*norm_length-1) in
  let a, b = rnd_bigint_donna_64 () in
  let a', b' = rnd_bigint_donna_64 () in
  print_string " --- \n";
  print_string "Random inputs a & b :\n";
  print_bigint_64 a;
  print_bigint_64 a';
  Bignum.fmul output a a';
  let bbb = modulo (mult_big_int b b') in
  print_string " Product with ecc_star big ints & with OCaml standard Big_Int: \n";
  print_bigint_64 output;
  print_big_int bbb;
  print_string "\n-- Performances --\n";
  time (fun () -> Fproduct.multiplication tmp a a') () "1000 multiplications" 1000;
  time (fun () -> Bignum.modulo a tmp) () "1000 modulos" 1000;
  time (fun () -> Fsum.fsum' a a') () "10000 additions" 10000;
  ()
  
let _ =
  test ()
