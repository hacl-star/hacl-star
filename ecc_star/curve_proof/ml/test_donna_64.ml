open Parameters
open UInt
open Big_int
open Stdint
open Bignum
       
let to_limb = to_uint_limb       

let template_donna_64 = fun x -> 51

let t = template_donna_64
        
let print_bigint_64 b =
  let mask = of_string "0x3ffffff" in
  for i = 0 to norm_length-1 do
    print_string (to_string (Bigint.index_limb b i));
    print_string " ";
  done;
  print_string "\n"

let format_secret s =
  Bigint.upd_byte s 0 (Uint8.logand (Bigint.index_byte s 0) (Uint8.of_int 248));
  Bigint.upd_byte s 31 (Uint8.logand (Bigint.index_byte s 31) (Uint8.of_int 127));
  Bigint.upd_byte s 31 (Uint8.logor (Bigint.index_byte s 31) (Uint8.of_int 64))

let scalar1 = "a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4"
let scalar2 = "4b66e9d4d1b4673c5ad22691957d6af5c11b6421e0ea01d42ca4169e7918ba0d"

let input1 = "e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c"
let input2 = "e5210f12786811d3f4b7959d0538ae2c31dbe7106fc03c3efc4cd549c715a493"
		      
let get_input_scalar scalar_string =
  let bytes = Array.init 32 (fun i -> Stdint.Uint8.of_string ("0x" ^ (String.sub scalar_string (2*i) 2))) in
  Bigint.Bigint(bytes,fun x -> 8)
	       
let get_input input_string =
  let bytes = Array.init 32 (fun i -> Stdint.Uint8.of_string ("0x" ^ (String.sub input_string (2*i) 2))) in
  let input64 = Array.make 4 zero_limb in
  let rec fill a b ctr =
    match ctr with
    | 0 -> ()
    | _ ->
       let i = ctr-1 in
       let idx = i / 8 in
       let shift = i mod 8 in
       a.(idx) <- add_limb a.(idx) (shift_left_limb (byte_to_limb b.(i)) (shift*8));
       fill a b (i-1) in
  fill input64 bytes 32;
  let input51 = Array.make 5 zero_limb in
  let mask = of_string "0x7ffffffffffff" in
  input51.(0) <- log_and_limb input64.(0) mask;
  input51.(1) <- add_limb (log_and_limb (shift_right_limb input64.(0) 51) mask)
			    (log_and_limb (shift_left_limb (input64.(1)) 13) mask);
  input51.(2) <- add_limb (log_and_limb (shift_right_limb input64.(1) 38) mask)
			    (log_and_limb (shift_left_limb (input64.(2)) 26) mask);
  input51.(3) <- add_limb (log_and_limb (shift_right_limb input64.(2) 25) mask)
			    (log_and_limb (shift_left_limb (input64.(3)) 39) mask);
  input51.(4) <- log_and_limb (shift_right_limb input64.(3) 12) mask;
  Bigint.Bigint(input51,Parameters.templ)

let get_input2 input_string =
  let mask = of_string "0x7ffffffffffff" in
  let bytes = Array.init 32 (fun i -> Stdint.Uint8.of_string ("0x" ^ (String.sub input_string (2*i) 2))) in
  let rec mk64 b idx i =
    match i with
    | 0 -> zero_limb | _ -> add_limb (shift_left_limb (byte_to_limb b.(idx+i-1)) (8*(i-1)))
				(mk64 b idx (i-1)) in
  let input51 = Array.make 5 zero_limb in
  input51.(0) <- log_and_limb (mk64 bytes 0 8) mask;
  input51.(1) <- log_and_limb (shift_right_limb (mk64 bytes 6 8) 3) mask;
  input51.(2) <- log_and_limb (shift_right_limb (mk64 bytes 12 8) 6) mask;
  input51.(3) <- log_and_limb (shift_right_limb (mk64 bytes 19 8) 1) mask;
  input51.(4) <- log_and_limb (shift_right_limb (mk64 bytes 24 8) 12) mask;
  Bigint.Bigint(input51,templ)
  
	       
let get_output output =
  let input51 = Bigint.getRef output in
  let input64 = Array.make 5 zero_limb in
  input64.(0) <- add_limb input51.(0) (shift_left_limb input51.(1) 51);
  input64.(1) <- add_limb (shift_right_limb input51.(1) 13) (shift_left_limb input51.(2) 38);
  input64.(2) <- add_limb (shift_right_limb input51.(2) 26) (shift_left_limb input51.(3) 25);
  input64.(3) <- add_limb (shift_right_limb input51.(3) 39) (shift_left_limb input51.(4) 12);
  let s = ref "" in
  for i = 0 to 3 do
    for j = 0 to 7 do
      let s' = (Uint8.to_string_hex (limb_to_byte (shift_right_limb input64.(i) (j*8)))) in
      let s' = String.sub s' 2 (String.length s' - 2) in
      let s' = if String.length s' = 2 then s' else ("0" ^ s') in
      s := !s ^ s';
    done;
  done;
  !s

	       
let time f x s =
  let t = Sys.time() in
  let _ = f x in
  Printf.printf "Ellapsed time for %s : %fs\n" s (Sys.time() -. t)

let compare s_ref s =
  for i = 0 to (String.length s_ref/2) - 1  do
    if String.sub s (2*i) 2 <> String.sub s_ref (2*i) 2 then
      failwith (Printf.sprintf "Reference and result differ at byte %d: %s %s\n" i (String.sub s_ref (2*i) 2) (String.sub s (2*i) 2))
  done

let test4 () =
  (* Output data *)
  let output = Bigint.create_limb norm_length in

  (* Get test scalar *)
  let scalar = get_input_scalar scalar1 in
  format_secret scalar;
  print_string "Input scalar:\n";
  Array.iter (fun x -> print_string ((Uint8.to_string x) ^ " ")) (Bigint.getRef scalar);
  print_string "\n";

  (* Create basepoint *)
  let qx = get_input2 input1 in
  let qy = Bigint.create_limb norm_length in
  let qz = Bigint.create_limb norm_length in
  Bigint.upd_limb qz 0 one_limb;
  print_string "Basepoint : \n";
  print_bigint_64 qx;
  print_bigint_64 qz;
  let basepoint = ConcretePoint.Point(qx, qy, qz) in

  (* Point to store the result *)
  let resx = Bigint.create_limb norm_length in
  let resy = Bigint.create_limb norm_length in
  let resz = Bigint.create_limb norm_length in
  let res = ConcretePoint.Point(resx, resy, resz) in
  
  (* Ladder *)
  time (fun () -> MontgomeryLadder.montgomery_ladder res scalar basepoint) () "the curve25519 montgomery ladder";
  (* time (fun () -> *)
  (*     for i = 0 to 9 do *)
  (*       MontgomeryLadder.montgomery_ladder res scalar basepoint; *)
  (*     done *)
  (*   ) () "10 times the montgomery ladder"; *)

  
  let zrecip = Bigint.create_limb norm_length in
  (* Get the affine coordinates back *)
  Crecip.crecip' zrecip (ConcretePoint.get_z res);
  Bignum.fmul output resx zrecip;
  Modulo.normalize output;

  print_bigint_64 (ConcretePoint.get_x res);
  print_bigint_64 (ConcretePoint.get_z res);
  print_bigint_64 output;
  let output_string = get_output output in
  print_string "\nExpected output u-coordinate:\nc3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552\n";
  print_string "Got:\n";
  print_string output_string;
  print_string "\n";
  let s_ref = "c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552" in
  compare s_ref output_string;
  print_string "SUCCESS"
	       
		  
let _ =
  test4 ()
  
