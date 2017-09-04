open Parameters
open UInt
open Big_int
open Stdint
open Bignum

let template_448 = fun x -> 56

let t = template_448

let print_bigint_64 b =
  for i = 0 to norm_length-1 do
    print_string (to_string (Bigint.index_limb b i));
    print_string " ";
  done;
  print_string "\n";
  for i = 0 to norm_length-1 do
    print_string (Uint64.to_string_hex (Uint64.of_string (to_string (Bigint.index_limb b i))));
    print_string " ";
  done;
  print_string "\n"

let format_secret s =
  Bigint.upd_byte s 0 (Uint8.logand (Bigint.index_byte s 0) (Uint8.of_int 252));
  Bigint.upd_byte s 55 (Uint8.logor (Bigint.index_byte s 55) (Uint8.of_int 128))

let scalar1 = "3d262fddf9ec8e88495266fea19a34d28882acef045104d0d1aae121700a779c984c24f8cdd78fbff44943eba368f54b29259a4f1c600ad3"
let scalar2 = "203d494428b8399352665ddca42f9de8fef600908e0d461cb021f8c538345dd77c3e4806e25f46d3315c44e0a5b4371282dd2c8d5be3095f"

let input1 = "06fce640fa3487bfda5f6cf2d5263f8aad88334cbd07437f020f08f9814dc031ddbdc38c19c6da2583fa5429db94ada18aa7a7fb4ef8a086"
let input2 = "0fbcc2f993cd56d3305b0b7d9e55d4c1a8fb5dbb52f8e9a1e9b6201b165d015894e56c4d3570bee52fe205e28a78b91cdfbde71ce8d157db"

let get_input_scalar scalar_string =
  let bytes = Array.init 56 (fun i -> Stdint.Uint8.of_string ("0x" ^ (String.sub scalar_string (2*i) 2))) in
  Bigint.Bigint(bytes,fun x -> 8)

let get_input input_string =
  let bytes = Array.init 56 (fun i -> Stdint.Uint8.of_string ("0x" ^ (String.sub input_string (2*i) 2))) in
  let input56 = Array.make 8 zero_limb in
  let rec fill a b ctr =
    match ctr with
    | 0 -> ()
    | _ ->
       let i = ctr-1 in
       let idx = i / 7 in
       let shift = i mod 7 in
       a.(idx) <- add_limb a.(idx) (shift_left_limb (byte_to_limb b.(i)) (shift*8));
       fill a b (ctr-1) in
  fill input56 bytes 56;
  print_string (input1 ^ "\n");
  Bigint.Bigint(input56,Parameters.templ)

let get_output output =
  let input56 = Bigint.getRef output in
  let s = ref "" in
  for i = 0 to 7 do
    for j = 0 to 6 do
      let s' = (Uint8.to_string_hex (Uint8.of_int64 (to_int64 (shift_right_limb input56.(i) (j*8))))) in
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

let test () =
  (* Output data *)
  let output = Bigint.create_limb norm_length in

  (* Get test scalar *)
  print_string "Getting input scalar :\n";
  let scalar = get_input_scalar scalar1 in
  format_secret scalar;
  Array.iter (fun x -> print_string ((Uint8.to_string x) ^ " ")) (Bigint.getRef scalar);
  print_string "\n";

  print_string "Getting input point :\n";
  (* Create basepoint *)
  let qx = get_input input1 in
  let qy = Bigint.create_limb norm_length in
  let qz = Bigint.create_limb norm_length in
  Bigint.upd_limb qz 0 (UInt.one_limb);
  let basepoint = ConcretePoint.Point(qx, qy, qz) in

  (* Point to store the result *)
  let resx = Bigint.create_limb norm_length in
  let resy = Bigint.create_limb norm_length in
  let resz = Bigint.create_limb norm_length in
  let res = ConcretePoint.Point(resx, resy, resz) in

  (* Ladder *)
  time (fun () -> MontgomeryLadder.montgomery_ladder res scalar basepoint) () "the curve448 montgomery ladder";

  let zrecip = Bigint.create_limb norm_length in
  Crecip.crecip zrecip (ConcretePoint.get_z res);
  Bignum.fmul output (ConcretePoint.get_x res) zrecip;
  Modulo.normalize output;

  let output_string = get_output output in
  print_string "Expected output u-coordinate:\nce3e4ff95a60dc6697da1db1d85e6afbdf79b50a2412d7546d5f239fe14fbaadeb445fc66a01b0779d98223961111e21766282f73dd96b6f\n";
  print_string "Got: \n";
  print_string output_string;
  print_string "\n";
  let s_ref = "ce3e4ff95a60dc6697da1db1d85e6afbdf79b50a2412d7546d5f239fe14fbaadeb445fc66a01b0779d98223961111e21766282f73dd96b6f" in
  compare s_ref output_string;
  print_string "SUCCESS\n"


let _ =
  test ()
