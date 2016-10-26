open Parameters
open UInt
open Big_int
open Stdint
open Bignum

let template_256 = fun x -> 32

let t = template_256

let print_bigint_64 b =
  for i = 0 to norm_length-1 do
    print_string (Uint64.to_string_hex (Uint64.of_int64 (to_int64 (Bigint.index_limb b i))));
    print_string " ";
  done;
  print_string "\n"

let print_bigint b =
  for i = 0 to norm_length-1 do
    print_string (Uint64.to_string_hex (Uint64.of_int64 (to_int64 (Bigint.index_limb b (7-i)))));
    print_string " ";
  done;
  print_string "\n"

let format_secret s =
  Bigint.upd_byte s 0 Uint8.zero

let scalar1 = "C9AFA9D845BA75166B5C215767B1D6934E50C3DB36E89B127B8A622B120F6721"
let scalar2 = "203d494428b8399352665ddca42f9de8fef600908e0d461cb021f8c538345dd77c3e4806e25f46d3315c44e0a5b4371282dd2c8d5be3095f"

(* Coordinates of the basepoint *)
let x = "6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296"
let y = "4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5"

let xs = "de2444bebc8d36e682edd27e0f271508617519b3221a8fa0b77cab3989da97c9"
let ys = "c093ae7ff36e5380fc01a5aad1e66659702de80f53cec576b6350b243042a256"

let xt = "55a8b00f8da1d44e62f6b3b25316212e39540dc861c89575bb8cf92e35e0986b"
let yt = "5421c3209c2d6c704835d82ac4c3dd90f61a8a52598b9e7ab656e9d8c8b24316"

let get_input_scalar scalar_string =
  let bytes = Array.init 32 (fun i -> Stdint.Uint8.of_string ("0x" ^ (String.sub scalar_string (62 - 2*i) 2))) in
  Bigint.Bigint(bytes,fun x -> 8)

let get_input input_string =
  let bytes = Array.init 32 (fun i -> Stdint.Uint8.of_string ("0x" ^ (String.sub input_string (62 - 2*i) 2))) in
  let input32 = Array.make 8 zero_limb in
  let rec fill a b ctr =
    match ctr with
    | 0 -> ()
    | _ ->
       let i = ctr-1 in
       let idx = i / 4 in
       let shift = i mod 4 in
       a.(idx) <- add_limb a.(idx) (shift_left_limb (byte_to_limb b.(i)) (shift*8));
       fill a b (ctr-1) in
  fill input32 bytes 32;
  Bigint.Bigint(input32,Parameters.templ)

let get_output output =
  let input32 = Bigint.getRef output in
  let s = ref "" in
  for i = 0 to 7 do
    for j = 0 to 3 do
      let s' = (Uint8.to_string_hex (limb_to_byte (shift_right_limb input32.(7-i) ((3-j)*8)))) in
      let s' = String.sub s' 2 (String.length s' - 2) in
      let s' = if String.length s' = 2 then s' else ("0" ^ s') in
      s := !s ^ s';
    done;
  done;
  !s

let get_scalar_of_string s =
  let b = Big_int.big_int_of_string s in
  Array.init 32 (fun i -> Stdint.Uint8.of_string (string_of_big_int (mod_big_int (shift_right_big_int b (8*i)) (power_int_positive_int 2 8))))

let time f x s =
  let t = Sys.time() in
  let _ = f x in
  Printf.printf "Ellapsed time for %s : %fs\n" s (Sys.time() -. t)

let compare s_ref s =
  for i = 0 to (String.length s_ref/2) - 1  do
    if String.sub s (2*i) 2 <> String.sub s_ref (2*i) 2 then
      failwith (Printf.sprintf "Reference and result differ at byte %d: %s %s\n" i (String.sub s_ref (2*i) 2) (String.sub s (2*i) 2))
  done

(* Test vectors taken from http://point-at-infinity.org/ecc/nisttv *)
let test () =
  (* Output data *)
  let output_x = Bigint.create_limb norm_length  in
  let output_y = Bigint.create_limb norm_length  in

  let scalar = get_scalar_of_string "115792089210356248762697446949407573529996955224135760342422259061068512044368" in
  let scalar = Bigint.Bigint(scalar, fun x -> 8) in

  print_string "Value of the scalar : lsb -> msb\n";
  Array.iter (fun x -> print_string ((Uint8.to_string x) ^ " ")) (Bigint.getRef scalar);
  print_string "\n";

  (* Create basepoint *)
  let qx = get_input x in
  let qy = get_input y in
  let qz = Bigint.create_limb norm_length  in
  Bigint.upd_limb qz 0 one_limb;
  print_string "Basepoint : \n";
  print_string "X coordinates : \n";
  print_bigint_64 qx;
  print_string "Y coordinates : \n";
  print_bigint_64 qy;
  print_string "Z coordinates : \n";
  print_bigint_64 qz;
  print_string "\n";
  let basepoint = ConcretePoint.Point(qx, qy, qz) in

  (* Point to store the result *)
  let resx = Bigint.create_limb norm_length  in
  let resy = Bigint.create_limb norm_length  in
  let resz = Bigint.create_limb norm_length  in
  let res = ConcretePoint.Point(resx, resy, resz) in

  (* Ladder *)
  time (fun () -> MontgomeryLadder.montgomery_ladder res scalar basepoint) () "the P256 montgomery ladder";

  let z = ConcretePoint.get_z res in
  let zrecip = Bigint.create_limb norm_length  in
  Crecip.crecip zrecip z;

  let zrecip2 = Bigint.create_limb norm_length  in
  let zrecip3 = Bigint.create_limb norm_length  in
  let z2 = Bigint.create_limb norm_length  in
  let z3 = Bigint.create_limb norm_length  in

  Bignum.fsquare z2 z;
  Bignum.fmul z3 z2 z;

  Bignum.fsquare zrecip2 zrecip;

  Bignum.fmul zrecip3 zrecip2 zrecip;

  Bignum.fmul output_x resx zrecip2;
  Bignum.fmul output_y resy zrecip3;

  Modulo.normalize output_x;
  Modulo.normalize output_y;

  let output_x_string = get_output output_x in
  let output_y_string = get_output output_y in
  print_string "Expected:\nx = 6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296\ny = b01cbd1c01e58065711814b583f061e9d431cca994cea1313449bf97c840ae0a\n";
  print_string "Got:\nx = ";
  print_string output_x_string;
  print_string "\ny = ";
  print_string output_y_string;
  print_string "\n";
  let ref1 = "6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296" in
  let ref2 = "b01cbd1c01e58065711814b583f061e9d431cca994cea1313449bf97c840ae0a" in  
  compare ref1 output_x_string;
  compare ref2 output_y_string;
  print_string "SUCCESS\n"

let test5 () =
  (* Output data *)
  let ss_x = Bigint.create_limb norm_length  in
  let ss_y = Bigint.create_limb norm_length  in
  let st_x = Bigint.create_limb norm_length  in
  let st_y = Bigint.create_limb norm_length  in

  (* Creating point "S" *)
  let sx = get_input xs in
  let sy = get_input ys in
  let sz = Bigint.create_limb norm_length  in Bigint.upd_limb sz 0  one_limb;
  let s = ConcretePoint.Point(sx, sy, sz) in

  (* Creating point "T" *)
  let tx = get_input xt in
  let ty = get_input yt in
  let tz = Bigint.create_limb norm_length  in Bigint.upd_limb tz 0  one_limb;
  let t = ConcretePoint.Point(tx, ty, tz) in

  print_string "Point 'S' : \n";
  print_bigint sx;
  print_bigint sy;
  print_bigint sz;

  print_string "\nPoint 'T' : \n";
  print_bigint tx;
  print_bigint ty;
  print_bigint tz;

  (* Points to store the results *)
  let ssx = Bigint.create_limb norm_length  in
  let ssy = Bigint.create_limb norm_length  in
  let ssz = Bigint.create_limb norm_length  in
  let ss = ConcretePoint.Point(ssx, ssy, ssz) in
  let stx = Bigint.create_limb norm_length  in
  let sty = Bigint.create_limb norm_length  in
  let stz = Bigint.create_limb norm_length  in
  let st = ConcretePoint.Point(stx, sty, stz) in

  (*  DoubleAndAdd.double_and_add ss st s t s; *)
  DoubleAndAdd.double ss s;
  DoubleAndAdd.add st t s;

  let szrecip = Bigint.create_limb norm_length  in
  let tzrecip = Bigint.create_limb norm_length  in

  Crecip.crecip szrecip ssz;
  Crecip.crecip tzrecip stz;

  let szrecip2 = Bigint.create_limb norm_length  in
  let szrecip3 = Bigint.create_limb norm_length  in
  let tzrecip2 = Bigint.create_limb norm_length  in
  let tzrecip3 = Bigint.create_limb norm_length  in

  Bignum.fsquare szrecip2 szrecip;
  Bignum.fmul szrecip3 szrecip2 szrecip;
  Bignum.fsquare tzrecip2 tzrecip;
  Bignum.fmul tzrecip3 tzrecip2 tzrecip;

  Bignum.fmul ss_x ssx szrecip2;
  Bignum.fmul ss_y ssy szrecip3;
  Bignum.fmul st_x stx tzrecip2;
  Bignum.fmul st_y sty tzrecip3;

  let ss_x_string = get_output ss_x in
  let ss_y_string = get_output ss_y in
  let st_x_string = get_output st_x in
  let st_y_string = get_output st_y in
  print_string "\nString output s + s: \n";
  print_string ss_x_string;
  print_string "\ny : \n";
  print_string ss_y_string;
  print_string "\n";
  print_string "\nString output s + t: \n";
  print_string st_x_string;
  print_string "\ny : \n";
  print_string st_y_string;
  print_string "\n"


let _ =
  test ()
