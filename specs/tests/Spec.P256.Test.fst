module Spec.P256.Test

open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence
open Spec.P256.Montgomery


let sk1 = List.Tot.map u8_from_UInt8 [
	0x13uy; 0x0euy; 0xeduy; 0x5euy; 0xb9uy; 0xbbuy; 0x8euy; 0x01uy;
    0x0uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy;
    0x0uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy;
    0x0uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy
]

(* let sk1 = List.Tot.map u8_from_UInt8 [
	0x2uy; 0x1uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy;
    0x0uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy;
    0x0uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy;
    0x0uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy; 0x0uy
] *)

let inputPoint = JacobianNat
	(to_elem(0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296))
	(to_elem(0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5))
	(to_elem(0x1))

let outputPoint = JacobianNat
	(to_elem(0x339150844EC15234807FE862A86BE77977DBFB3AE3D96F4C22795513AEAAB82F))
	(to_elem(0xB1C14DDFDC8EC1B2583F51E85A5EB3A155840F2034730E9B5ADA38B674336A21))
	(to_elem(0x01))


let test () =
	assert_norm(List.Tot.length sk1 = 32);
	let scalar = of_list sk1 in

	let output = montgomery_ladder inputPoint scalar in
	let x = output.xN in
	let y = output.yN in
	let z = output.zN in

	let output = norm output in

	let x = output.xN in
	let y = output.yN in
	let z = output.zN in

	let result1 = point_compare outputPoint output in

	if result1 then begin  IO.print_string "\nSuccess!\n"; true end
  	else begin IO.print_string "\nFailure :(\n"; false end
