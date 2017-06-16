//
//   Copyright 2016-2017  INRIA
//
//   Maintainers: Jean-Karim Zinzindohoué
//                Karthikeyan Bhargavan
//                Benjamin Beurdouche
//
//   Licensed under the Apache License, Version 2.0 (the "License");
//   you may not use this file except in compliance with the License.
//   You may obtain a copy of the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in writing, software
//   distributed under the License is distributed on an "AS IS" BASIS,
//   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//   See the License for the specific language governing permissions and
//   limitations under the License.
//

module Spec.SecretBox
(* NaCl secretbox: https://cr.yp.to/highspeed/naclcrypto-20090310.pdf *)

open FStar.Seq
open FStar.UInt32
open FStar.Endianness
open Spec.Lib

let keylen =   32 (* in bytes *)
let noncelen = 24 (* in bytes *)
type key = lbytes keylen
type nonce = lbytes noncelen
type bytes = seq UInt8.t

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 30"

val secretbox_init: k:key -> n:nonce -> 
    		    Tot (Spec.Poly1305.key * Spec.Salsa20.key * Spec.Salsa20.nonce)
let secretbox_init  k n = 
    let (n1,n2) = split n 16 in
    let subkey = Spec.HSalsa20.hsalsa20 k n1 in
    let keyblock = Spec.Salsa20.salsa20_block subkey n2 0 in
    let mackey = slice keyblock 0 32 in
    (mackey,subkey,n2)    

val secretbox_process: input:bytes{length input / Spec.Salsa20.blocklen < pow2 32} ->
    		       k:Spec.Salsa20.key -> n:Spec.Salsa20.nonce -> 
    		       Tot (lbytes (length input))
let secretbox_process input k n = 
    let ilen = length input in
    let ilen0 = if ilen < 32 then ilen else 32 in
    let (i0,irest) = split input ilen0 in
    let iblock0 = create 32 0uy @| i0 in
    let oblock0 = Spec.Salsa20.salsa20_encrypt_bytes k n 0 iblock0 in
    let (_,o0) = split oblock0 32 in
    let orest = Spec.Salsa20.salsa20_encrypt_bytes k n 1 irest in
    let output = o0 @| orest in
    output


val secretbox_detached: m:bytes{length m / Spec.Salsa20.blocklen < pow2 32} ->
    k:key -> n:nonce -> Tot (Spec.Poly1305.tag * lbytes (length m)) 
let secretbox_detached m k n = 
    let (mk,ek,n) = secretbox_init k n in
    let cipher = secretbox_process m ek n in
    let mac = Spec.Poly1305.poly1305 cipher mk in
    (mac,cipher)


val secretbox_open_detached: c:bytes{length c / Spec.Salsa20.blocklen < pow2 32} ->
    mac:Spec.Poly1305.tag -> k:key -> n:nonce -> Tot (option (lbytes (length c)))
let secretbox_open_detached cipher mac k n = 
    let (mk,ek,n) = secretbox_init k n in
    let xmac = Spec.Poly1305.poly1305 cipher mk in
    if xmac = mac then 
       let plain = secretbox_process cipher ek n in
       Some plain
    else None


val secretbox_easy: m:bytes{length m / Spec.Salsa20.blocklen < pow2 32} ->
    k:key -> n:nonce -> Tot (lbytes (length m + 16)) 
let secretbox_easy m k n = 
    let (mac,cipher) = secretbox_detached m k n in 
    mac @| cipher


val secretbox_open_easy: c:bytes{length c >= 16 /\ (length c - 16) / Spec.Salsa20.blocklen < pow2 32} ->
    k:key -> n:nonce -> Tot (option (lbytes (length c - 16)))
let secretbox_open_easy c k n = 
    let (mac,cipher) = split c 16 in 
    secretbox_open_detached cipher mac k n 

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 30"
//(* Tests: https://cr.yp.to/highspeed/naclcrypto-20090310.pdf *)

unfold let k = [
    	0x1buy;0x27uy;0x55uy;0x64uy;0x73uy;0xe9uy;0x85uy;0xd4uy;
	0x62uy;0xcduy;0x51uy;0x19uy;0x7auy;0x9auy;0x46uy;0xc7uy;
	0x60uy;0x09uy;0x54uy;0x9euy;0xacuy;0x64uy;0x74uy;0xf2uy;
	0x06uy;0xc4uy;0xeeuy;0x08uy;0x44uy;0xf6uy;0x83uy;0x89uy]

unfold let n = [
        0x69uy;0x69uy;0x6euy;0xe9uy;0x55uy;0xb6uy;0x2buy;0x73uy;
	0xcduy;0x62uy;0xbduy;0xa8uy;0x75uy;0xfcuy;0x73uy;0xd6uy;
	0x82uy;0x19uy;0xe0uy;0x03uy;0x6buy;0x7auy;0x0buy;0x37uy]

unfold let p = [
    	0xbeuy;0x07uy;0x5fuy;0xc5uy;0x3cuy;0x81uy;0xf2uy;0xd5uy;
	0xcfuy;0x14uy;0x13uy;0x16uy;0xebuy;0xebuy;0x0cuy;0x7buy;
	0x52uy;0x28uy;0xc5uy;0x2auy;0x4cuy;0x62uy;0xcbuy;0xd4uy;
	0x4buy;0x66uy;0x84uy;0x9buy;0x64uy;0x24uy;0x4fuy;0xfcuy;
	0xe5uy;0xecuy;0xbauy;0xafuy;0x33uy;0xbduy;0x75uy;0x1auy;
	0x1auy;0xc7uy;0x28uy;0xd4uy;0x5euy;0x6cuy;0x61uy;0x29uy;
	0x6cuy;0xdcuy;0x3cuy;0x01uy;0x23uy;0x35uy;0x61uy;0xf4uy;
	0x1duy;0xb6uy;0x6cuy;0xceuy;0x31uy;0x4auy;0xdbuy;0x31uy;
	0x0euy;0x3buy;0xe8uy;0x25uy;0x0cuy;0x46uy;0xf0uy;0x6duy;
	0xceuy;0xeauy;0x3auy;0x7fuy;0xa1uy;0x34uy;0x80uy;0x57uy;
	0xe2uy;0xf6uy;0x55uy;0x6auy;0xd6uy;0xb1uy;0x31uy;0x8auy;
	0x02uy;0x4auy;0x83uy;0x8fuy;0x21uy;0xafuy;0x1fuy;0xdeuy;
	0x04uy;0x89uy;0x77uy;0xebuy;0x48uy;0xf5uy;0x9fuy;0xfduy;
	0x49uy;0x24uy;0xcauy;0x1cuy;0x60uy;0x90uy;0x2euy;0x52uy;
	0xf0uy;0xa0uy;0x89uy;0xbcuy;0x76uy;0x89uy;0x70uy;0x40uy;
	0xe0uy;0x82uy;0xf9uy;0x37uy;0x76uy;0x38uy;0x48uy;0x64uy;
	0x5euy;0x07uy;0x05uy]

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

let test() = 
  assert_norm(List.Tot.length k = 32);
  assert_norm(List.Tot.length n = 24);
  assert_norm(List.Tot.length p = 131);
    let k:key = createL k in
    let n:nonce = createL n in
    let p:bytes = createL p in
    let (mac,cipher) = secretbox_detached p k n in
    let out_easy = secretbox_easy p k n in
    let (mac_easy,cipher_easy) = split out_easy 16 in
    let plain = secretbox_open_detached cipher mac k n in
    let plain_easy = secretbox_open_easy (mac @| cipher) k n in
    match plain, plain_easy with
    | None, _ | _, None -> false
    | Some plain', Some plain_easy' ->
      plain' = p && plain_easy' = p && mac_easy = mac &&
      mac = createL [0xf3uy;0xffuy;0xc7uy;0x70uy;0x3fuy;0x94uy;0x00uy;0xe5uy;
    	  	   0x2auy;0x7duy;0xfbuy;0x4buy;0x3duy;0x33uy;0x05uy;0xd9uy] &&
      cipher = cipher_easy &&
      cipher = createL [
        0x8euy;0x99uy;0x3buy;0x9fuy;0x48uy;0x68uy;0x12uy;0x73uy;
	0xc2uy;0x96uy;0x50uy;0xbauy;0x32uy;0xfcuy;0x76uy;0xceuy;
	0x48uy;0x33uy;0x2euy;0xa7uy;0x16uy;0x4duy;0x96uy;0xa4uy;
	0x47uy;0x6fuy;0xb8uy;0xc5uy;0x31uy;0xa1uy;0x18uy;0x6auy;
	0xc0uy;0xdfuy;0xc1uy;0x7cuy;0x98uy;0xdcuy;0xe8uy;0x7buy;
	0x4duy;0xa7uy;0xf0uy;0x11uy;0xecuy;0x48uy;0xc9uy;0x72uy;
	0x71uy;0xd2uy;0xc2uy;0x0fuy;0x9buy;0x92uy;0x8fuy;0xe2uy;
	0x27uy;0x0duy;0x6fuy;0xb8uy;0x63uy;0xd5uy;0x17uy;0x38uy;
	0xb4uy;0x8euy;0xeeuy;0xe3uy;0x14uy;0xa7uy;0xccuy;0x8auy;
	0xb9uy;0x32uy;0x16uy;0x45uy;0x48uy;0xe5uy;0x26uy;0xaeuy;
	0x90uy;0x22uy;0x43uy;0x68uy;0x51uy;0x7auy;0xcfuy;0xeauy;
	0xbduy;0x6buy;0xb3uy;0x73uy;0x2buy;0xc0uy;0xe9uy;0xdauy;
	0x99uy;0x83uy;0x2buy;0x61uy;0xcauy;0x01uy;0xb6uy;0xdeuy;
	0x56uy;0x24uy;0x4auy;0x9euy;0x88uy;0xd5uy;0xf9uy;0xb3uy;
	0x79uy;0x73uy;0xf6uy;0x22uy;0xa4uy;0x3duy;0x14uy;0xa6uy;
	0x59uy;0x9buy;0x1fuy;0x65uy;0x4cuy;0xb4uy;0x5auy;0x74uy;
	0xe3uy;0x55uy;0xa5uy
    	]
