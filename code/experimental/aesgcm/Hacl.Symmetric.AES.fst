module Hacl.Symmetric.AES

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HyperStack.ST
open Hacl.UInt8
open Hacl.Cast
open FStar.Buffer

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32  = Hacl.UInt32

let u8  = U8.t
let u32 = U32.t
let s8  = H8.t
let s32 = H32.t

let u8s = buffer s8

(* This HAS to go in some more appropriate place *)
assume MaxUInt8: pow2 8 = 256
assume MaxUInt32: pow2 32 = 4294967296

(* Parameters for AES-256 *)
let nk = 8ul
let nb = 4ul
let nr = 14ul

val xtime: b:byte -> Tot byte
let xtime b =
  (b <<^ 1ul) ^^ (((b >>^ 7ul) &^ (uint8_to_sint8 1uy)) *%^ (uint8_to_sint8 0x1buy))

val multiply: a:byte -> b:byte -> Tot byte
let multiply a b =
  ((a *%^ (b &^ (uint8_to_sint8 1uy)))
  ^^ (xtime a *%^ ((b >>^ 1ul) &^ (uint8_to_sint8 1uy)))
  ^^ (xtime (xtime a) *%^ ((b >>^ 2ul) &^ (uint8_to_sint8 1uy)))
  ^^ (xtime (xtime (xtime a)) *%^ ((b >>^ 3ul) &^ (uint8_to_sint8 1uy)))
  ^^ (xtime (xtime (xtime (xtime a))) *%^ ((b >>^ 4ul) &^ (uint8_to_sint8 1uy)))
  ^^ (xtime (xtime (xtime (xtime (xtime a)))) *%^ ((b >>^ 5ul) &^ (uint8_to_sint8 1uy)))
  ^^ (xtime (xtime (xtime (xtime (xtime (xtime a))))) *%^ ((b >>^ 6ul) &^ (uint8_to_sint8 1uy)))
  ^^ (xtime (xtime (xtime (xtime (xtime (xtime (xtime a)))))) *%^ ((b >>^ 7ul) &^ (uint8_to_sint8 1uy))))

#set-options "--lax"

val mk_sbox: sbox:u8s{length sbox = 256} -> STL unit
  (requires (fun h -> live h sbox))
  (ensures  (fun h0 _ h1 -> live h1 sbox /\ modifies_1 sbox h0 h1))
let mk_sbox sbox = 
  sbox.(0ul) <-   (uint8_to_sint8 0x63uy); sbox.(1ul) <-   (uint8_to_sint8 0x7cuy); sbox.(2ul) <-   (uint8_to_sint8 0x77uy); sbox.(3ul) <-   (uint8_to_sint8 0x7buy); 
  sbox.(4ul) <-   (uint8_to_sint8 0xf2uy); sbox.(5ul) <-   (uint8_to_sint8 0x6buy); sbox.(6ul) <-   (uint8_to_sint8 0x6fuy); sbox.(7ul) <-   (uint8_to_sint8 0xc5uy); 
  sbox.(8ul) <-   (uint8_to_sint8 0x30uy); sbox.(9ul) <-   (uint8_to_sint8 0x01uy); sbox.(10ul) <-  (uint8_to_sint8 0x67uy); sbox.(11ul) <-  (uint8_to_sint8 0x2buy); 
  sbox.(12ul) <-  (uint8_to_sint8 0xfeuy); sbox.(13ul) <-  (uint8_to_sint8 0xd7uy); sbox.(14ul) <-  (uint8_to_sint8 0xabuy); sbox.(15ul) <-  (uint8_to_sint8 0x76uy); 
  sbox.(16ul) <-  (uint8_to_sint8 0xcauy); sbox.(17ul) <-  (uint8_to_sint8 0x82uy); sbox.(18ul) <-  (uint8_to_sint8 0xc9uy); sbox.(19ul) <-  (uint8_to_sint8 0x7duy); 
  sbox.(20ul) <-  (uint8_to_sint8 0xfauy); sbox.(21ul) <-  (uint8_to_sint8 0x59uy); sbox.(22ul) <-  (uint8_to_sint8 0x47uy); sbox.(23ul) <-  (uint8_to_sint8 0xf0uy); 
  sbox.(24ul) <-  (uint8_to_sint8 0xaduy); sbox.(25ul) <-  (uint8_to_sint8 0xd4uy); sbox.(26ul) <-  (uint8_to_sint8 0xa2uy); sbox.(27ul) <-  (uint8_to_sint8 0xafuy); 
  sbox.(28ul) <-  (uint8_to_sint8 0x9cuy); sbox.(29ul) <-  (uint8_to_sint8 0xa4uy); sbox.(30ul) <-  (uint8_to_sint8 0x72uy); sbox.(31ul) <-  (uint8_to_sint8 0xc0uy); 
  sbox.(32ul) <-  (uint8_to_sint8 0xb7uy); sbox.(33ul) <-  (uint8_to_sint8 0xfduy); sbox.(34ul) <-  (uint8_to_sint8 0x93uy); sbox.(35ul) <-  (uint8_to_sint8 0x26uy); 
  sbox.(36ul) <-  (uint8_to_sint8 0x36uy); sbox.(37ul) <-  (uint8_to_sint8 0x3fuy); sbox.(38ul) <-  (uint8_to_sint8 0xf7uy); sbox.(39ul) <-  (uint8_to_sint8 0xccuy); 
  sbox.(40ul) <-  (uint8_to_sint8 0x34uy); sbox.(41ul) <-  (uint8_to_sint8 0xa5uy); sbox.(42ul) <-  (uint8_to_sint8 0xe5uy); sbox.(43ul) <-  (uint8_to_sint8 0xf1uy); 
  sbox.(44ul) <-  (uint8_to_sint8 0x71uy); sbox.(45ul) <-  (uint8_to_sint8 0xd8uy); sbox.(46ul) <-  (uint8_to_sint8 0x31uy); sbox.(47ul) <-  (uint8_to_sint8 0x15uy); 
  sbox.(48ul) <-  (uint8_to_sint8 0x04uy); sbox.(49ul) <-  (uint8_to_sint8 0xc7uy); sbox.(50ul) <-  (uint8_to_sint8 0x23uy); sbox.(51ul) <-  (uint8_to_sint8 0xc3uy); 
  sbox.(52ul) <-  (uint8_to_sint8 0x18uy); sbox.(53ul) <-  (uint8_to_sint8 0x96uy); sbox.(54ul) <-  (uint8_to_sint8 0x05uy); sbox.(55ul) <-  (uint8_to_sint8 0x9auy); 
  sbox.(56ul) <-  (uint8_to_sint8 0x07uy); sbox.(57ul) <-  (uint8_to_sint8 0x12uy); sbox.(58ul) <-  (uint8_to_sint8 0x80uy); sbox.(59ul) <-  (uint8_to_sint8 0xe2uy); 
  sbox.(60ul) <-  (uint8_to_sint8 0xebuy); sbox.(61ul) <-  (uint8_to_sint8 0x27uy); sbox.(62ul) <-  (uint8_to_sint8 0xb2uy); sbox.(63ul) <-  (uint8_to_sint8 0x75uy); 
  sbox.(64ul) <-  (uint8_to_sint8 0x09uy); sbox.(65ul) <-  (uint8_to_sint8 0x83uy); sbox.(66ul) <-  (uint8_to_sint8 0x2cuy); sbox.(67ul) <-  (uint8_to_sint8 0x1auy); 
  sbox.(68ul) <-  (uint8_to_sint8 0x1buy); sbox.(69ul) <-  (uint8_to_sint8 0x6euy); sbox.(70ul) <-  (uint8_to_sint8 0x5auy); sbox.(71ul) <-  (uint8_to_sint8 0xa0uy); 
  sbox.(72ul) <-  (uint8_to_sint8 0x52uy); sbox.(73ul) <-  (uint8_to_sint8 0x3buy); sbox.(74ul) <-  (uint8_to_sint8 0xd6uy); sbox.(75ul) <-  (uint8_to_sint8 0xb3uy); 
  sbox.(76ul) <-  (uint8_to_sint8 0x29uy); sbox.(77ul) <-  (uint8_to_sint8 0xe3uy); sbox.(78ul) <-  (uint8_to_sint8 0x2fuy); sbox.(79ul) <-  (uint8_to_sint8 0x84uy); 
  sbox.(80ul) <-  (uint8_to_sint8 0x53uy); sbox.(81ul) <-  (uint8_to_sint8 0xd1uy); sbox.(82ul) <-  (uint8_to_sint8 0x00uy); sbox.(83ul) <-  (uint8_to_sint8 0xeduy); 
  sbox.(84ul) <-  (uint8_to_sint8 0x20uy); sbox.(85ul) <-  (uint8_to_sint8 0xfcuy); sbox.(86ul) <-  (uint8_to_sint8 0xb1uy); sbox.(87ul) <-  (uint8_to_sint8 0x5buy); 
  sbox.(88ul) <-  (uint8_to_sint8 0x6auy); sbox.(89ul) <-  (uint8_to_sint8 0xcbuy); sbox.(90ul) <-  (uint8_to_sint8 0xbeuy); sbox.(91ul) <-  (uint8_to_sint8 0x39uy); 
  sbox.(92ul) <-  (uint8_to_sint8 0x4auy); sbox.(93ul) <-  (uint8_to_sint8 0x4cuy); sbox.(94ul) <-  (uint8_to_sint8 0x58uy); sbox.(95ul) <-  (uint8_to_sint8 0xcfuy); 
  sbox.(96ul) <-  (uint8_to_sint8 0xd0uy); sbox.(97ul) <-  (uint8_to_sint8 0xefuy); sbox.(98ul) <-  (uint8_to_sint8 0xaauy); sbox.(99ul) <-  (uint8_to_sint8 0xfbuy); 
  sbox.(100ul) <- (uint8_to_sint8 0x43uy); sbox.(101ul) <- (uint8_to_sint8 0x4duy); sbox.(102ul) <- (uint8_to_sint8 0x33uy); sbox.(103ul) <- (uint8_to_sint8 0x85uy); 
  sbox.(104ul) <- (uint8_to_sint8 0x45uy); sbox.(105ul) <- (uint8_to_sint8 0xf9uy); sbox.(106ul) <- (uint8_to_sint8 0x02uy); sbox.(107ul) <- (uint8_to_sint8 0x7fuy); 
  sbox.(108ul) <- (uint8_to_sint8 0x50uy); sbox.(109ul) <- (uint8_to_sint8 0x3cuy); sbox.(110ul) <- (uint8_to_sint8 0x9fuy); sbox.(111ul) <- (uint8_to_sint8 0xa8uy); 
  sbox.(112ul) <- (uint8_to_sint8 0x51uy); sbox.(113ul) <- (uint8_to_sint8 0xa3uy); sbox.(114ul) <- (uint8_to_sint8 0x40uy); sbox.(115ul) <- (uint8_to_sint8 0x8fuy); 
  sbox.(116ul) <- (uint8_to_sint8 0x92uy); sbox.(117ul) <- (uint8_to_sint8 0x9duy); sbox.(118ul) <- (uint8_to_sint8 0x38uy); sbox.(119ul) <- (uint8_to_sint8 0xf5uy); 
  sbox.(120ul) <- (uint8_to_sint8 0xbcuy); sbox.(121ul) <- (uint8_to_sint8 0xb6uy); sbox.(122ul) <- (uint8_to_sint8 0xdauy); sbox.(123ul) <- (uint8_to_sint8 0x21uy); 
  sbox.(124ul) <- (uint8_to_sint8 0x10uy); sbox.(125ul) <- (uint8_to_sint8 0xffuy); sbox.(126ul) <- (uint8_to_sint8 0xf3uy); sbox.(127ul) <- (uint8_to_sint8 0xd2uy); 
  sbox.(128ul) <- (uint8_to_sint8 0xcduy); sbox.(129ul) <- (uint8_to_sint8 0x0cuy); sbox.(130ul) <- (uint8_to_sint8 0x13uy); sbox.(131ul) <- (uint8_to_sint8 0xecuy); 
  sbox.(132ul) <- (uint8_to_sint8 0x5fuy); sbox.(133ul) <- (uint8_to_sint8 0x97uy); sbox.(134ul) <- (uint8_to_sint8 0x44uy); sbox.(135ul) <- (uint8_to_sint8 0x17uy); 
  sbox.(136ul) <- (uint8_to_sint8 0xc4uy); sbox.(137ul) <- (uint8_to_sint8 0xa7uy); sbox.(138ul) <- (uint8_to_sint8 0x7euy); sbox.(139ul) <- (uint8_to_sint8 0x3duy); 
  sbox.(140ul) <- (uint8_to_sint8 0x64uy); sbox.(141ul) <- (uint8_to_sint8 0x5duy); sbox.(142ul) <- (uint8_to_sint8 0x19uy); sbox.(143ul) <- (uint8_to_sint8 0x73uy); 
  sbox.(144ul) <- (uint8_to_sint8 0x60uy); sbox.(145ul) <- (uint8_to_sint8 0x81uy); sbox.(146ul) <- (uint8_to_sint8 0x4fuy); sbox.(147ul) <- (uint8_to_sint8 0xdcuy); 
  sbox.(148ul) <- (uint8_to_sint8 0x22uy); sbox.(149ul) <- (uint8_to_sint8 0x2auy); sbox.(150ul) <- (uint8_to_sint8 0x90uy); sbox.(151ul) <- (uint8_to_sint8 0x88uy); 
  sbox.(152ul) <- (uint8_to_sint8 0x46uy); sbox.(153ul) <- (uint8_to_sint8 0xeeuy); sbox.(154ul) <- (uint8_to_sint8 0xb8uy); sbox.(155ul) <- (uint8_to_sint8 0x14uy); 
  sbox.(156ul) <- (uint8_to_sint8 0xdeuy); sbox.(157ul) <- (uint8_to_sint8 0x5euy); sbox.(158ul) <- (uint8_to_sint8 0x0buy); sbox.(159ul) <- (uint8_to_sint8 0xdbuy); 
  sbox.(160ul) <- (uint8_to_sint8 0xe0uy); sbox.(161ul) <- (uint8_to_sint8 0x32uy); sbox.(162ul) <- (uint8_to_sint8 0x3auy); sbox.(163ul) <- (uint8_to_sint8 0x0auy); 
  sbox.(164ul) <- (uint8_to_sint8 0x49uy); sbox.(165ul) <- (uint8_to_sint8 0x06uy); sbox.(166ul) <- (uint8_to_sint8 0x24uy); sbox.(167ul) <- (uint8_to_sint8 0x5cuy); 
  sbox.(168ul) <- (uint8_to_sint8 0xc2uy); sbox.(169ul) <- (uint8_to_sint8 0xd3uy); sbox.(170ul) <- (uint8_to_sint8 0xacuy); sbox.(171ul) <- (uint8_to_sint8 0x62uy); 
  sbox.(172ul) <- (uint8_to_sint8 0x91uy); sbox.(173ul) <- (uint8_to_sint8 0x95uy); sbox.(174ul) <- (uint8_to_sint8 0xe4uy); sbox.(175ul) <- (uint8_to_sint8 0x79uy); 
  sbox.(176ul) <- (uint8_to_sint8 0xe7uy); sbox.(177ul) <- (uint8_to_sint8 0xc8uy); sbox.(178ul) <- (uint8_to_sint8 0x37uy); sbox.(179ul) <- (uint8_to_sint8 0x6duy); 
  sbox.(180ul) <- (uint8_to_sint8 0x8duy); sbox.(181ul) <- (uint8_to_sint8 0xd5uy); sbox.(182ul) <- (uint8_to_sint8 0x4euy); sbox.(183ul) <- (uint8_to_sint8 0xa9uy); 
  sbox.(184ul) <- (uint8_to_sint8 0x6cuy); sbox.(185ul) <- (uint8_to_sint8 0x56uy); sbox.(186ul) <- (uint8_to_sint8 0xf4uy); sbox.(187ul) <- (uint8_to_sint8 0xeauy); 
  sbox.(188ul) <- (uint8_to_sint8 0x65uy); sbox.(189ul) <- (uint8_to_sint8 0x7auy); sbox.(190ul) <- (uint8_to_sint8 0xaeuy); sbox.(191ul) <- (uint8_to_sint8 0x08uy); 
  sbox.(192ul) <- (uint8_to_sint8 0xbauy); sbox.(193ul) <- (uint8_to_sint8 0x78uy); sbox.(194ul) <- (uint8_to_sint8 0x25uy); sbox.(195ul) <- (uint8_to_sint8 0x2euy); 
  sbox.(196ul) <- (uint8_to_sint8 0x1cuy); sbox.(197ul) <- (uint8_to_sint8 0xa6uy); sbox.(198ul) <- (uint8_to_sint8 0xb4uy); sbox.(199ul) <- (uint8_to_sint8 0xc6uy); 
  sbox.(200ul) <- (uint8_to_sint8 0xe8uy); sbox.(201ul) <- (uint8_to_sint8 0xdduy); sbox.(202ul) <- (uint8_to_sint8 0x74uy); sbox.(203ul) <- (uint8_to_sint8 0x1fuy); 
  sbox.(204ul) <- (uint8_to_sint8 0x4buy); sbox.(205ul) <- (uint8_to_sint8 0xbduy); sbox.(206ul) <- (uint8_to_sint8 0x8buy); sbox.(207ul) <- (uint8_to_sint8 0x8auy); 
  sbox.(208ul) <- (uint8_to_sint8 0x70uy); sbox.(209ul) <- (uint8_to_sint8 0x3euy); sbox.(210ul) <- (uint8_to_sint8 0xb5uy); sbox.(211ul) <- (uint8_to_sint8 0x66uy); 
  sbox.(212ul) <- (uint8_to_sint8 0x48uy); sbox.(213ul) <- (uint8_to_sint8 0x03uy); sbox.(214ul) <- (uint8_to_sint8 0xf6uy); sbox.(215ul) <- (uint8_to_sint8 0x0euy); 
  sbox.(216ul) <- (uint8_to_sint8 0x61uy); sbox.(217ul) <- (uint8_to_sint8 0x35uy); sbox.(218ul) <- (uint8_to_sint8 0x57uy); sbox.(219ul) <- (uint8_to_sint8 0xb9uy); 
  sbox.(220ul) <- (uint8_to_sint8 0x86uy); sbox.(221ul) <- (uint8_to_sint8 0xc1uy); sbox.(222ul) <- (uint8_to_sint8 0x1duy); sbox.(223ul) <- (uint8_to_sint8 0x9euy); 
  sbox.(224ul) <- (uint8_to_sint8 0xe1uy); sbox.(225ul) <- (uint8_to_sint8 0xf8uy); sbox.(226ul) <- (uint8_to_sint8 0x98uy); sbox.(227ul) <- (uint8_to_sint8 0x11uy); 
  sbox.(228ul) <- (uint8_to_sint8 0x69uy); sbox.(229ul) <- (uint8_to_sint8 0xd9uy); sbox.(230ul) <- (uint8_to_sint8 0x8euy); sbox.(231ul) <- (uint8_to_sint8 0x94uy); 
  sbox.(232ul) <- (uint8_to_sint8 0x9buy); sbox.(233ul) <- (uint8_to_sint8 0x1euy); sbox.(234ul) <- (uint8_to_sint8 0x87uy); sbox.(235ul) <- (uint8_to_sint8 0xe9uy); 
  sbox.(236ul) <- (uint8_to_sint8 0xceuy); sbox.(237ul) <- (uint8_to_sint8 0x55uy); sbox.(238ul) <- (uint8_to_sint8 0x28uy); sbox.(239ul) <- (uint8_to_sint8 0xdfuy); 
  sbox.(240ul) <- (uint8_to_sint8 0x8cuy); sbox.(241ul) <- (uint8_to_sint8 0xa1uy); sbox.(242ul) <- (uint8_to_sint8 0x89uy); sbox.(243ul) <- (uint8_to_sint8 0x0duy); 
  sbox.(244ul) <- (uint8_to_sint8 0xbfuy); sbox.(245ul) <- (uint8_to_sint8 0xe6uy); sbox.(246ul) <- (uint8_to_sint8 0x42uy); sbox.(247ul) <- (uint8_to_sint8 0x68uy); 
  sbox.(248ul) <- (uint8_to_sint8 0x41uy); sbox.(249ul) <- (uint8_to_sint8 0x99uy); sbox.(250ul) <- (uint8_to_sint8 0x2duy); sbox.(251ul) <- (uint8_to_sint8 0x0fuy); 
  sbox.(252ul) <- (uint8_to_sint8 0xb0uy); sbox.(253ul) <- (uint8_to_sint8 0x54uy); sbox.(254ul) <- (uint8_to_sint8 0xbbuy); sbox.(255ul) <- (uint8_to_sint8 0x16uy)

val mk_inv_sbox: sbox:u8s{length sbox = 256} -> STL unit
  (requires (fun h -> live h sbox))
  (ensures  (fun h0 _ h1 -> live h1 sbox /\ modifies_1 sbox h0 h1))
let mk_inv_sbox sbox = 
  sbox.(0ul) <-   (uint8_to_sint8 0x52uy); sbox.(1ul) <-   (uint8_to_sint8 0x09uy); sbox.(2ul) <-   (uint8_to_sint8 0x6auy); sbox.(3ul) <-   (uint8_to_sint8 0xd5uy); 
  sbox.(4ul) <-   (uint8_to_sint8 0x30uy); sbox.(5ul) <-   (uint8_to_sint8 0x36uy); sbox.(6ul) <-   (uint8_to_sint8 0xa5uy); sbox.(7ul) <-   (uint8_to_sint8 0x38uy); 
  sbox.(8ul) <-   (uint8_to_sint8 0xbfuy); sbox.(9ul) <-   (uint8_to_sint8 0x40uy); sbox.(10ul) <-  (uint8_to_sint8 0xa3uy); sbox.(11ul) <-  (uint8_to_sint8 0x9euy); 
  sbox.(12ul) <-  (uint8_to_sint8 0x81uy); sbox.(13ul) <-  (uint8_to_sint8 0xf3uy); sbox.(14ul) <-  (uint8_to_sint8 0xd7uy); sbox.(15ul) <-  (uint8_to_sint8 0xfbuy); 
  sbox.(16ul) <-  (uint8_to_sint8 0x7cuy); sbox.(17ul) <-  (uint8_to_sint8 0xe3uy); sbox.(18ul) <-  (uint8_to_sint8 0x39uy); sbox.(19ul) <-  (uint8_to_sint8 0x82uy); 
  sbox.(20ul) <-  (uint8_to_sint8 0x9buy); sbox.(21ul) <-  (uint8_to_sint8 0x2fuy); sbox.(22ul) <-  (uint8_to_sint8 0xffuy); sbox.(23ul) <-  (uint8_to_sint8 0x87uy); 
  sbox.(24ul) <-  (uint8_to_sint8 0x34uy); sbox.(25ul) <-  (uint8_to_sint8 0x8euy); sbox.(26ul) <-  (uint8_to_sint8 0x43uy); sbox.(27ul) <-  (uint8_to_sint8 0x44uy); 
  sbox.(28ul) <-  (uint8_to_sint8 0xc4uy); sbox.(29ul) <-  (uint8_to_sint8 0xdeuy); sbox.(30ul) <-  (uint8_to_sint8 0xe9uy); sbox.(31ul) <-  (uint8_to_sint8 0xcbuy); 
  sbox.(32ul) <-  (uint8_to_sint8 0x54uy); sbox.(33ul) <-  (uint8_to_sint8 0x7buy); sbox.(34ul) <-  (uint8_to_sint8 0x94uy); sbox.(35ul) <-  (uint8_to_sint8 0x32uy); 
  sbox.(36ul) <-  (uint8_to_sint8 0xa6uy); sbox.(37ul) <-  (uint8_to_sint8 0xc2uy); sbox.(38ul) <-  (uint8_to_sint8 0x23uy); sbox.(39ul) <-  (uint8_to_sint8 0x3duy); 
  sbox.(40ul) <-  (uint8_to_sint8 0xeeuy); sbox.(41ul) <-  (uint8_to_sint8 0x4cuy); sbox.(42ul) <-  (uint8_to_sint8 0x95uy); sbox.(43ul) <-  (uint8_to_sint8 0x0buy); 
  sbox.(44ul) <-  (uint8_to_sint8 0x42uy); sbox.(45ul) <-  (uint8_to_sint8 0xfauy); sbox.(46ul) <-  (uint8_to_sint8 0xc3uy); sbox.(47ul) <-  (uint8_to_sint8 0x4euy); 
  sbox.(48ul) <-  (uint8_to_sint8 0x08uy); sbox.(49ul) <-  (uint8_to_sint8 0x2euy); sbox.(50ul) <-  (uint8_to_sint8 0xa1uy); sbox.(51ul) <-  (uint8_to_sint8 0x66uy); 
  sbox.(52ul) <-  (uint8_to_sint8 0x28uy); sbox.(53ul) <-  (uint8_to_sint8 0xd9uy); sbox.(54ul) <-  (uint8_to_sint8 0x24uy); sbox.(55ul) <-  (uint8_to_sint8 0xb2uy); 
  sbox.(56ul) <-  (uint8_to_sint8 0x76uy); sbox.(57ul) <-  (uint8_to_sint8 0x5buy); sbox.(58ul) <-  (uint8_to_sint8 0xa2uy); sbox.(59ul) <-  (uint8_to_sint8 0x49uy); 
  sbox.(60ul) <-  (uint8_to_sint8 0x6duy); sbox.(61ul) <-  (uint8_to_sint8 0x8buy); sbox.(62ul) <-  (uint8_to_sint8 0xd1uy); sbox.(63ul) <-  (uint8_to_sint8 0x25uy); 
  sbox.(64ul) <-  (uint8_to_sint8 0x72uy); sbox.(65ul) <-  (uint8_to_sint8 0xf8uy); sbox.(66ul) <-  (uint8_to_sint8 0xf6uy); sbox.(67ul) <-  (uint8_to_sint8 0x64uy); 
  sbox.(68ul) <-  (uint8_to_sint8 0x86uy); sbox.(69ul) <-  (uint8_to_sint8 0x68uy); sbox.(70ul) <-  (uint8_to_sint8 0x98uy); sbox.(71ul) <-  (uint8_to_sint8 0x16uy); 
  sbox.(72ul) <-  (uint8_to_sint8 0xd4uy); sbox.(73ul) <-  (uint8_to_sint8 0xa4uy); sbox.(74ul) <-  (uint8_to_sint8 0x5cuy); sbox.(75ul) <-  (uint8_to_sint8 0xccuy); 
  sbox.(76ul) <-  (uint8_to_sint8 0x5duy); sbox.(77ul) <-  (uint8_to_sint8 0x65uy); sbox.(78ul) <-  (uint8_to_sint8 0xb6uy); sbox.(79ul) <-  (uint8_to_sint8 0x92uy); 
  sbox.(80ul) <-  (uint8_to_sint8 0x6cuy); sbox.(81ul) <-  (uint8_to_sint8 0x70uy); sbox.(82ul) <-  (uint8_to_sint8 0x48uy); sbox.(83ul) <-  (uint8_to_sint8 0x50uy); 
  sbox.(84ul) <-  (uint8_to_sint8 0xfduy); sbox.(85ul) <-  (uint8_to_sint8 0xeduy); sbox.(86ul) <-  (uint8_to_sint8 0xb9uy); sbox.(87ul) <-  (uint8_to_sint8 0xdauy); 
  sbox.(88ul) <-  (uint8_to_sint8 0x5euy); sbox.(89ul) <-  (uint8_to_sint8 0x15uy); sbox.(90ul) <-  (uint8_to_sint8 0x46uy); sbox.(91ul) <-  (uint8_to_sint8 0x57uy); 
  sbox.(92ul) <-  (uint8_to_sint8 0xa7uy); sbox.(93ul) <-  (uint8_to_sint8 0x8duy); sbox.(94ul) <-  (uint8_to_sint8 0x9duy); sbox.(95ul) <-  (uint8_to_sint8 0x84uy); 
  sbox.(96ul) <-  (uint8_to_sint8 0x90uy); sbox.(97ul) <-  (uint8_to_sint8 0xd8uy); sbox.(98ul) <-  (uint8_to_sint8 0xabuy); sbox.(99ul) <-  (uint8_to_sint8 0x00uy); 
  sbox.(100ul) <- (uint8_to_sint8 0x8cuy); sbox.(101ul) <- (uint8_to_sint8 0xbcuy); sbox.(102ul) <- (uint8_to_sint8 0xd3uy); sbox.(103ul) <- (uint8_to_sint8 0x0auy); 
  sbox.(104ul) <- (uint8_to_sint8 0xf7uy); sbox.(105ul) <- (uint8_to_sint8 0xe4uy); sbox.(106ul) <- (uint8_to_sint8 0x58uy); sbox.(107ul) <- (uint8_to_sint8 0x05uy); 
  sbox.(108ul) <- (uint8_to_sint8 0xb8uy); sbox.(109ul) <- (uint8_to_sint8 0xb3uy); sbox.(110ul) <- (uint8_to_sint8 0x45uy); sbox.(111ul) <- (uint8_to_sint8 0x06uy); 
  sbox.(112ul) <- (uint8_to_sint8 0xd0uy); sbox.(113ul) <- (uint8_to_sint8 0x2cuy); sbox.(114ul) <- (uint8_to_sint8 0x1euy); sbox.(115ul) <- (uint8_to_sint8 0x8fuy); 
  sbox.(116ul) <- (uint8_to_sint8 0xcauy); sbox.(117ul) <- (uint8_to_sint8 0x3fuy); sbox.(118ul) <- (uint8_to_sint8 0x0fuy); sbox.(119ul) <- (uint8_to_sint8 0x02uy); 
  sbox.(120ul) <- (uint8_to_sint8 0xc1uy); sbox.(121ul) <- (uint8_to_sint8 0xafuy); sbox.(122ul) <- (uint8_to_sint8 0xbduy); sbox.(123ul) <- (uint8_to_sint8 0x03uy); 
  sbox.(124ul) <- (uint8_to_sint8 0x01uy); sbox.(125ul) <- (uint8_to_sint8 0x13uy); sbox.(126ul) <- (uint8_to_sint8 0x8auy); sbox.(127ul) <- (uint8_to_sint8 0x6buy); 
  sbox.(128ul) <- (uint8_to_sint8 0x3auy); sbox.(129ul) <- (uint8_to_sint8 0x91uy); sbox.(130ul) <- (uint8_to_sint8 0x11uy); sbox.(131ul) <- (uint8_to_sint8 0x41uy); 
  sbox.(132ul) <- (uint8_to_sint8 0x4fuy); sbox.(133ul) <- (uint8_to_sint8 0x67uy); sbox.(134ul) <- (uint8_to_sint8 0xdcuy); sbox.(135ul) <- (uint8_to_sint8 0xeauy); 
  sbox.(136ul) <- (uint8_to_sint8 0x97uy); sbox.(137ul) <- (uint8_to_sint8 0xf2uy); sbox.(138ul) <- (uint8_to_sint8 0xcfuy); sbox.(139ul) <- (uint8_to_sint8 0xceuy); 
  sbox.(140ul) <- (uint8_to_sint8 0xf0uy); sbox.(141ul) <- (uint8_to_sint8 0xb4uy); sbox.(142ul) <- (uint8_to_sint8 0xe6uy); sbox.(143ul) <- (uint8_to_sint8 0x73uy); 
  sbox.(144ul) <- (uint8_to_sint8 0x96uy); sbox.(145ul) <- (uint8_to_sint8 0xacuy); sbox.(146ul) <- (uint8_to_sint8 0x74uy); sbox.(147ul) <- (uint8_to_sint8 0x22uy); 
  sbox.(148ul) <- (uint8_to_sint8 0xe7uy); sbox.(149ul) <- (uint8_to_sint8 0xaduy); sbox.(150ul) <- (uint8_to_sint8 0x35uy); sbox.(151ul) <- (uint8_to_sint8 0x85uy); 
  sbox.(152ul) <- (uint8_to_sint8 0xe2uy); sbox.(153ul) <- (uint8_to_sint8 0xf9uy); sbox.(154ul) <- (uint8_to_sint8 0x37uy); sbox.(155ul) <- (uint8_to_sint8 0xe8uy); 
  sbox.(156ul) <- (uint8_to_sint8 0x1cuy); sbox.(157ul) <- (uint8_to_sint8 0x75uy); sbox.(158ul) <- (uint8_to_sint8 0xdfuy); sbox.(159ul) <- (uint8_to_sint8 0x6euy); 
  sbox.(160ul) <- (uint8_to_sint8 0x47uy); sbox.(161ul) <- (uint8_to_sint8 0xf1uy); sbox.(162ul) <- (uint8_to_sint8 0x1auy); sbox.(163ul) <- (uint8_to_sint8 0x71uy); 
  sbox.(164ul) <- (uint8_to_sint8 0x1duy); sbox.(165ul) <- (uint8_to_sint8 0x29uy); sbox.(166ul) <- (uint8_to_sint8 0xc5uy); sbox.(167ul) <- (uint8_to_sint8 0x89uy); 
  sbox.(168ul) <- (uint8_to_sint8 0x6fuy); sbox.(169ul) <- (uint8_to_sint8 0xb7uy); sbox.(170ul) <- (uint8_to_sint8 0x62uy); sbox.(171ul) <- (uint8_to_sint8 0x0euy); 
  sbox.(172ul) <- (uint8_to_sint8 0xaauy); sbox.(173ul) <- (uint8_to_sint8 0x18uy); sbox.(174ul) <- (uint8_to_sint8 0xbeuy); sbox.(175ul) <- (uint8_to_sint8 0x1buy); 
  sbox.(176ul) <- (uint8_to_sint8 0xfcuy); sbox.(177ul) <- (uint8_to_sint8 0x56uy); sbox.(178ul) <- (uint8_to_sint8 0x3euy); sbox.(179ul) <- (uint8_to_sint8 0x4buy); 
  sbox.(180ul) <- (uint8_to_sint8 0xc6uy); sbox.(181ul) <- (uint8_to_sint8 0xd2uy); sbox.(182ul) <- (uint8_to_sint8 0x79uy); sbox.(183ul) <- (uint8_to_sint8 0x20uy); 
  sbox.(184ul) <- (uint8_to_sint8 0x9auy); sbox.(185ul) <- (uint8_to_sint8 0xdbuy); sbox.(186ul) <- (uint8_to_sint8 0xc0uy); sbox.(187ul) <- (uint8_to_sint8 0xfeuy); 
  sbox.(188ul) <- (uint8_to_sint8 0x78uy); sbox.(189ul) <- (uint8_to_sint8 0xcduy); sbox.(190ul) <- (uint8_to_sint8 0x5auy); sbox.(191ul) <- (uint8_to_sint8 0xf4uy); 
  sbox.(192ul) <- (uint8_to_sint8 0x1fuy); sbox.(193ul) <- (uint8_to_sint8 0xdduy); sbox.(194ul) <- (uint8_to_sint8 0xa8uy); sbox.(195ul) <- (uint8_to_sint8 0x33uy); 
  sbox.(196ul) <- (uint8_to_sint8 0x88uy); sbox.(197ul) <- (uint8_to_sint8 0x07uy); sbox.(198ul) <- (uint8_to_sint8 0xc7uy); sbox.(199ul) <- (uint8_to_sint8 0x31uy); 
  sbox.(200ul) <- (uint8_to_sint8 0xb1uy); sbox.(201ul) <- (uint8_to_sint8 0x12uy); sbox.(202ul) <- (uint8_to_sint8 0x10uy); sbox.(203ul) <- (uint8_to_sint8 0x59uy); 
  sbox.(204ul) <- (uint8_to_sint8 0x27uy); sbox.(205ul) <- (uint8_to_sint8 0x80uy); sbox.(206ul) <- (uint8_to_sint8 0xecuy); sbox.(207ul) <- (uint8_to_sint8 0x5fuy); 
  sbox.(208ul) <- (uint8_to_sint8 0x60uy); sbox.(209ul) <- (uint8_to_sint8 0x51uy); sbox.(210ul) <- (uint8_to_sint8 0x7fuy); sbox.(211ul) <- (uint8_to_sint8 0xa9uy); 
  sbox.(212ul) <- (uint8_to_sint8 0x19uy); sbox.(213ul) <- (uint8_to_sint8 0xb5uy); sbox.(214ul) <- (uint8_to_sint8 0x4auy); sbox.(215ul) <- (uint8_to_sint8 0x0duy); 
  sbox.(216ul) <- (uint8_to_sint8 0x2duy); sbox.(217ul) <- (uint8_to_sint8 0xe5uy); sbox.(218ul) <- (uint8_to_sint8 0x7auy); sbox.(219ul) <- (uint8_to_sint8 0x9fuy); 
  sbox.(220ul) <- (uint8_to_sint8 0x93uy); sbox.(221ul) <- (uint8_to_sint8 0xc9uy); sbox.(222ul) <- (uint8_to_sint8 0x9cuy); sbox.(223ul) <- (uint8_to_sint8 0xefuy); 
  sbox.(224ul) <- (uint8_to_sint8 0xa0uy); sbox.(225ul) <- (uint8_to_sint8 0xe0uy); sbox.(226ul) <- (uint8_to_sint8 0x3buy); sbox.(227ul) <- (uint8_to_sint8 0x4duy); 
  sbox.(228ul) <- (uint8_to_sint8 0xaeuy); sbox.(229ul) <- (uint8_to_sint8 0x2auy); sbox.(230ul) <- (uint8_to_sint8 0xf5uy); sbox.(231ul) <- (uint8_to_sint8 0xb0uy);
  sbox.(232ul) <- (uint8_to_sint8 0xc8uy); sbox.(233ul) <- (uint8_to_sint8 0xebuy); sbox.(234ul) <- (uint8_to_sint8 0xbbuy); sbox.(235ul) <- (uint8_to_sint8 0x3cuy);
  sbox.(236ul) <- (uint8_to_sint8 0x83uy); sbox.(237ul) <- (uint8_to_sint8 0x53uy); sbox.(238ul) <- (uint8_to_sint8 0x99uy); sbox.(239ul) <- (uint8_to_sint8 0x61uy);
  sbox.(240ul) <- (uint8_to_sint8 0x17uy); sbox.(241ul) <- (uint8_to_sint8 0x2buy); sbox.(242ul) <- (uint8_to_sint8 0x04uy); sbox.(243ul) <- (uint8_to_sint8 0x7euy);
  sbox.(244ul) <- (uint8_to_sint8 0xbauy); sbox.(245ul) <- (uint8_to_sint8 0x77uy); sbox.(246ul) <- (uint8_to_sint8 0xd6uy); sbox.(247ul) <- (uint8_to_sint8 0x26uy);
  sbox.(248ul) <- (uint8_to_sint8 0xe1uy); sbox.(249ul) <- (uint8_to_sint8 0x69uy); sbox.(250ul) <- (uint8_to_sint8 0x14uy); sbox.(251ul) <- (uint8_to_sint8 0x63uy);
  sbox.(252ul) <- (uint8_to_sint8 0x55uy); sbox.(253ul) <- (uint8_to_sint8 0x21uy); sbox.(254ul) <- (uint8_to_sint8 0x0cuy); sbox.(255ul) <- (uint8_to_sint8 0x7duy)

#reset-options

let rec access_aux: sb:u8s{length sb = 256} -> byte -> ctr:UInt32.t{UInt32.v ctr <= 256} -> byte -> STL byte
  (requires (fun h -> live h sb))
  (ensures  (fun h0 _ h1 -> h1 == h0))
  = fun sbox i ctr tmp ->
  if U32.(ctr =^ 256ul) then tmp
  else let mask = eq_mask i (uint32_to_sint8 ctr) in
       let tmp = tmp |^ (mask &^ sbox.(ctr)) in
       access_aux sbox i (U32.(ctr +^ 1ul)) tmp

val access: sbox:u8s{length sbox = 256} -> idx:byte -> STL byte
  (requires (fun h -> live h sbox))
  (ensures  (fun h0 _ h1 -> h1 == h0))
let access sbox i =
  access_aux sbox i 0ul (uint8_to_sint8 0uy)

val subBytes_aux_sbox: state:u8s{length state >= 4 * UInt32.v nb} -> sbox:u8s{length sbox = 256 /\ disjoint state sbox} ->
  ctr:UInt32.t{UInt32.v ctr <= 16} -> STL unit
  (requires (fun h -> live h state /\ live h sbox))
  (ensures  (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))
let rec subBytes_aux_sbox state sbox ctr =
  if U32.(ctr =^ 16ul) then ()
  else
  begin
    let si = state.(ctr) in
    let si' = access sbox si in
    state.(ctr) <- si';
    subBytes_aux_sbox state sbox (U32.(ctr +^ 1ul))
  end

val subBytes_sbox: state:u8s{length state >= 4 * UInt32.v nb} -> sbox:u8s{length sbox = 256 /\ disjoint state sbox} -> STL unit
  (requires (fun h -> live h state /\ live h sbox))
  (ensures  (fun h0 _ h1 -> modifies_1 state h0 h1 /\ live h1 state))
let subBytes_sbox state sbox =
  subBytes_aux_sbox state sbox 0ul

val shiftRows: state:u8s{length state >= 4 * UInt32.v nb} -> STL unit
  (requires (fun h -> live h state))
  (ensures  (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))
let shiftRows state =
  let open FStar.UInt32 in
  let i = 1ul in
  let tmp = state.(i) in
  state.(i)       <- state.((i+^4ul));
  state.(i+^4ul)  <- state.((i+^8ul));
  state.(i+^8ul)  <- state.((i+^12ul));
  state.(i+^12ul) <- tmp;
  let i = 2ul in
  let tmp = state.(i) in
  state.(i)      <- state.((i+^8ul));
  state.(i+^8ul) <- tmp;
  let tmp = state.(i+^4ul) in
  state.(i+^4ul)  <- state.((i+^12ul));
  state.(i+^12ul) <- tmp;
  let i = 3ul in
  let tmp = state.(i) in
  state.(i)       <- state.((i+^12ul));
  state.(i+^12ul) <- state.((i+^8ul));
  state.(i+^8ul)  <- state.((i+^4ul));
  state.(i+^4ul)  <- tmp;
  ()

#reset-options "--z3rlimit 50 --initial_fuel 0 --max_fuel 0"

val mixColumns_: state:u8s{length state >= 4 * UInt32.v nb} -> c:UInt32.t{UInt32.v c < 4} -> STL unit
  (requires (fun h -> live h state))
  (ensures  (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))
let mixColumns_ state c =
  let open FStar.UInt32 in
  let s0 = state.(0ul+^(4ul*^c)) in
  let s1 = state.(1ul+^(4ul*^c)) in
  let s2 = state.(2ul+^(4ul*^c)) in
  let s3 = state.(3ul+^(4ul*^c)) in
  state.((4ul*^c)+^0ul) <- H8.(multiply (uint8_to_sint8 0x2uy) s0 ^^ multiply (uint8_to_sint8 0x3uy) s1 ^^ s2 ^^ s3);
  state.((4ul*^c)+^1ul) <- H8.(multiply (uint8_to_sint8 0x2uy) s1 ^^ multiply (uint8_to_sint8 0x3uy) s2 ^^ s3 ^^ s0);
  state.((4ul*^c)+^2ul) <- H8.(multiply (uint8_to_sint8 0x2uy) s2 ^^ multiply (uint8_to_sint8 0x3uy) s3 ^^ s0 ^^ s1);
  state.((4ul*^c)+^3ul) <- H8.(multiply (uint8_to_sint8 0x2uy) s3 ^^ multiply (uint8_to_sint8 0x3uy) s0 ^^ s1 ^^ s2)

#reset-options "--initial_fuel 0 --max_fuel 0"

val mixColumns: state:u8s{length state >= 4 * UInt32.v nb} -> STL unit
  (requires (fun h -> live h state))
  (ensures  (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))
let mixColumns state =
  mixColumns_ state 0ul;
  mixColumns_ state 1ul;
  mixColumns_ state 2ul;
  mixColumns_ state 3ul

#reset-options "--z3rlimit 10 --initial_fuel 0 --max_fuel 0"

val addRoundKey_: state:u8s{length state >= 4 * UInt32.v nb} -> w:u8s{length w >= 16 * (UInt32.v nr+1) /\ disjoint state w} -> round:UInt32.t{UInt32.v round <= UInt32.v nr}  -> c:UInt32.t{UInt32.v c < 4} -> STL unit
    (requires (fun h -> live h state /\ live h w))
    (ensures  (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))
let addRoundKey_ state w round c =
  let open FStar.UInt32 in
  let s0 = state.((4ul*^c)+^0ul) in
  let s1 = state.((4ul*^c)+^1ul) in
  let s2 = state.((4ul*^c)+^2ul) in
  let s3 = state.((4ul*^c)+^3ul) in
  let w0 = w.(((4ul*^round)*^nb)+^(4ul*^c)+^0ul) in
  let w1 = w.(((4ul*^round)*^nb)+^(4ul*^c)+^1ul) in
  let w2 = w.(((4ul*^round)*^nb)+^(4ul*^c)+^2ul) in
  let w3 = w.(((4ul*^round)*^nb)+^(4ul*^c)+^3ul) in
  state.((4ul*^c)+^0ul) <- H8.(s0 ^^ w0);
  state.((4ul*^c)+^1ul) <- H8.(s1 ^^ w1);
  state.((4ul*^c)+^2ul) <- H8.(s2 ^^ w2);
  state.((4ul*^c)+^3ul) <- H8.(s3 ^^ w3)

val addRoundKey: state:u8s{length state >= 4 * UInt32.v nb} -> w:u8s{length w >= 16 * (UInt32.v nr+1) /\ disjoint state w} -> round:UInt32.t{UInt32.v round <= UInt32.v nr}  -> STL unit
    (requires (fun h -> live h state /\ live h w))
    (ensures  (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))
let addRoundKey state w round =
  addRoundKey_ state w round 0ul;
  addRoundKey_ state w round 1ul;
  addRoundKey_ state w round 2ul;
  addRoundKey_ state w round 3ul

val cipher_loop: state:u8s{length state >= 4 * UInt32.v nb} -> w:u8s{length w >= 16 * (UInt32.v nr+1) /\ disjoint state w} -> sbox:u8s{length sbox = 256 /\ disjoint sbox state} -> round:UInt32.t{UInt32.v round <= UInt32.v nr} -> STL unit
  (requires (fun h -> live h state /\ live h w /\ live h sbox))
  (ensures  (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))
let rec cipher_loop state w sbox round =
  let open FStar.UInt32 in
  if round = 14ul then ()
  else begin
    subBytes_sbox state sbox;
    shiftRows state;
    mixColumns state;
    addRoundKey state w round;
    cipher_loop state w sbox (round+^1ul)
  end

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val cipher_body: state:u8s{length state >= 4 * UInt32.v nb} -> out:u8s{length out >= 4 * UInt32.v nb} -> input:u8s{length input >= 4*UInt32.v nb} -> w:u8s{length w >= 16 * (UInt32.v nr+1)} -> sbox:u8s{length sbox = 256} -> STL unit
  (requires (fun h -> live h state /\ live h out /\ live h input /\ live h w /\ live h sbox
    /\ disjoint out input /\ disjoint out w /\ disjoint out sbox /\ disjoint state out
    /\ disjoint state input /\ disjoint state w /\ disjoint state sbox))
  (ensures  (fun h0 _ h1 -> live h1 state /\ live h1 out /\ modifies_2 out state h0 h1))
let cipher_body state out input w sbox =
  let open FStar.UInt32 in
  blit input 0ul state 0ul (4ul*^nb);
  addRoundKey state w 0ul;
  cipher_loop state w sbox 1ul;
  subBytes_sbox state sbox;
  shiftRows state;
  addRoundKey state w nr;
  blit state 0ul out 0ul (4ul*^nb)

val cipher: out:u8s{length out >= 4 * UInt32.v nb} -> input:u8s{length input >= 4*UInt32.v nb} -> w:u8s{length w >= 16 * (UInt32.v nr+1)} -> sbox:u8s{length sbox = 256} -> STL unit
  (requires (fun h -> live h out /\ live h input /\ live h w /\ live h sbox
    /\ disjoint out input /\ disjoint out w /\ disjoint out sbox))
  (ensures  (fun h0 _ h1 -> live h1 out /\ modifies_1 out h0 h1))
let cipher out input w sbox =
  push_frame();
  let state = create (uint8_to_sint8 0uy) (U32.(4ul*^nb)) in
  cipher_body state out input w sbox;
  pop_frame()

val rotWord: word:u8s{length word >= 4} -> STL unit
  (requires (fun h -> live h word))
  (ensures  (fun h0 _ h1 -> live h1 word /\ modifies_1 word h0 h1))
let rotWord word =
  let w0 = word.(0ul) in
  let w1 = word.(1ul) in
  let w2 = word.(2ul) in
  let w3 = word.(3ul) in
  word.(0ul) <- w1;
  word.(1ul) <- w2;
  word.(2ul) <- w3;
  word.(3ul) <- w0;
  ()

val subWord: word:u8s{length word >= 4} -> sbox:u8s{length sbox = 256} -> STL unit
  (requires (fun h -> live h word /\ live h sbox /\ disjoint word sbox))
  (ensures  (fun h0 _ h1 -> live h1 word /\ modifies_1 word h0 h1))
let subWord word sbox =
  let w0 = word.(0ul) in
  let w1 = word.(1ul) in
  let w2 = word.(2ul) in
  let w3 = word.(3ul) in
  word.(0ul) <- (access sbox w0);
  word.(1ul) <- (access sbox w1);
  word.(2ul) <- (access sbox w2);
  word.(3ul) <- (access sbox w3);
  ()

val rcon: i:UInt32.t{UInt32.v i >= 1} -> byte -> Tot byte (decreases (UInt32.v i))
let rec rcon i tmp =
  let open FStar.UInt32 in
  if i =^ 1ul then tmp
  else begin
    let tmp = multiply (uint8_to_sint8 0x2uy) tmp in
    rcon (i-^1ul) tmp
  end

#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

let lemma_aux_000 (i:UInt32.t{UInt32.v i < 240 /\ UInt32.v i >= 4 * UInt32.v nk}) : Lemma
  (let open FStar.UInt32 in
    (4 * v nk <= pow2 32 - 1 /\ v (i+^0ul) >= v (4ul *^ nk) /\ v (i+^1ul) >= v (4ul *^ nk) /\ v (i+^2ul) >= v (4ul *^ nk) /\ v (i+^3ul) >= v (4ul *^ nk) /\ v ((i/^4ul)/^nk) >= 1)) = ()

#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0"

val keyExpansion_aux_0:w:u8s{length w >= 16 * (UInt32.v nr+1)} -> temp:u8s{length temp >= 4} -> sbox:u8s{length sbox = 256} -> i:UInt32.t{UInt32.v i < 60 /\ UInt32.v i >= UInt32.v nk} -> STL unit
  (requires (fun h -> live h w /\ live h temp /\ live h sbox
    /\ disjoint w temp /\ disjoint w sbox /\ disjoint temp sbox))
  (ensures  (fun h0 _ h1 -> live h1 temp /\ modifies_1 temp h0 h1))
let keyExpansion_aux_0 w temp sbox j =
  let open FStar.UInt32 in
  let h0 = ST.get() in
  let i = 4ul *^ j in
  lemma_aux_000 i;
  blit w (i-^4ul) temp 0ul 4ul;
  if ((i/^4ul) %^ nk) =^ 0ul then (
    rotWord temp;
    subWord temp sbox;
    let t0 = temp.(0ul) in
    let rc = rcon ((i/^4ul)/^nk) (uint8_to_sint8 1uy) in
    let z = H8.(t0 ^^ rc) in
    temp.(0ul) <- z
  ) else if (((i/^4ul) %^ nk) =^ 4ul) then (
    subWord temp sbox
  );
  let h1 = ST.get() in
  assert(live h1 temp);
  assert(modifies_1 temp h0 h1)

#reset-options "--z3rlimit 50 --initial_fuel 0 --max_fuel 0"

val keyExpansion_aux_1: w:u8s{length w >= 16 * (UInt32.v nr+1)} -> temp:u8s{length temp >= 4} -> sbox:u8s{length sbox = 256} -> i:UInt32.t{UInt32.v i < 60 /\ UInt32.v i >= UInt32.v nk} -> STL unit
  (requires (fun h -> live h w /\ live h temp /\ live h sbox
    /\ disjoint w temp /\ disjoint w sbox /\ disjoint temp sbox))
  (ensures  (fun h0 _ h1 -> live h1 w /\ modifies_1 w h0 h1))
let keyExpansion_aux_1 w temp sbox j =
  let open FStar.UInt32 in
  let i = 4ul *^ j in
  let w0 = w.(i +^ 0ul -^ (4ul*^nk)) in
  let w1 = w.(i +^ 1ul -^ (4ul*^nk)) in
  let w2 = w.(i +^ 2ul -^ (4ul*^nk)) in
  let w3 = w.(i +^ 3ul -^ (4ul*^nk)) in
  let t0 = temp.(0ul) in
  let t1 = temp.(1ul) in
  let t2 = temp.(2ul) in
  let t3 = temp.(3ul) in
  w.(i+^0ul) <- H8.(t0 ^^ w0);
  w.(i+^1ul) <- H8.(t1 ^^ w1);
  w.(i+^2ul) <- H8.(t2 ^^ w2);
  w.(i+^3ul) <- H8.(t3 ^^ w3)

val keyExpansion_aux: w:u8s{length w >= 16 * (UInt32.v nr+1)} -> temp:u8s{length temp >= 4} -> sbox:u8s{length sbox = 256} -> i:UInt32.t{UInt32.v i <= 60 /\ UInt32.v i >= UInt32.v nk} -> STL unit
  (requires (fun h -> live h w /\ live h temp /\ live h sbox
    /\ disjoint w temp /\ disjoint w sbox /\ disjoint temp sbox))
  (ensures  (fun h0 _ h1 -> live h1 temp /\ live h1 w /\ modifies_2 temp w h0 h1))
let rec keyExpansion_aux w temp sbox j =
  let open FStar.UInt32 in
  let h0 = ST.get() in
  if j >=^ 60ul then ()
  else begin
    let i = 4ul *^ j in
    lemma_aux_000 i;
    keyExpansion_aux_0 w temp sbox j;
    keyExpansion_aux_1 w temp sbox j;
    keyExpansion_aux w temp sbox (j +^ 1ul)
  end

let lemma_aux_001 (w:u8s{length w >= 4 * UInt32.v nb * (UInt32.v nr+1)}) : Lemma (length w >= 240) = ()

val keyExpansion: key:u8s{length key >= 4 * UInt32.v nk} -> w:u8s{length w >= 4 * UInt32.v nb * (UInt32.v nr+1)} -> sbox:u8s{length sbox = 256} -> STL unit
  (requires (fun h -> live h key /\ live h w /\ live h sbox /\ disjoint key w /\ disjoint w sbox))
  (ensures  (fun h0 _ h1 -> live h1 w /\ modifies_1 w h0 h1))
let keyExpansion key w sbox =
  let open FStar.UInt32 in
  push_frame();
  let temp = create (uint8_to_sint8 0uy) 4ul in
  lemma_aux_001 w;
  blit key 0ul w 0ul (4ul *^ nk);
  let i = 4ul *^ nk in
  keyExpansion_aux w temp sbox nk;
  pop_frame()


val invShiftRows: state:u8s{length state >= 4 * UInt32.v nb} -> STL unit
  (requires (fun h -> live h state))
  (ensures  (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))
let invShiftRows state =
  let open FStar.UInt32 in
  let i = 3ul in
  let tmp = state.(i) in
  state.(i)       <- (state.(i+^4ul));
  state.(i+^4ul)  <- (state.(i+^8ul));
  state.(i+^8ul)  <- (state.(i+^12ul));
  state.(i+^12ul) <- tmp;
  let i = 2ul in
  let tmp = state.(i) in
  state.(i)       <- (state.(i+^8ul));
  state.(i+^8ul)  <- tmp;
  let tmp = state.(i+^4ul) in
  state.(i+^4ul)  <- (state.(i+^12ul));
  state.(i+^12ul) <- tmp;
  let i = 1ul in
  let tmp = state.(i) in
  state.(i)       <- (state.(i+^12ul));
  state.(i+^12ul) <- (state.(i+^8ul));
  state.(i+^8ul)  <- (state.(i+^4ul));
  state.(i+^4ul)  <- tmp;
  ()

val invSubBytes_aux_sbox: state:u8s{length state >= 4 * UInt32.v nb} -> sbox:u8s{length sbox = 256} -> ctr:UInt32.t{UInt32.v ctr <= 16} -> STL unit
  (requires (fun h -> live h state /\ live h sbox /\ disjoint state sbox))
  (ensures  (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))
let rec invSubBytes_aux_sbox state sbox ctr =
  if ctr = 16ul then ()
  else begin
    let si = state.(ctr) in
    let si' = access sbox si in
    state.(ctr) <- si';
    invSubBytes_aux_sbox state sbox (U32.(ctr+^1ul))
  end

val invSubBytes_sbox: state:u8s{length state >= 4 * UInt32.v nb} -> sbox:u8s{length sbox = 256} -> STL unit
  (requires (fun h -> live h state /\ live h sbox /\ disjoint state sbox))
  (ensures  (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))
let invSubBytes_sbox state sbox =
  invSubBytes_aux_sbox state sbox 0ul

#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0"

val invMixColumns_: state:u8s{length state >= 4 * UInt32.v nb} -> c:UInt32.t{UInt32.v c < 4} -> STL unit
  (requires (fun h -> live h state))
  (ensures  (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1 ))
let invMixColumns_ state c =
  let open FStar.UInt32 in
  let s0 = state.(0ul+^(4ul*^c)) in
  let s1 = state.(1ul+^(4ul*^c)) in
  let s2 = state.(2ul+^(4ul*^c)) in
  let s3 = state.(3ul+^(4ul*^c)) in
  state.((4ul*^c)+^0ul) <- (H8.(multiply (uint8_to_sint8 0xeuy) s0 ^^ multiply (uint8_to_sint8 0xbuy) s1
	       ^^ multiply (uint8_to_sint8 0xduy) s2 ^^ multiply (uint8_to_sint8 0x9uy) s3));
  state.((4ul*^c)+^1ul) <- (H8.(multiply (uint8_to_sint8 0xeuy) s1 ^^ multiply (uint8_to_sint8 0xbuy) s2
	       ^^ multiply (uint8_to_sint8 0xduy) s3 ^^ multiply (uint8_to_sint8 0x9uy) s0));
  state.((4ul*^c)+^2ul) <- (H8.(multiply (uint8_to_sint8 0xeuy) s2 ^^ multiply (uint8_to_sint8 0xbuy) s3
	       ^^ multiply (uint8_to_sint8 0xduy) s0 ^^ multiply (uint8_to_sint8 0x9uy) s1));
  state.((4ul*^c)+^3ul) <- (H8.(multiply (uint8_to_sint8 0xeuy) s3 ^^ multiply (uint8_to_sint8 0xbuy) s0
	       ^^ multiply (uint8_to_sint8 0xduy) s1 ^^ multiply (uint8_to_sint8 0x9uy) s2))

#reset-options "--initial_fuel 0 --max_fuel 0"

val invMixColumns: state:u8s{length state >= 4 * UInt32.v nb} -> STL unit
  (requires (fun h -> live h state))
  (ensures  (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1 ))
let invMixColumns state =
  invMixColumns_ state 0ul;
  invMixColumns_ state 1ul;
  invMixColumns_ state 2ul;
  invMixColumns_ state 3ul

val inv_cipher_loop: state:u8s{length state >= 4 * UInt32.v nb} -> w:u8s{length w >= 4 * UInt32.v nb * (UInt32.v nr+1)} -> sbox:u8s{length sbox = 256} -> round:UInt32.t{UInt32.v round <= UInt32.v nr - 1} -> STL unit
  (requires (fun h -> live h state /\ live h w /\ live h sbox /\ disjoint state w /\ disjoint state sbox
    /\ disjoint sbox w))
  (ensures  (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1 ))
let rec inv_cipher_loop state w sbox round =
  let open FStar.UInt32 in
  if round =^ 0ul then ()
  else begin
    invShiftRows state;
    invSubBytes_sbox state sbox;
    let h = ST.get() in
    assert(live h state /\ live h w);
    assume(length w >= 16 * (v nr+1));
    addRoundKey state w round;
    invMixColumns state;
    inv_cipher_loop state w sbox (round -^ 1ul)
  end

let lemma_002 (w:u8s) : Lemma (requires (length w >= 4 * UInt32.v nb * (UInt32.v nr + 1))) (ensures (length w >= 16 * (UInt32.v nr + 1))) = ()

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val inv_cipher: out:u8s{length out = 4 * UInt32.v nb} -> input:u8s{length input = 4* UInt32.v nb} -> w:u8s{length w >= 4 * UInt32.v nb * (UInt32.v nr+1)} -> sbox:u8s{length sbox = 256} -> STL unit
  (requires (fun h -> live h out /\ live h input /\ live h w /\ live h sbox
    /\ disjoint out input /\ disjoint out w /\ disjoint out sbox /\ disjoint sbox w))
  (ensures  (fun h0 _ h1 -> live h1 out /\ modifies_1 out h0 h1))
let inv_cipher out input w sbox =
  let open FStar.UInt32 in
  push_frame();
  let state = create (uint8_to_sint8 0uy) (4ul *^ nb) in
  blit input 0ul state 0ul (4ul *^ nb);
  lemma_002 w;
  addRoundKey state w nr;
  inv_cipher_loop state w sbox 13ul;
  invShiftRows state;
  invSubBytes_sbox state sbox;
  addRoundKey state w 0ul;
  blit state 0ul out 0ul (4ul *^ nb);
  pop_frame()
