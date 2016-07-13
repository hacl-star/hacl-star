module Symmetric.AES

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HST
open Hacl.UInt8
open Hacl.Cast
open Hacl.SBuffer

// Parameters for AES-256 
let nk = 8ul
let nb = 4ul
let nr = 14ul

(* S8 operators *)
let op_Hat_Less_Less (a:byte) (b:UInt32.t) : Tot byte = shift_left a b
let op_Hat_Greater_Greater (a:byte) (b:UInt32.t) : Tot byte = shift_right a b
let op_Hat_Hat (a:byte) (b:byte) : Tot byte = logxor a b
let op_Hat_Amp (a:byte) (b:byte) : Tot byte = logand a b
let op_Hat_Bar (a:byte) (b:byte) : Tot byte = logor  a b
let op_Hat_Star_Percent (a:byte) (b:byte) : Tot byte = mul_mod a b

(* U32 operators *)
let op_At_Plus = UInt32.add
let op_At_Subtraction = UInt32.sub
let op_At_Star = UInt32.mul
let op_At_Slash = UInt32.div
let op_At_Equals = UInt32.eq
let op_At_Percent = UInt32.rem

val xtime: b:byte -> Tot byte
let xtime b =
  (b ^<< 1ul) ^^ (((b ^>> 7ul) ^& (uint8_to_sint8 1uy)) ^*% (uint8_to_sint8 0x1buy))

val multiply: a:byte -> b:byte -> Tot byte
let multiply a b =
  ((a ^*% (b ^& (uint8_to_sint8 1uy)))
  ^^ (xtime a ^*% ((b ^>> 1ul) ^& (uint8_to_sint8 1uy)))
  ^^ (xtime (xtime a) ^*% ((b ^>> 2ul) ^& (uint8_to_sint8 1uy)))
  ^^ (xtime (xtime (xtime a)) ^*% ((b ^>> 3ul) ^& (uint8_to_sint8 1uy)))
  ^^ (xtime (xtime (xtime (xtime a))) ^*% ((b ^>> 4ul) ^& (uint8_to_sint8 1uy)))
  ^^ (xtime (xtime (xtime (xtime (xtime a)))) ^*% ((b ^>> 5ul) ^& (uint8_to_sint8 1uy)))
  ^^ (xtime (xtime (xtime (xtime (xtime (xtime a))))) ^*% ((b ^>> 6ul) ^& (uint8_to_sint8 1uy)))
  ^^ (xtime (xtime (xtime (xtime (xtime (xtime (xtime a)))))) ^*% ((b ^>> 7ul) ^& (uint8_to_sint8 1uy))))

#set-options "--lax"

val mk_sbox: sbox:u8s{length sbox = 256} -> STL unit
  (requires (fun h -> live h sbox))
  (ensures  (fun h0 _ h1 -> live h1 sbox /\ modifies_1 sbox h0 h1))
let mk_sbox sbox = 
  upd sbox 0ul   (uint8_to_sint8 0x63uy); upd sbox 1ul   (uint8_to_sint8 0x7cuy); upd sbox 2ul   (uint8_to_sint8 0x77uy); upd sbox 3ul   (uint8_to_sint8 0x7buy); 
  upd sbox 4ul   (uint8_to_sint8 0xf2uy); upd sbox 5ul   (uint8_to_sint8 0x6buy); upd sbox 6ul   (uint8_to_sint8 0x6fuy); upd sbox 7ul   (uint8_to_sint8 0xc5uy); 
  upd sbox 8ul   (uint8_to_sint8 0x30uy); upd sbox 9ul   (uint8_to_sint8 0x01uy); upd sbox 10ul  (uint8_to_sint8 0x67uy); upd sbox 11ul  (uint8_to_sint8 0x2buy); 
  upd sbox 12ul  (uint8_to_sint8 0xfeuy); upd sbox 13ul  (uint8_to_sint8 0xd7uy); upd sbox 14ul  (uint8_to_sint8 0xabuy); upd sbox 15ul  (uint8_to_sint8 0x76uy); 
  upd sbox 16ul  (uint8_to_sint8 0xcauy); upd sbox 17ul  (uint8_to_sint8 0x82uy); upd sbox 18ul  (uint8_to_sint8 0xc9uy); upd sbox 19ul  (uint8_to_sint8 0x7duy); 
  upd sbox 20ul  (uint8_to_sint8 0xfauy); upd sbox 21ul  (uint8_to_sint8 0x59uy); upd sbox 22ul  (uint8_to_sint8 0x47uy); upd sbox 23ul  (uint8_to_sint8 0xf0uy); 
  upd sbox 24ul  (uint8_to_sint8 0xaduy); upd sbox 25ul  (uint8_to_sint8 0xd4uy); upd sbox 26ul  (uint8_to_sint8 0xa2uy); upd sbox 27ul  (uint8_to_sint8 0xafuy); 
  upd sbox 28ul  (uint8_to_sint8 0x9cuy); upd sbox 29ul  (uint8_to_sint8 0xa4uy); upd sbox 30ul  (uint8_to_sint8 0x72uy); upd sbox 31ul  (uint8_to_sint8 0xc0uy); 
  upd sbox 32ul  (uint8_to_sint8 0xb7uy); upd sbox 33ul  (uint8_to_sint8 0xfduy); upd sbox 34ul  (uint8_to_sint8 0x93uy); upd sbox 35ul  (uint8_to_sint8 0x26uy); 
  upd sbox 36ul  (uint8_to_sint8 0x36uy); upd sbox 37ul  (uint8_to_sint8 0x3fuy); upd sbox 38ul  (uint8_to_sint8 0xf7uy); upd sbox 39ul  (uint8_to_sint8 0xccuy); 
  upd sbox 40ul  (uint8_to_sint8 0x34uy); upd sbox 41ul  (uint8_to_sint8 0xa5uy); upd sbox 42ul  (uint8_to_sint8 0xe5uy); upd sbox 43ul  (uint8_to_sint8 0xf1uy); 
  upd sbox 44ul  (uint8_to_sint8 0x71uy); upd sbox 45ul  (uint8_to_sint8 0xd8uy); upd sbox 46ul  (uint8_to_sint8 0x31uy); upd sbox 47ul  (uint8_to_sint8 0x15uy); 
  upd sbox 48ul  (uint8_to_sint8 0x04uy); upd sbox 49ul  (uint8_to_sint8 0xc7uy); upd sbox 50ul  (uint8_to_sint8 0x23uy); upd sbox 51ul  (uint8_to_sint8 0xc3uy); 
  upd sbox 52ul  (uint8_to_sint8 0x18uy); upd sbox 53ul  (uint8_to_sint8 0x96uy); upd sbox 54ul  (uint8_to_sint8 0x05uy); upd sbox 55ul  (uint8_to_sint8 0x9auy); 
  upd sbox 56ul  (uint8_to_sint8 0x07uy); upd sbox 57ul  (uint8_to_sint8 0x12uy); upd sbox 58ul  (uint8_to_sint8 0x80uy); upd sbox 59ul  (uint8_to_sint8 0xe2uy); 
  upd sbox 60ul  (uint8_to_sint8 0xebuy); upd sbox 61ul  (uint8_to_sint8 0x27uy); upd sbox 62ul  (uint8_to_sint8 0xb2uy); upd sbox 63ul  (uint8_to_sint8 0x75uy); 
  upd sbox 64ul  (uint8_to_sint8 0x09uy); upd sbox 65ul  (uint8_to_sint8 0x83uy); upd sbox 66ul  (uint8_to_sint8 0x2cuy); upd sbox 67ul  (uint8_to_sint8 0x1auy); 
  upd sbox 68ul  (uint8_to_sint8 0x1buy); upd sbox 69ul  (uint8_to_sint8 0x6euy); upd sbox 70ul  (uint8_to_sint8 0x5auy); upd sbox 71ul  (uint8_to_sint8 0xa0uy); 
  upd sbox 72ul  (uint8_to_sint8 0x52uy); upd sbox 73ul  (uint8_to_sint8 0x3buy); upd sbox 74ul  (uint8_to_sint8 0xd6uy); upd sbox 75ul  (uint8_to_sint8 0xb3uy); 
  upd sbox 76ul  (uint8_to_sint8 0x29uy); upd sbox 77ul  (uint8_to_sint8 0xe3uy); upd sbox 78ul  (uint8_to_sint8 0x2fuy); upd sbox 79ul  (uint8_to_sint8 0x84uy); 
  upd sbox 80ul  (uint8_to_sint8 0x53uy); upd sbox 81ul  (uint8_to_sint8 0xd1uy); upd sbox 82ul  (uint8_to_sint8 0x00uy); upd sbox 83ul  (uint8_to_sint8 0xeduy); 
  upd sbox 84ul  (uint8_to_sint8 0x20uy); upd sbox 85ul  (uint8_to_sint8 0xfcuy); upd sbox 86ul  (uint8_to_sint8 0xb1uy); upd sbox 87ul  (uint8_to_sint8 0x5buy); 
  upd sbox 88ul  (uint8_to_sint8 0x6auy); upd sbox 89ul  (uint8_to_sint8 0xcbuy); upd sbox 90ul  (uint8_to_sint8 0xbeuy); upd sbox 91ul  (uint8_to_sint8 0x39uy); 
  upd sbox 92ul  (uint8_to_sint8 0x4auy); upd sbox 93ul  (uint8_to_sint8 0x4cuy); upd sbox 94ul  (uint8_to_sint8 0x58uy); upd sbox 95ul  (uint8_to_sint8 0xcfuy); 
  upd sbox 96ul  (uint8_to_sint8 0xd0uy); upd sbox 97ul  (uint8_to_sint8 0xefuy); upd sbox 98ul  (uint8_to_sint8 0xaauy); upd sbox 99ul  (uint8_to_sint8 0xfbuy); 
  upd sbox 100ul (uint8_to_sint8 0x43uy); upd sbox 101ul (uint8_to_sint8 0x4duy); upd sbox 102ul (uint8_to_sint8 0x33uy); upd sbox 103ul (uint8_to_sint8 0x85uy); 
  upd sbox 104ul (uint8_to_sint8 0x45uy); upd sbox 105ul (uint8_to_sint8 0xf9uy); upd sbox 106ul (uint8_to_sint8 0x02uy); upd sbox 107ul (uint8_to_sint8 0x7fuy); 
  upd sbox 108ul (uint8_to_sint8 0x50uy); upd sbox 109ul (uint8_to_sint8 0x3cuy); upd sbox 110ul (uint8_to_sint8 0x9fuy); upd sbox 111ul (uint8_to_sint8 0xa8uy); 
  upd sbox 112ul (uint8_to_sint8 0x51uy); upd sbox 113ul (uint8_to_sint8 0xa3uy); upd sbox 114ul (uint8_to_sint8 0x40uy); upd sbox 115ul (uint8_to_sint8 0x8fuy); 
  upd sbox 116ul (uint8_to_sint8 0x92uy); upd sbox 117ul (uint8_to_sint8 0x9duy); upd sbox 118ul (uint8_to_sint8 0x38uy); upd sbox 119ul (uint8_to_sint8 0xf5uy); 
  upd sbox 120ul (uint8_to_sint8 0xbcuy); upd sbox 121ul (uint8_to_sint8 0xb6uy); upd sbox 122ul (uint8_to_sint8 0xdauy); upd sbox 123ul (uint8_to_sint8 0x21uy); 
  upd sbox 124ul (uint8_to_sint8 0x10uy); upd sbox 125ul (uint8_to_sint8 0xffuy); upd sbox 126ul (uint8_to_sint8 0xf3uy); upd sbox 127ul (uint8_to_sint8 0xd2uy); 
  upd sbox 128ul (uint8_to_sint8 0xcduy); upd sbox 129ul (uint8_to_sint8 0x0cuy); upd sbox 130ul (uint8_to_sint8 0x13uy); upd sbox 131ul (uint8_to_sint8 0xecuy); 
  upd sbox 132ul (uint8_to_sint8 0x5fuy); upd sbox 133ul (uint8_to_sint8 0x97uy); upd sbox 134ul (uint8_to_sint8 0x44uy); upd sbox 135ul (uint8_to_sint8 0x17uy); 
  upd sbox 136ul (uint8_to_sint8 0xc4uy); upd sbox 137ul (uint8_to_sint8 0xa7uy); upd sbox 138ul (uint8_to_sint8 0x7euy); upd sbox 139ul (uint8_to_sint8 0x3duy); 
  upd sbox 140ul (uint8_to_sint8 0x64uy); upd sbox 141ul (uint8_to_sint8 0x5duy); upd sbox 142ul (uint8_to_sint8 0x19uy); upd sbox 143ul (uint8_to_sint8 0x73uy); 
  upd sbox 144ul (uint8_to_sint8 0x60uy); upd sbox 145ul (uint8_to_sint8 0x81uy); upd sbox 146ul (uint8_to_sint8 0x4fuy); upd sbox 147ul (uint8_to_sint8 0xdcuy); 
  upd sbox 148ul (uint8_to_sint8 0x22uy); upd sbox 149ul (uint8_to_sint8 0x2auy); upd sbox 150ul (uint8_to_sint8 0x90uy); upd sbox 151ul (uint8_to_sint8 0x88uy); 
  upd sbox 152ul (uint8_to_sint8 0x46uy); upd sbox 153ul (uint8_to_sint8 0xeeuy); upd sbox 154ul (uint8_to_sint8 0xb8uy); upd sbox 155ul (uint8_to_sint8 0x14uy); 
  upd sbox 156ul (uint8_to_sint8 0xdeuy); upd sbox 157ul (uint8_to_sint8 0x5euy); upd sbox 158ul (uint8_to_sint8 0x0buy); upd sbox 159ul (uint8_to_sint8 0xdbuy); 
  upd sbox 160ul (uint8_to_sint8 0xe0uy); upd sbox 161ul (uint8_to_sint8 0x32uy); upd sbox 162ul (uint8_to_sint8 0x3auy); upd sbox 163ul (uint8_to_sint8 0x0auy); 
  upd sbox 164ul (uint8_to_sint8 0x49uy); upd sbox 165ul (uint8_to_sint8 0x06uy); upd sbox 166ul (uint8_to_sint8 0x24uy); upd sbox 167ul (uint8_to_sint8 0x5cuy); 
  upd sbox 168ul (uint8_to_sint8 0xc2uy); upd sbox 169ul (uint8_to_sint8 0xd3uy); upd sbox 170ul (uint8_to_sint8 0xacuy); upd sbox 171ul (uint8_to_sint8 0x62uy); 
  upd sbox 172ul (uint8_to_sint8 0x91uy); upd sbox 173ul (uint8_to_sint8 0x95uy); upd sbox 174ul (uint8_to_sint8 0xe4uy); upd sbox 175ul (uint8_to_sint8 0x79uy); 
  upd sbox 176ul (uint8_to_sint8 0xe7uy); upd sbox 177ul (uint8_to_sint8 0xc8uy); upd sbox 178ul (uint8_to_sint8 0x37uy); upd sbox 179ul (uint8_to_sint8 0x6duy); 
  upd sbox 180ul (uint8_to_sint8 0x8duy); upd sbox 181ul (uint8_to_sint8 0xd5uy); upd sbox 182ul (uint8_to_sint8 0x4euy); upd sbox 183ul (uint8_to_sint8 0xa9uy); 
  upd sbox 184ul (uint8_to_sint8 0x6cuy); upd sbox 185ul (uint8_to_sint8 0x56uy); upd sbox 186ul (uint8_to_sint8 0xf4uy); upd sbox 187ul (uint8_to_sint8 0xeauy); 
  upd sbox 188ul (uint8_to_sint8 0x65uy); upd sbox 189ul (uint8_to_sint8 0x7auy); upd sbox 190ul (uint8_to_sint8 0xaeuy); upd sbox 191ul (uint8_to_sint8 0x08uy); 
  upd sbox 192ul (uint8_to_sint8 0xbauy); upd sbox 193ul (uint8_to_sint8 0x78uy); upd sbox 194ul (uint8_to_sint8 0x25uy); upd sbox 195ul (uint8_to_sint8 0x2euy); 
  upd sbox 196ul (uint8_to_sint8 0x1cuy); upd sbox 197ul (uint8_to_sint8 0xa6uy); upd sbox 198ul (uint8_to_sint8 0xb4uy); upd sbox 199ul (uint8_to_sint8 0xc6uy); 
  upd sbox 200ul (uint8_to_sint8 0xe8uy); upd sbox 201ul (uint8_to_sint8 0xdduy); upd sbox 202ul (uint8_to_sint8 0x74uy); upd sbox 203ul (uint8_to_sint8 0x1fuy); 
  upd sbox 204ul (uint8_to_sint8 0x4buy); upd sbox 205ul (uint8_to_sint8 0xbduy); upd sbox 206ul (uint8_to_sint8 0x8buy); upd sbox 207ul (uint8_to_sint8 0x8auy); 
  upd sbox 208ul (uint8_to_sint8 0x70uy); upd sbox 209ul (uint8_to_sint8 0x3euy); upd sbox 210ul (uint8_to_sint8 0xb5uy); upd sbox 211ul (uint8_to_sint8 0x66uy); 
  upd sbox 212ul (uint8_to_sint8 0x48uy); upd sbox 213ul (uint8_to_sint8 0x03uy); upd sbox 214ul (uint8_to_sint8 0xf6uy); upd sbox 215ul (uint8_to_sint8 0x0euy); 
  upd sbox 216ul (uint8_to_sint8 0x61uy); upd sbox 217ul (uint8_to_sint8 0x35uy); upd sbox 218ul (uint8_to_sint8 0x57uy); upd sbox 219ul (uint8_to_sint8 0xb9uy); 
  upd sbox 220ul (uint8_to_sint8 0x86uy); upd sbox 221ul (uint8_to_sint8 0xc1uy); upd sbox 222ul (uint8_to_sint8 0x1duy); upd sbox 223ul (uint8_to_sint8 0x9euy); 
  upd sbox 224ul (uint8_to_sint8 0xe1uy); upd sbox 225ul (uint8_to_sint8 0xf8uy); upd sbox 226ul (uint8_to_sint8 0x98uy); upd sbox 227ul (uint8_to_sint8 0x11uy); 
  upd sbox 228ul (uint8_to_sint8 0x69uy); upd sbox 229ul (uint8_to_sint8 0xd9uy); upd sbox 230ul (uint8_to_sint8 0x8euy); upd sbox 231ul (uint8_to_sint8 0x94uy); 
  upd sbox 232ul (uint8_to_sint8 0x9buy); upd sbox 233ul (uint8_to_sint8 0x1euy); upd sbox 234ul (uint8_to_sint8 0x87uy); upd sbox 235ul (uint8_to_sint8 0xe9uy); 
  upd sbox 236ul (uint8_to_sint8 0xceuy); upd sbox 237ul (uint8_to_sint8 0x55uy); upd sbox 238ul (uint8_to_sint8 0x28uy); upd sbox 239ul (uint8_to_sint8 0xdfuy); 
  upd sbox 240ul (uint8_to_sint8 0x8cuy); upd sbox 241ul (uint8_to_sint8 0xa1uy); upd sbox 242ul (uint8_to_sint8 0x89uy); upd sbox 243ul (uint8_to_sint8 0x0duy); 
  upd sbox 244ul (uint8_to_sint8 0xbfuy); upd sbox 245ul (uint8_to_sint8 0xe6uy); upd sbox 246ul (uint8_to_sint8 0x42uy); upd sbox 247ul (uint8_to_sint8 0x68uy); 
  upd sbox 248ul (uint8_to_sint8 0x41uy); upd sbox 249ul (uint8_to_sint8 0x99uy); upd sbox 250ul (uint8_to_sint8 0x2duy); upd sbox 251ul (uint8_to_sint8 0x0fuy); 
  upd sbox 252ul (uint8_to_sint8 0xb0uy); upd sbox 253ul (uint8_to_sint8 0x54uy); upd sbox 254ul (uint8_to_sint8 0xbbuy); upd sbox 255ul (uint8_to_sint8 0x16uy)

val mk_inv_sbox: sbox:u8s{length sbox = 256} -> STL unit
  (requires (fun h -> live h sbox))
  (ensures  (fun h0 _ h1 -> live h1 sbox /\ modifies_1 sbox h0 h1))
let mk_inv_sbox sbox = 
  upd sbox 0ul   (uint8_to_sint8 0x52uy); upd sbox 1ul   (uint8_to_sint8 0x09uy); upd sbox 2ul   (uint8_to_sint8 0x6auy); upd sbox 3ul   (uint8_to_sint8 0xd5uy); 
  upd sbox 4ul   (uint8_to_sint8 0x30uy); upd sbox 5ul   (uint8_to_sint8 0x36uy); upd sbox 6ul   (uint8_to_sint8 0xa5uy); upd sbox 7ul   (uint8_to_sint8 0x38uy); 
  upd sbox 8ul   (uint8_to_sint8 0xbfuy); upd sbox 9ul   (uint8_to_sint8 0x40uy); upd sbox 10ul  (uint8_to_sint8 0xa3uy); upd sbox 11ul  (uint8_to_sint8 0x9euy); 
  upd sbox 12ul  (uint8_to_sint8 0x81uy); upd sbox 13ul  (uint8_to_sint8 0xf3uy); upd sbox 14ul  (uint8_to_sint8 0xd7uy); upd sbox 15ul  (uint8_to_sint8 0xfbuy); 
  upd sbox 16ul  (uint8_to_sint8 0x7cuy); upd sbox 17ul  (uint8_to_sint8 0xe3uy); upd sbox 18ul  (uint8_to_sint8 0x39uy); upd sbox 19ul  (uint8_to_sint8 0x82uy); 
  upd sbox 20ul  (uint8_to_sint8 0x9buy); upd sbox 21ul  (uint8_to_sint8 0x2fuy); upd sbox 22ul  (uint8_to_sint8 0xffuy); upd sbox 23ul  (uint8_to_sint8 0x87uy); 
  upd sbox 24ul  (uint8_to_sint8 0x34uy); upd sbox 25ul  (uint8_to_sint8 0x8euy); upd sbox 26ul  (uint8_to_sint8 0x43uy); upd sbox 27ul  (uint8_to_sint8 0x44uy); 
  upd sbox 28ul  (uint8_to_sint8 0xc4uy); upd sbox 29ul  (uint8_to_sint8 0xdeuy); upd sbox 30ul  (uint8_to_sint8 0xe9uy); upd sbox 31ul  (uint8_to_sint8 0xcbuy); 
  upd sbox 32ul  (uint8_to_sint8 0x54uy); upd sbox 33ul  (uint8_to_sint8 0x7buy); upd sbox 34ul  (uint8_to_sint8 0x94uy); upd sbox 35ul  (uint8_to_sint8 0x32uy); 
  upd sbox 36ul  (uint8_to_sint8 0xa6uy); upd sbox 37ul  (uint8_to_sint8 0xc2uy); upd sbox 38ul  (uint8_to_sint8 0x23uy); upd sbox 39ul  (uint8_to_sint8 0x3duy); 
  upd sbox 40ul  (uint8_to_sint8 0xeeuy); upd sbox 41ul  (uint8_to_sint8 0x4cuy); upd sbox 42ul  (uint8_to_sint8 0x95uy); upd sbox 43ul  (uint8_to_sint8 0x0buy); 
  upd sbox 44ul  (uint8_to_sint8 0x42uy); upd sbox 45ul  (uint8_to_sint8 0xfauy); upd sbox 46ul  (uint8_to_sint8 0xc3uy); upd sbox 47ul  (uint8_to_sint8 0x4euy); 
  upd sbox 48ul  (uint8_to_sint8 0x08uy); upd sbox 49ul  (uint8_to_sint8 0x2euy); upd sbox 50ul  (uint8_to_sint8 0xa1uy); upd sbox 51ul  (uint8_to_sint8 0x66uy); 
  upd sbox 52ul  (uint8_to_sint8 0x28uy); upd sbox 53ul  (uint8_to_sint8 0xd9uy); upd sbox 54ul  (uint8_to_sint8 0x24uy); upd sbox 55ul  (uint8_to_sint8 0xb2uy); 
  upd sbox 56ul  (uint8_to_sint8 0x76uy); upd sbox 57ul  (uint8_to_sint8 0x5buy); upd sbox 58ul  (uint8_to_sint8 0xa2uy); upd sbox 59ul  (uint8_to_sint8 0x49uy); 
  upd sbox 60ul  (uint8_to_sint8 0x6duy); upd sbox 61ul  (uint8_to_sint8 0x8buy); upd sbox 62ul  (uint8_to_sint8 0xd1uy); upd sbox 63ul  (uint8_to_sint8 0x25uy); 
  upd sbox 64ul  (uint8_to_sint8 0x72uy); upd sbox 65ul  (uint8_to_sint8 0xf8uy); upd sbox 66ul  (uint8_to_sint8 0xf6uy); upd sbox 67ul  (uint8_to_sint8 0x64uy); 
  upd sbox 68ul  (uint8_to_sint8 0x86uy); upd sbox 69ul  (uint8_to_sint8 0x68uy); upd sbox 70ul  (uint8_to_sint8 0x98uy); upd sbox 71ul  (uint8_to_sint8 0x16uy); 
  upd sbox 72ul  (uint8_to_sint8 0xd4uy); upd sbox 73ul  (uint8_to_sint8 0xa4uy); upd sbox 74ul  (uint8_to_sint8 0x5cuy); upd sbox 75ul  (uint8_to_sint8 0xccuy); 
  upd sbox 76ul  (uint8_to_sint8 0x5duy); upd sbox 77ul  (uint8_to_sint8 0x65uy); upd sbox 78ul  (uint8_to_sint8 0xb6uy); upd sbox 79ul  (uint8_to_sint8 0x92uy); 
  upd sbox 80ul  (uint8_to_sint8 0x6cuy); upd sbox 81ul  (uint8_to_sint8 0x70uy); upd sbox 82ul  (uint8_to_sint8 0x48uy); upd sbox 83ul  (uint8_to_sint8 0x50uy); 
  upd sbox 84ul  (uint8_to_sint8 0xfduy); upd sbox 85ul  (uint8_to_sint8 0xeduy); upd sbox 86ul  (uint8_to_sint8 0xb9uy); upd sbox 87ul  (uint8_to_sint8 0xdauy); 
  upd sbox 88ul  (uint8_to_sint8 0x5euy); upd sbox 89ul  (uint8_to_sint8 0x15uy); upd sbox 90ul  (uint8_to_sint8 0x46uy); upd sbox 91ul  (uint8_to_sint8 0x57uy); 
  upd sbox 92ul  (uint8_to_sint8 0xa7uy); upd sbox 93ul  (uint8_to_sint8 0x8duy); upd sbox 94ul  (uint8_to_sint8 0x9duy); upd sbox 95ul  (uint8_to_sint8 0x84uy); 
  upd sbox 96ul  (uint8_to_sint8 0x90uy); upd sbox 97ul  (uint8_to_sint8 0xd8uy); upd sbox 98ul  (uint8_to_sint8 0xabuy); upd sbox 99ul  (uint8_to_sint8 0x00uy); 
  upd sbox 100ul (uint8_to_sint8 0x8cuy); upd sbox 101ul (uint8_to_sint8 0xbcuy); upd sbox 102ul (uint8_to_sint8 0xd3uy); upd sbox 103ul (uint8_to_sint8 0x0auy); 
  upd sbox 104ul (uint8_to_sint8 0xf7uy); upd sbox 105ul (uint8_to_sint8 0xe4uy); upd sbox 106ul (uint8_to_sint8 0x58uy); upd sbox 107ul (uint8_to_sint8 0x05uy); 
  upd sbox 108ul (uint8_to_sint8 0xb8uy); upd sbox 109ul (uint8_to_sint8 0xb3uy); upd sbox 110ul (uint8_to_sint8 0x45uy); upd sbox 111ul (uint8_to_sint8 0x06uy); 
  upd sbox 112ul (uint8_to_sint8 0xd0uy); upd sbox 113ul (uint8_to_sint8 0x2cuy); upd sbox 114ul (uint8_to_sint8 0x1euy); upd sbox 115ul (uint8_to_sint8 0x8fuy); 
  upd sbox 116ul (uint8_to_sint8 0xcauy); upd sbox 117ul (uint8_to_sint8 0x3fuy); upd sbox 118ul (uint8_to_sint8 0x0fuy); upd sbox 119ul (uint8_to_sint8 0x02uy); 
  upd sbox 120ul (uint8_to_sint8 0xc1uy); upd sbox 121ul (uint8_to_sint8 0xafuy); upd sbox 122ul (uint8_to_sint8 0xbduy); upd sbox 123ul (uint8_to_sint8 0x03uy); 
  upd sbox 124ul (uint8_to_sint8 0x01uy); upd sbox 125ul (uint8_to_sint8 0x13uy); upd sbox 126ul (uint8_to_sint8 0x8auy); upd sbox 127ul (uint8_to_sint8 0x6buy); 
  upd sbox 128ul (uint8_to_sint8 0x3auy); upd sbox 129ul (uint8_to_sint8 0x91uy); upd sbox 130ul (uint8_to_sint8 0x11uy); upd sbox 131ul (uint8_to_sint8 0x41uy); 
  upd sbox 132ul (uint8_to_sint8 0x4fuy); upd sbox 133ul (uint8_to_sint8 0x67uy); upd sbox 134ul (uint8_to_sint8 0xdcuy); upd sbox 135ul (uint8_to_sint8 0xeauy); 
  upd sbox 136ul (uint8_to_sint8 0x97uy); upd sbox 137ul (uint8_to_sint8 0xf2uy); upd sbox 138ul (uint8_to_sint8 0xcfuy); upd sbox 139ul (uint8_to_sint8 0xceuy); 
  upd sbox 140ul (uint8_to_sint8 0xf0uy); upd sbox 141ul (uint8_to_sint8 0xb4uy); upd sbox 142ul (uint8_to_sint8 0xe6uy); upd sbox 143ul (uint8_to_sint8 0x73uy); 
  upd sbox 144ul (uint8_to_sint8 0x96uy); upd sbox 145ul (uint8_to_sint8 0xacuy); upd sbox 146ul (uint8_to_sint8 0x74uy); upd sbox 147ul (uint8_to_sint8 0x22uy); 
  upd sbox 148ul (uint8_to_sint8 0xe7uy); upd sbox 149ul (uint8_to_sint8 0xaduy); upd sbox 150ul (uint8_to_sint8 0x35uy); upd sbox 151ul (uint8_to_sint8 0x85uy); 
  upd sbox 152ul (uint8_to_sint8 0xe2uy); upd sbox 153ul (uint8_to_sint8 0xf9uy); upd sbox 154ul (uint8_to_sint8 0x37uy); upd sbox 155ul (uint8_to_sint8 0xe8uy); 
  upd sbox 156ul (uint8_to_sint8 0x1cuy); upd sbox 157ul (uint8_to_sint8 0x75uy); upd sbox 158ul (uint8_to_sint8 0xdfuy); upd sbox 159ul (uint8_to_sint8 0x6euy); 
  upd sbox 160ul (uint8_to_sint8 0x47uy); upd sbox 161ul (uint8_to_sint8 0xf1uy); upd sbox 162ul (uint8_to_sint8 0x1auy); upd sbox 163ul (uint8_to_sint8 0x71uy); 
  upd sbox 164ul (uint8_to_sint8 0x1duy); upd sbox 165ul (uint8_to_sint8 0x29uy); upd sbox 166ul (uint8_to_sint8 0xc5uy); upd sbox 167ul (uint8_to_sint8 0x89uy); 
  upd sbox 168ul (uint8_to_sint8 0x6fuy); upd sbox 169ul (uint8_to_sint8 0xb7uy); upd sbox 170ul (uint8_to_sint8 0x62uy); upd sbox 171ul (uint8_to_sint8 0x0euy); 
  upd sbox 172ul (uint8_to_sint8 0xaauy); upd sbox 173ul (uint8_to_sint8 0x18uy); upd sbox 174ul (uint8_to_sint8 0xbeuy); upd sbox 175ul (uint8_to_sint8 0x1buy); 
  upd sbox 176ul (uint8_to_sint8 0xfcuy); upd sbox 177ul (uint8_to_sint8 0x56uy); upd sbox 178ul (uint8_to_sint8 0x3euy); upd sbox 179ul (uint8_to_sint8 0x4buy); 
  upd sbox 180ul (uint8_to_sint8 0xc6uy); upd sbox 181ul (uint8_to_sint8 0xd2uy); upd sbox 182ul (uint8_to_sint8 0x79uy); upd sbox 183ul (uint8_to_sint8 0x20uy); 
  upd sbox 184ul (uint8_to_sint8 0x9auy); upd sbox 185ul (uint8_to_sint8 0xdbuy); upd sbox 186ul (uint8_to_sint8 0xc0uy); upd sbox 187ul (uint8_to_sint8 0xfeuy); 
  upd sbox 188ul (uint8_to_sint8 0x78uy); upd sbox 189ul (uint8_to_sint8 0xcduy); upd sbox 190ul (uint8_to_sint8 0x5auy); upd sbox 191ul (uint8_to_sint8 0xf4uy); 
  upd sbox 192ul (uint8_to_sint8 0x1fuy); upd sbox 193ul (uint8_to_sint8 0xdduy); upd sbox 194ul (uint8_to_sint8 0xa8uy); upd sbox 195ul (uint8_to_sint8 0x33uy); 
  upd sbox 196ul (uint8_to_sint8 0x88uy); upd sbox 197ul (uint8_to_sint8 0x07uy); upd sbox 198ul (uint8_to_sint8 0xc7uy); upd sbox 199ul (uint8_to_sint8 0x31uy); 
  upd sbox 200ul (uint8_to_sint8 0xb1uy); upd sbox 201ul (uint8_to_sint8 0x12uy); upd sbox 202ul (uint8_to_sint8 0x10uy); upd sbox 203ul (uint8_to_sint8 0x59uy); 
  upd sbox 204ul (uint8_to_sint8 0x27uy); upd sbox 205ul (uint8_to_sint8 0x80uy); upd sbox 206ul (uint8_to_sint8 0xecuy); upd sbox 207ul (uint8_to_sint8 0x5fuy); 
  upd sbox 208ul (uint8_to_sint8 0x60uy); upd sbox 209ul (uint8_to_sint8 0x51uy); upd sbox 210ul (uint8_to_sint8 0x7fuy); upd sbox 211ul (uint8_to_sint8 0xa9uy); 
  upd sbox 212ul (uint8_to_sint8 0x19uy); upd sbox 213ul (uint8_to_sint8 0xb5uy); upd sbox 214ul (uint8_to_sint8 0x4auy); upd sbox 215ul (uint8_to_sint8 0x0duy); 
  upd sbox 216ul (uint8_to_sint8 0x2duy); upd sbox 217ul (uint8_to_sint8 0xe5uy); upd sbox 218ul (uint8_to_sint8 0x7auy); upd sbox 219ul (uint8_to_sint8 0x9fuy); 
  upd sbox 220ul (uint8_to_sint8 0x93uy); upd sbox 221ul (uint8_to_sint8 0xc9uy); upd sbox 222ul (uint8_to_sint8 0x9cuy); upd sbox 223ul (uint8_to_sint8 0xefuy); 
  upd sbox 224ul (uint8_to_sint8 0xa0uy); upd sbox 225ul (uint8_to_sint8 0xe0uy); upd sbox 226ul (uint8_to_sint8 0x3buy); upd sbox 227ul (uint8_to_sint8 0x4duy); 
  upd sbox 228ul (uint8_to_sint8 0xaeuy); upd sbox 229ul (uint8_to_sint8 0x2auy); upd sbox 230ul (uint8_to_sint8 0xf5uy); upd sbox 231ul (uint8_to_sint8 0xb0uy); 
  upd sbox 232ul (uint8_to_sint8 0xc8uy); upd sbox 233ul (uint8_to_sint8 0xebuy); upd sbox 234ul (uint8_to_sint8 0xbbuy); upd sbox 235ul (uint8_to_sint8 0x3cuy); 
  upd sbox 236ul (uint8_to_sint8 0x83uy); upd sbox 237ul (uint8_to_sint8 0x53uy); upd sbox 238ul (uint8_to_sint8 0x99uy); upd sbox 239ul (uint8_to_sint8 0x61uy); 
  upd sbox 240ul (uint8_to_sint8 0x17uy); upd sbox 241ul (uint8_to_sint8 0x2buy); upd sbox 242ul (uint8_to_sint8 0x04uy); upd sbox 243ul (uint8_to_sint8 0x7euy); 
  upd sbox 244ul (uint8_to_sint8 0xbauy); upd sbox 245ul (uint8_to_sint8 0x77uy); upd sbox 246ul (uint8_to_sint8 0xd6uy); upd sbox 247ul (uint8_to_sint8 0x26uy); 
  upd sbox 248ul (uint8_to_sint8 0xe1uy); upd sbox 249ul (uint8_to_sint8 0x69uy); upd sbox 250ul (uint8_to_sint8 0x14uy); upd sbox 251ul (uint8_to_sint8 0x63uy); 
  upd sbox 252ul (uint8_to_sint8 0x55uy); upd sbox 253ul (uint8_to_sint8 0x21uy); upd sbox 254ul (uint8_to_sint8 0x0cuy); upd sbox 255ul (uint8_to_sint8 0x7duy)

#reset-options

val access: sbox:u8s{length sbox = 256} -> idx:byte -> STL byte
  (requires (fun h -> live h sbox))
  (ensures  (fun h0 _ h1 -> h1 == h0))
let access sbox i =
  let rec access_aux: sb:u8s{length sb = 256} -> byte -> ctr:UInt32.t{UInt32.v ctr <= 256} -> byte -> STL byte 
    (requires (fun h -> live h sb))
    (ensures  (fun h0 _ h1 -> h1 == h0))
    = fun sbox i ctr tmp -> 
    if ctr @= 256ul then tmp 
    else let mask = eq_mask i (uint32_to_sint8 ctr) in
	 let tmp = tmp ^| (mask ^& index sbox ctr) in
	 access_aux sbox i (UInt32.add ctr 1ul) tmp in
  access_aux sbox i 0ul (uint8_to_sint8 0uy)

val subBytes_aux_sbox: state:u8s{length state >= 16} -> sbox:u8s{length sbox = 256 /\ disjoint state sbox} -> 
  ctr:UInt32.t{UInt32.v ctr <= 16} -> STL unit
  (requires (fun h -> live h state /\ live h sbox))
  (ensures  (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))
let rec subBytes_aux_sbox state sbox ctr =
  if ctr @= 16ul then ()
  else 
  begin
    let si = index state ctr in
    let si' = access sbox si in
    upd state ctr si';
    subBytes_aux_sbox state sbox (UInt32.add ctr 1ul)
  end

val subBytes_sbox: state:u8s{length state >= 16} -> sbox:u8s{length sbox = 256 /\ disjoint state sbox} -> STL unit
  (requires (fun h -> live h state /\ live h sbox))
  (ensures  (fun h0 _ h1 -> modifies_1 state h0 h1 /\ live h1 state))
let subBytes_sbox state sbox =
  subBytes_aux_sbox state sbox 0ul

val shiftRows: state:u8s{length state >= 16} -> STL unit
  (requires (fun h -> live h state))
  (ensures  (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))
let shiftRows state =
  let i = 1ul in
  let tmp = index state i in
  upd state i      (index state (i@+4ul)); 
  upd state (i@+4ul)  (index state (i@+8ul)); 
  upd state (i@+8ul)  (index state (i@+12ul)); 
  upd state (i@+12ul) tmp;
  let i = 2ul in
  let tmp = index state i in
  upd state i      (index state (i@+8ul)); 
  upd state (i@+8ul)  tmp; 
  let tmp = index state (i@+4ul) in
  upd state (i@+4ul)  (index state (i@+12ul)); 
  upd state (i@+12ul) tmp;
  let i = 3ul in
  let tmp = index state i in
  upd state i      (index state (i@+12ul)); 
  upd state (i@+12ul) (index state (i@+8ul));
  upd state (i@+8ul)  (index state (i@+4ul)); 
  upd state (i@+4ul)  tmp; 
  ()
       
#reset-options "--z3timeout 20"
#set-options "--lax"

val mixColumns: state:u8s{length state >= 16} -> STL unit
  (requires (fun h -> live h state))
  (ensures  (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))
let mixColumns state =
  let c = 0ul in
  let s0 = index state (0ul@+(4ul@*c)) in
  let s1 = index state (1ul@+(4ul@*c)) in
  let s2 = index state (2ul@+(4ul@*c)) in
  let s3 = index state (3ul@+(4ul@*c)) in
  upd state ((4ul@*c)@+0ul) (multiply (uint8_to_sint8 0x2uy) s0 ^^ multiply (uint8_to_sint8 0x3uy) s1 ^^ s2 ^^ s3);
  upd state ((4ul@*c)@+1ul) (multiply (uint8_to_sint8 0x2uy) s1 ^^ multiply (uint8_to_sint8 0x3uy) s2 ^^ s3 ^^ s0);
  upd state ((4ul@*c)@+2ul) (multiply (uint8_to_sint8 0x2uy) s2 ^^ multiply (uint8_to_sint8 0x3uy) s3 ^^ s0 ^^ s1);
  upd state ((4ul@*c)@+3ul) (multiply (uint8_to_sint8 0x2uy) s3 ^^ multiply (uint8_to_sint8 0x3uy) s0 ^^ s1 ^^ s2);
  let c = 1ul in
  let s0 = index state (0ul@+(4ul@*c)) in
  let s1 = index state (1ul@+(4ul@*c)) in
  let s2 = index state (2ul@+(4ul@*c)) in
  let s3 = index state (3ul@+(4ul@*c)) in
  upd state ((4ul@*c)@+0ul) (multiply (uint8_to_sint8 0x2uy) s0 ^^ multiply (uint8_to_sint8 0x3uy) s1 ^^ s2 ^^ s3);
  upd state ((4ul@*c)@+1ul) (multiply (uint8_to_sint8 0x2uy) s1 ^^ multiply (uint8_to_sint8 0x3uy) s2 ^^ s3 ^^ s0);
  upd state ((4ul@*c)@+2ul) (multiply (uint8_to_sint8 0x2uy) s2 ^^ multiply (uint8_to_sint8 0x3uy) s3 ^^ s0 ^^ s1);
  upd state ((4ul@*c)@+3ul) (multiply (uint8_to_sint8 0x2uy) s3 ^^ multiply (uint8_to_sint8 0x3uy) s0 ^^ s1 ^^ s2);
  let c = 2ul in
  let s0 = index state (0ul@+(4ul@*c)) in
  let s1 = index state (1ul@+(4ul@*c)) in
  let s2 = index state (2ul@+(4ul@*c)) in
  let s3 = index state (3ul@+(4ul@*c)) in
  upd state ((4ul@*c)@+0ul) (multiply (uint8_to_sint8 0x2uy) s0 ^^ multiply (uint8_to_sint8 0x3uy) s1 ^^ s2 ^^ s3);
  upd state ((4ul@*c)@+1ul) (multiply (uint8_to_sint8 0x2uy) s1 ^^ multiply (uint8_to_sint8 0x3uy) s2 ^^ s3 ^^ s0);
  upd state ((4ul@*c)@+2ul) (multiply (uint8_to_sint8 0x2uy) s2 ^^ multiply (uint8_to_sint8 0x3uy) s3 ^^ s0 ^^ s1);
  upd state ((4ul@*c)@+3ul) (multiply (uint8_to_sint8 0x2uy) s3 ^^ multiply (uint8_to_sint8 0x3uy) s0 ^^ s1 ^^ s2);
  let c = 3ul in
  let s0 = index state (0ul@+(4ul@*c)) in
  let s1 = index state (1ul@+(4ul@*c)) in
  let s2 = index state (2ul@+(4ul@*c)) in
  let s3 = index state (3ul@+(4ul@*c)) in
  upd state ((4ul@*c)@+0ul) (multiply (uint8_to_sint8 0x2uy) s0 ^^ multiply (uint8_to_sint8 0x3uy) s1 ^^ s2 ^^ s3);
  upd state ((4ul@*c)@+1ul) (multiply (uint8_to_sint8 0x2uy) s1 ^^ multiply (uint8_to_sint8 0x3uy) s2 ^^ s3 ^^ s0);
  upd state ((4ul@*c)@+2ul) (multiply (uint8_to_sint8 0x2uy) s2 ^^ multiply (uint8_to_sint8 0x3uy) s3 ^^ s0 ^^ s1);
  upd state ((4ul@*c)@+3ul) (multiply (uint8_to_sint8 0x2uy) s3 ^^ multiply (uint8_to_sint8 0x3uy) s0 ^^ s1 ^^ s2);
  ()

#reset-options

val addRoundKey: state:u8s{length state >= 16} -> w:u8s -> round:UInt32.t -> St unit
let addRoundKey state w round =
  let c = 0ul in
  let s0 = index state ((4ul@*c)@+0ul) in
  let s1 = index state ((4ul@*c)@+1ul) in
  let s2 = index state ((4ul@*c)@+2ul) in
  let s3 = index state ((4ul@*c)@+3ul) in
  let w0 = index w (((4ul@*round)@*nb)@+(4ul@*c)@+0ul) in
  let w1 = index w (((4ul@*round)@*nb)@+(4ul@*c)@+1ul) in
  let w2 = index w (((4ul@*round)@*nb)@+(4ul@*c)@+2ul) in
  let w3 = index w (((4ul@*round)@*nb)@+(4ul@*c)@+3ul) in
  upd state ((4ul@*c)@+0ul) (s0 ^^ w0);
  upd state ((4ul@*c)@+1ul) (s1 ^^ w1);
  upd state ((4ul@*c)@+2ul) (s2 ^^ w2);
  upd state ((4ul@*c)@+3ul) (s3 ^^ w3);
  let c = 1ul in
  let s0 = index state ((4ul@*c)@+0ul) in
  let s1 = index state ((4ul@*c)@+1ul) in
  let s2 = index state ((4ul@*c)@+2ul) in
  let s3 = index state ((4ul@*c)@+3ul) in
  let w0 = index w (((4ul@*round)@*nb)@+(4ul@*c)@+0ul) in
  let w1 = index w (((4ul@*round)@*nb)@+(4ul@*c)@+1ul) in
  let w2 = index w (((4ul@*round)@*nb)@+(4ul@*c)@+2ul) in
  let w3 = index w (((4ul@*round)@*nb)@+(4ul@*c)@+3ul) in
  upd state ((4ul@*c)@+0ul) (s0 ^^ w0);
  upd state ((4ul@*c)@+1ul) (s1 ^^ w1);
  upd state ((4ul@*c)@+2ul) (s2 ^^ w2);
  upd state ((4ul@*c)@+3ul) (s3 ^^ w3);
  let c = 2ul in
  let s0 = index state ((4ul@*c)@+0ul) in
  let s1 = index state ((4ul@*c)@+1ul) in
  let s2 = index state ((4ul@*c)@+2ul) in
  let s3 = index state ((4ul@*c)@+3ul) in
  let w0 = index w (((4ul@*round)@*nb)@+(4ul@*c)@+0ul) in
  let w1 = index w (((4ul@*round)@*nb)@+(4ul@*c)@+1ul) in
  let w2 = index w (((4ul@*round)@*nb)@+(4ul@*c)@+2ul) in
  let w3 = index w (((4ul@*round)@*nb)@+(4ul@*c)@+3ul) in
  upd state ((4ul@*c)@+0ul) (s0 ^^ w0);
  upd state ((4ul@*c)@+1ul) (s1 ^^ w1);
  upd state ((4ul@*c)@+2ul) (s2 ^^ w2);
  upd state ((4ul@*c)@+3ul) (s3 ^^ w3);
  let c = 3ul in
  let s0 = index state ((4ul@*c)@+0ul) in
  let s1 = index state ((4ul@*c)@+1ul) in
  let s2 = index state ((4ul@*c)@+2ul) in
  let s3 = index state ((4ul@*c)@+3ul) in
  let w0 = index w (((4ul@*round)@*nb)@+(4ul@*c)@+0ul) in
  let w1 = index w (((4ul@*round)@*nb)@+(4ul@*c)@+1ul) in
  let w2 = index w (((4ul@*round)@*nb)@+(4ul@*c)@+2ul) in
  let w3 = index w (((4ul@*round)@*nb)@+(4ul@*c)@+3ul) in
  upd state ((4ul@*c)@+0ul) (s0 ^^ w0);
  upd state ((4ul@*c)@+1ul) (s1 ^^ w1);
  upd state ((4ul@*c)@+2ul) (s2 ^^ w2);
  upd state ((4ul@*c)@+3ul) (s3 ^^ w3);
  ()

val cipher_loop: state:u8s -> w:u8s -> u8s -> round:UInt32.t -> St unit
let rec cipher_loop state w sbox round = 
  if round = 14ul then ()
  else begin
    subBytes_sbox state sbox;
    shiftRows state;
    mixColumns state;
    addRoundKey state w round; 
    cipher_loop state w sbox (round@+1ul)
  end

val cipher: out:u8s{length out = 4 * UInt32.v nb} -> input:u8s{length input = 4*UInt32.v nb} -> w:u8s{length w = 4 * (UInt32.v nr+1)} -> sbox:u8s{length sbox = 256} -> St unit
let cipher out input w sbox =
  let state = create (uint8_to_sint8 0uy) (4ul@*nb) in
  blit input 0ul state 0ul (4ul@*nb);
  addRoundKey state w 0ul;
  cipher_loop state w sbox 1ul;
  subBytes_sbox state sbox;
  shiftRows state;
  addRoundKey state w nr;
  blit state 0ul out 0ul (4ul@*nb);
  ()

val rotWord: word:u8s{length word = 4} -> St unit
let rotWord word =
  let w0 = index word 0ul in
  let w1 = index word 1ul in
  let w2 = index word 2ul in
  let w3 = index word 3ul in
  upd word 0ul w1;
  upd word 1ul w2;
  upd word 2ul w3;
  upd word 3ul w0;
  ()
  
val subWord: word:u8s{length word = 4} -> sbox:u8s -> St unit
let subWord word sbox =
  let w0 = index word 0ul in
  let w1 = index word 1ul in
  let w2 = index word 2ul in
  let w3 = index word 3ul in
  upd word 0ul (access sbox w0);
  upd word 1ul (access sbox w1);
  upd word 2ul (access sbox w2);
  upd word 3ul (access sbox w3);
  ()  
  
val rcon: UInt32.t -> byte -> Tot byte
let rec rcon i tmp =
  if i = 1ul then tmp
  else begin
    let tmp = multiply (uint8_to_sint8 0x2uy) tmp in    
    rcon (i@-1ul) tmp
  end

val keyExpansion_aux: u8s -> u8s -> u8s -> u8s -> UInt32.t -> St unit
let rec keyExpansion_aux key w temp sbox i =
  if i @= 240ul then ()
  else begin
    blit w (i@-4ul) temp 0ul 4ul;
    if (i@/4ul) @% nk = 0ul then (
      rotWord temp;
      subWord temp sbox;
      upd temp 0ul (index temp 0ul ^^ rcon ((i@/4ul)@/nk) (uint8_to_sint8 1uy)) 
    ) else if (((i@/4ul) @% nk) @= 4ul) then (
      subWord temp sbox
    );
    let w0 = index w (i@+0ul@-(4ul@*nk)) in
    let w1 = index w (i@+1ul@-(4ul@*nk)) in
    let w2 = index w (i@+2ul@-(4ul@*nk)) in
    let w3 = index w (i@+3ul@-(4ul@*nk)) in
    let t0 = index temp (0ul) in
    let t1 = index temp (1ul) in
    let t2 = index temp (2ul) in
    let t3 = index temp (3ul) in
    upd w (i@+0ul) (t0 ^^ w0);
    upd w (i@+1ul) (t1 ^^ w1);
    upd w (i@+2ul) (t2 ^^ w2);
    upd w (i@+3ul) (t3 ^^ w3);
    keyExpansion_aux key w temp sbox (i@+4ul)
  end  
    
val keyExpansion: key:u8s{length key = 4 * UInt32.v nk} -> w:u8s{length w = 4 * (UInt32.v nb * (UInt32.v nr+1))} -> sbox:u8s -> St unit
let keyExpansion key w sbox =
  let temp = create (uint8_to_sint8 0uy) 4ul in
  blit key 0ul w 0ul (4ul@*nk);
  let i = 4ul @* nk in
  keyExpansion_aux key w temp sbox i

val invShiftRows: state:u8s{length state = 16} -> St unit
let invShiftRows state =
  let i = 3ul in
  let tmp = index state i in
  upd state i      (index state (i@+4ul)); 
  upd state (i@+4ul)  (index state (i@+8ul)); 
  upd state (i@+8ul)  (index state (i@+12ul)); 
  upd state (i@+12ul) tmp;
  let i = 2ul in
  let tmp = index state i in
  upd state i      (index state (i@+8ul)); 
  upd state (i@+8ul)  tmp; 
  let tmp = index state (i@+4ul) in
  upd state (i@+4ul)  (index state (i@+12ul)); 
  upd state (i@+12ul) tmp;
  let i = 1ul in
  let tmp = index state i in
  upd state i      (index state (i@+12ul)); 
  upd state (i@+12ul) (index state (i@+8ul));
  upd state (i@+8ul)  (index state (i@+4ul)); 
  upd state (i@+4ul)  tmp; 
  ()

val invSubBytes_aux_sbox: state:u8s -> sbox:u8s -> ctr:UInt32.t -> St unit
let rec invSubBytes_aux_sbox state sbox ctr =
  if ctr = 16ul then () 
  else begin 
    let si = index state ctr in
    let si' = access sbox si in
    upd state ctr si';
    invSubBytes_aux_sbox state sbox (ctr@+1ul)
  end

val invSubBytes_sbox: state:u8s -> u8s -> St unit
let invSubBytes_sbox state sbox = 
  invSubBytes_aux_sbox state sbox 0ul
       
val invMixColumns: u8s -> St unit
let invMixColumns state =
  let c = 0ul in
  let s0 = index state (0ul@+(4ul@*c)) in
  let s1 = index state (1ul@+(4ul@*c)) in
  let s2 = index state (2ul@+(4ul@*c)) in
  let s3 = index state (3ul@+(4ul@*c)) in
  upd state ((4ul@*c)@+0ul) (multiply (uint8_to_sint8 0xeuy) s0 ^^ multiply (uint8_to_sint8 0xbuy) s1 
	       ^^ multiply (uint8_to_sint8 0xduy) s2 ^^ multiply (uint8_to_sint8 0x9uy) s3);
  upd state ((4ul@*c)@+1ul) (multiply (uint8_to_sint8 0xeuy) s1 ^^ multiply (uint8_to_sint8 0xbuy) s2 
	       ^^ multiply (uint8_to_sint8 0xduy) s3 ^^ multiply (uint8_to_sint8 0x9uy) s0);
  upd state ((4ul@*c)@+2ul) (multiply (uint8_to_sint8 0xeuy) s2 ^^ multiply (uint8_to_sint8 0xbuy) s3 
	       ^^ multiply (uint8_to_sint8 0xduy) s0 ^^ multiply (uint8_to_sint8 0x9uy) s1);
  upd state ((4ul@*c)@+3ul) (multiply (uint8_to_sint8 0xeuy) s3 ^^ multiply (uint8_to_sint8 0xbuy) s0 
	       ^^ multiply (uint8_to_sint8 0xduy) s1 ^^ multiply (uint8_to_sint8 0x9uy) s2);
  let c = 1ul in
  let s0 = index state (0ul@+(4ul@*c)) in
  let s1 = index state (1ul@+(4ul@*c)) in
  let s2 = index state (2ul@+(4ul@*c)) in
  let s3 = index state (3ul@+(4ul@*c)) in
  upd state ((4ul@*c)@+0ul) (multiply (uint8_to_sint8 0xeuy) s0 ^^ multiply (uint8_to_sint8 0xbuy) s1 
	       ^^ multiply (uint8_to_sint8 0xduy) s2 ^^ multiply (uint8_to_sint8 0x9uy) s3);
  upd state ((4ul@*c)@+1ul) (multiply (uint8_to_sint8 0xeuy) s1 ^^ multiply (uint8_to_sint8 0xbuy) s2 
	       ^^ multiply (uint8_to_sint8 0xduy) s3 ^^ multiply (uint8_to_sint8 0x9uy) s0);
  upd state ((4ul@*c)@+2ul) (multiply (uint8_to_sint8 0xeuy) s2 ^^ multiply (uint8_to_sint8 0xbuy) s3 
	       ^^ multiply (uint8_to_sint8 0xduy) s0 ^^ multiply (uint8_to_sint8 0x9uy) s1);
  upd state ((4ul@*c)@+3ul) (multiply (uint8_to_sint8 0xeuy) s3 ^^ multiply (uint8_to_sint8 0xbuy) s0 
	       ^^ multiply (uint8_to_sint8 0xduy) s1 ^^ multiply (uint8_to_sint8 0x9uy) s2);
  let c = 2ul in
  let s0 = index state (0ul@+(4ul@*c)) in
  let s1 = index state (1ul@+(4ul@*c)) in
  let s2 = index state (2ul@+(4ul@*c)) in
  let s3 = index state (3ul@+(4ul@*c)) in
  upd state ((4ul@*c)@+0ul) (multiply (uint8_to_sint8 0xeuy) s0 ^^ multiply (uint8_to_sint8 0xbuy) s1 
	       ^^ multiply (uint8_to_sint8 0xduy) s2 ^^ multiply (uint8_to_sint8 0x9uy) s3);
  upd state ((4ul@*c)@+1ul) (multiply (uint8_to_sint8 0xeuy) s1 ^^ multiply (uint8_to_sint8 0xbuy) s2 
	       ^^ multiply (uint8_to_sint8 0xduy) s3 ^^ multiply (uint8_to_sint8 0x9uy) s0);
  upd state ((4ul@*c)@+2ul) (multiply (uint8_to_sint8 0xeuy) s2 ^^ multiply (uint8_to_sint8 0xbuy) s3 
	       ^^ multiply (uint8_to_sint8 0xduy) s0 ^^ multiply (uint8_to_sint8 0x9uy) s1);
  upd state ((4ul@*c)@+3ul) (multiply (uint8_to_sint8 0xeuy) s3 ^^ multiply (uint8_to_sint8 0xbuy) s0 
	       ^^ multiply (uint8_to_sint8 0xduy) s1 ^^ multiply (uint8_to_sint8 0x9uy) s2);
  let c = 3ul in
  let s0 = index state (0ul@+(4ul@*c)) in
  let s1 = index state (1ul@+(4ul@*c)) in
  let s2 = index state (2ul@+(4ul@*c)) in
  let s3 = index state (3ul@+(4ul@*c)) in
  upd state ((4ul@*c)@+0ul) (multiply (uint8_to_sint8 0xeuy) s0 ^^ multiply (uint8_to_sint8 0xbuy) s1 
	       ^^ multiply (uint8_to_sint8 0xduy) s2 ^^ multiply (uint8_to_sint8 0x9uy) s3);
  upd state ((4ul@*c)@+1ul) (multiply (uint8_to_sint8 0xeuy) s1 ^^ multiply (uint8_to_sint8 0xbuy) s2 
	       ^^ multiply (uint8_to_sint8 0xduy) s3 ^^ multiply (uint8_to_sint8 0x9uy) s0);
  upd state ((4ul@*c)@+2ul) (multiply (uint8_to_sint8 0xeuy) s2 ^^ multiply (uint8_to_sint8 0xbuy) s3 
	       ^^ multiply (uint8_to_sint8 0xduy) s0 ^^ multiply (uint8_to_sint8 0x9uy) s1);
  upd state ((4ul@*c)@+3ul) (multiply (uint8_to_sint8 0xeuy) s3 ^^ multiply (uint8_to_sint8 0xbuy) s0 
	       ^^ multiply (uint8_to_sint8 0xduy) s1 ^^ multiply (uint8_to_sint8 0x9uy) s2);
  ()

val inv_cipher_loop: state:u8s -> w:u8s -> u8s -> round:UInt32.t -> St unit
let rec inv_cipher_loop state w sbox round = 
  if round = 0ul then ()
  else begin
    invShiftRows state;
    invSubBytes_sbox state sbox;
    addRoundKey state w round; 
    invMixColumns state;
    inv_cipher_loop state w sbox (round@-1ul)
  end

val inv_cipher: out:u8s{length out = 4 * UInt32.v nb} -> input:u8s{length input = 4* UInt32.v nb} -> w:u8s{length w = 4 * (UInt32.v nr+1)} -> sbox:u8s{length sbox = 256} -> St unit
let inv_cipher out input w sbox =
  let state = create (uint8_to_sint8 0uy) (4ul@*nb) in
  blit input 0ul state 0ul (4ul@*nb);
  addRoundKey state w nr;
  inv_cipher_loop state w sbox 13ul;
  invShiftRows state;
  invSubBytes_sbox state sbox;
  addRoundKey state w 0ul;
  blit state 0ul out 0ul (4ul@*nb)
