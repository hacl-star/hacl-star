module Spec.HMAC_DRBG.Vectors

open Spec.Hash.Definitions

#set-options "--max_fuel 0 --max_ifuel 0"

///
/// HMAC-DRBG test vectors from HIST CAVP
/// https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program/random-number-generators#DRBG
///

/// BEGIN: excerpt of Test.Lowstarize
/// Avoids having it as a dependency, but would be better to move this to /lib

noextract
val is_hex_digit: Char.char -> bool
let is_hex_digit = function
  | '0'
  | '1'
  | '2'
  | '3'
  | '4'
  | '5'
  | '6'
  | '7'
  | '8'
  | '9'
  | 'a' | 'A'
  | 'b' | 'B'
  | 'c' | 'C'
  | 'd' | 'D'
  | 'e' | 'E'
  | 'f' | 'F' -> true
  | _ -> false

noextract
type hex_digit = c:Char.char{is_hex_digit c}

noextract
val int_of_hex: c:hex_digit -> int
let int_of_hex = function
  | '0' -> 0
  | '1' -> 1
  | '2' -> 2
  | '3' -> 3
  | '4' -> 4
  | '5' -> 5
  | '6' -> 6
  | '7' -> 7
  | '8' -> 8
  | '9' -> 9
  | 'a' | 'A' -> 10
  | 'b' | 'B' -> 11
  | 'c' | 'C' -> 12
  | 'd' | 'D' -> 13
  | 'e' | 'E' -> 14
  | 'f' | 'F' -> 15

noextract
val byte_of_hex: a:hex_digit -> b:hex_digit -> int
let byte_of_hex a b =
  FStar.Mul.(int_of_hex a * 16 + int_of_hex b)

noextract unfold
type hex_string =
  s:string{normalize (String.strlen s % 2 = 0) /\
           normalize (List.Tot.for_all is_hex_digit (String.list_of_string s))}

/// END: Excerpt of Test.Lowstarize

type vec = {
  a: hash_alg;
  entropy_input: hex_string;
  nonce: hex_string;
  personalization_string: hex_string;
  entropy_input_reseed: hex_string;
  additional_input_reseed: hex_string;
  additional_input_1: hex_string;
  additional_input_2: hex_string;  
  returned_bits: hex_string;
}

let test_vectors : list vec = [
  { 
  a = SHA1;
  entropy_input = "79349bbf7cdda5799557866621c91383";
  nonce = "1146733abf8c35c8";
  personalization_string = "";
  entropy_input_reseed = "c7215b5b96c48e9b338c74e3e99dfedf";
  additional_input_reseed = "";
  additional_input_1 = "";
  additional_input_2 = "";
  returned_bits = "c6a16ab8d420706f0f34ab7fec5adca9d8ca3a133e159ca6ac43c6f8a2be22834a4c0a0affb10d7194f1c1a5cf7322ec1ae0964ed4bf122746e087fdb5b3e91b3493d5bb98faed49e85f130fc8a459b7";
  };
  {
  a = SHA1;
  entropy_input = "c2e9a6e2e29f47dee0e808660c446a4f";
  nonce = "aff465073a97862c";
  personalization_string = "";
  entropy_input_reseed = "2ab6787095e944c5276d29bbbbd7a777";
  additional_input_reseed = "358ffeab6a24f932abd4c9577f84cb13";
  additional_input_1 = "37578c2d9b68d43d6c83164a4c43ce37";
  additional_input_2 = "02a7c9575d9527a33df9fb566373db3a";
  returned_bits = "fcd318c83563f72e5a21d4a93a84254e0c3bb6d3ded55c3d5939dbd5d1525062fd587a422012437aeb88589e669e5a5d57f7ebb16e30590f6debd0eced84f8e57d47a3d123a52361145a8fab258ed19b";
  };
  {
  a = SHA2_256;
  entropy_input = "06032cd5eed33f39265f49ecb142c511da9aff2af71203bffaf34a9ca5bd9c0d";
  nonce = "0e66f71edc43e42a45ad3c6fc6cdc4df";
  personalization_string = "";
  entropy_input_reseed = "01920a4e669ed3a85ae8a33b35a74ad7fb2a6bb4cf395ce00334a9c9a5a5d552";  
  additional_input_reseed = "";
  additional_input_1 = "";
  additional_input_2 = "";
  returned_bits = "76fc79fe9b50beccc991a11b5635783a83536add03c157fb30645e611c2898bb2b1bc215000209208cd506cb28da2a51bdb03826aaf2bd2335d576d519160842e7158ad0949d1a9ec3e66ea1b1a064b005de914eac2e9d4f2d72a8616a80225422918250ff66a41bd2f864a6a38cc5b6499dc43f7f2bd09e1e0f8f5885935124";
  };
  {
  a = SHA2_256;
  entropy_input = "93161b2dc08cb0fd50171141c865a841ca935cfdd2b5907d6ff8ab0348c4ceb0";
  nonce = "5cb9f6e5912b90c3349a50ab881b35a1";
personalization_string =  "0dceb4a36326c4df1685df43fddeecb5d0c76f00eb44826694f27e610290f6e1";
  entropy_input_reseed = "d8e9be44b5f293482548d4787762ebfb03c73c40e45385e8b98907cd66f493dd";
  additional_input_reseed = "105a8f85d6959f3e043ef508cfea21d52123f03b7aea8034c4eec761eaba1fee";
  additional_input_1 = "bf781f7e489d9b4b5aa5ee6d1796468af672a8d25f311edf3c4b4dbf433d703f";
  additional_input_2 = "c81d6bcf1e5bf37e39dda1735c6f193df115b1a854a12e7cafe060afe4589335";
  returned_bits = "4306628124d0100fade7eaaf5edf227d50771f9e5f2e1e983800eef9a39fde0b0c280e63c8728d836b5b93ea794a32c1c04cfc54bd5300e3febb5fe2e1023eded8d7cd180279a598f76823e8d5a7dffcc93a09deec5d1f80838e938fba4de9f47e94b99382ae55f116df9c3b3ddf7e50516e203645852a415796f03a86418107";
  };
  {
  a = SHA2_384;
  entropy_input = "096349506f3a7653d54db7ec1d09e93413edd175b6ddbeb00e56752a520ac8ff";
  nonce = "fc7983b918acadaa71a67e1624f1b502";
  personalization_string = "";
  entropy_input_reseed = "4260a0495fdaba58aae41df82505012d480c8e4f751fd7ebc39f9becd694b2a3";
  additional_input_reseed = "";
  additional_input_1 = "";
  additional_input_2 = "";
  returned_bits = "f4c7bec0c26cf3892d214549ac6f3d82f34c6966d4295099ee56166e879a70ecae130251facda351e903d877b6c5eab5153ce87ba6c7cf8bcc61cbd14cfbe34cf1ed43678aee69cd87b60e6bcb6ff48ebd44ce9e31982d8fe20aec34fa51d625f845f61056575969bf785c2ffab4dcc754f13de63423e94bad8d5e166d96a62a602d3ee4045df162028b89cac45e6207d9097f2b3ac0ab17729251985f276f1287f5c56cc9ba1a79fbdbb291f3a945fbfdbd63cf13b82ec91f7b1085b33279e3";
  };
  {
  a = SHA2_512;
  entropy_input = "48c121b18733af15c27e1dd9ba66a9a81a5579cdba0f5b657ec53c2b9e90bbf6";
  nonce = "bbb7c777428068fad9970891f879b1af";
  personalization_string = "";  
  entropy_input_reseed = "e0ffefdadb9ccf990504d568bdb4d862cbe17ccce6e22dfcab8b4804fd21421a";
  additional_input_reseed = "";
  additional_input_1 = "";
  additional_input_2 = "";
  returned_bits = "05da6aac7d980da038f65f392841476d37fe70fbd3e369d1f80196e66e54b8fadb1d60e1a0f3d4dc173769d75fc3410549d7a843270a54a068b4fe767d7d9a59604510a875ad1e9731c8afd0fd50b825e2c50d062576175106a9981be37e02ec7c5cd0a69aa0ca65bddaee1b0de532e10cfa1f5bf6a026e47379736a099d6750ab121dbe3622b841baf8bdcbe875c85ba4b586b8b5b57b0fecbec08c12ff2a9453c47c6e32a52103d972c62ab9affb8e728a31fcefbbccc556c0f0a35f4b10ace2d96b906e36cbb72233201e536d3e13b045187b417d2449cad1edd192e061f12d22147b0a176ea8d9c4c35404395b6502ef333a813b6586037479e0fa3c6a23";
  };
]
