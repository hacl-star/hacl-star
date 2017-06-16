//
//   Copyright 2016-2017  INRIA and Microsoft Research
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

module Crypto.Indexing

type id0 = {
 a: aeadAlg;
 aesi: aesImpl;
}
let id = id0

inline_for_extraction let aeadAlg_of_id i = i.a

inline_for_extraction let macAlg_of_id i =
  match i.a with
  | AES_128_GCM       -> GHASH
  | AES_256_GCM       -> GHASH
  | CHACHA20_POLY1305 -> POLY1305

inline_for_extraction let cipherAlg_of_id i =
  match i.a with
  | AES_128_GCM       -> AES128
  | AES_256_GCM       -> AES256
  | CHACHA20_POLY1305 -> CHACHA20

inline_for_extraction let aesImpl_of_id (i:id) = i.aesi

let aeadAlg_cipherAlg i = ()

let testId (a:aeadAlg) = {a=a; aesi=HaclAES;}

