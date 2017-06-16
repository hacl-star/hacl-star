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

module Hacl.Bignum.Constants

inline_for_extraction let prime:pos = assert_norm(pow2 255 > 19); pow2 255 - 19
inline_for_extraction let word_size = 64
inline_for_extraction let len = 5
inline_for_extraction let limb_size = 51
inline_for_extraction let keylen = 32
inline_for_extraction let limb = Hacl.UInt64.t
inline_for_extraction let wide = Hacl.UInt128.t
inline_for_extraction let a24 = assert_norm(121665 < pow2 64); 121665uL
