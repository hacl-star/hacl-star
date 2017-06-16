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

module Ed25519

let sign signature secret msg len =
  Hacl.Impl.Ed25519.Sign.sign signature secret msg len

let verify public msg len signature =
  Hacl.Impl.Ed25519.Verify.verify public msg len signature

let secret_to_public out secret =
  Hacl.Impl.Ed25519.SecretToPublic.secret_to_public out secret
