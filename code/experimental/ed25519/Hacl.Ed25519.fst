module Hacl.Ed25519

let sign signature secret len msg =
  Hacl.Impl.Ed25519.Sign.sign signature secret len msg

let verify public_key len msg signature =
  Hacl.Impl.Ed25519.Verify.verify public_key len msg signature

let secret_to_public output secret =
  Hacl.Impl.Ed25519.SecretToPublic.secret_to_public output secret

let expand_keys ks secret =
  Hacl.Impl.Ed25519.Sign.Expanded.expand_keys ks secret

let sign_expanded signature ks len msg =
  Hacl.Impl.Ed25519.Sign.Expanded.sign signature ks len msg
