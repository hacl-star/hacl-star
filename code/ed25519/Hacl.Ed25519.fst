module Hacl.Ed25519

let sign signature secret msg len =
  Hacl.Impl.Ed25519.Sign.sign signature secret msg len

let verify output msg len signature =
  Hacl.Impl.Ed25519.Verify.verify output msg len signature

let secret_to_public output secret =
  Hacl.Impl.Ed25519.SecretToPublic.secret_to_public output secret

let expand_keys ks secret =
  Hacl.Impl.Ed25519.Sign.Expanded.expand_keys ks secret

let sign_expanded signature ks msg len =
  Hacl.Impl.Ed25519.Sign.Expanded.sign signature ks msg len
