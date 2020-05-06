module Hacl.Ed25519

let sign signature priv len msg =
  Hacl.Impl.Ed25519.Sign.sign signature priv len msg

let verify pub len msg signature =
  Hacl.Impl.Ed25519.Verify.verify pub len msg signature

let secret_to_public pub priv =
  Hacl.Impl.Ed25519.SecretToPublic.secret_to_public pub priv

let expand_keys ks priv =
  Hacl.Impl.Ed25519.Sign.Expanded.expand_keys ks priv

let sign_expanded signature ks len msg =
  Hacl.Impl.Ed25519.Sign.Expanded.sign signature ks len msg
