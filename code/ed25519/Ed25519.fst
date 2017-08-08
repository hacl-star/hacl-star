module Ed25519

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

let sign signature secret msg len =
  Hacl.Impl.Ed25519.Sign.sign signature secret msg len

let verify public msg len signature =
  Hacl.Impl.Ed25519.Verify.verify public msg len signature

let secret_to_public out secret =
  Hacl.Impl.Ed25519.SecretToPublic.secret_to_public out secret
