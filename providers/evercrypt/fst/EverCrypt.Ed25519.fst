module EverCrypt.Ed25519

/// For now, only one implementation... to be improved in the future.

let sign signature secret len msg =
  Hacl.Ed25519.sign signature secret len msg

let verify output len msg signature =
  Hacl.Ed25519.verify output len msg signature

let secret_to_public output secret =
  Hacl.Ed25519.secret_to_public output secret

let expand_keys ks secret =
  Hacl.Ed25519.expand_keys ks secret

let sign_expanded signature ks len msg =
  Hacl.Ed25519.sign_expanded signature ks len msg
