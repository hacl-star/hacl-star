module EverCrypt.Ed25519

/// For now, only one implementation... to be improved in the future.

let secret_to_public public_key private_key =
  Hacl.Ed25519.secret_to_public public_key private_key

let expand_keys expanded_keys private_key =
  Hacl.Ed25519.expand_keys expanded_keys private_key

let sign_expanded signature expanded_keys msg_len msg =
  Hacl.Ed25519.sign_expanded signature expanded_keys msg_len msg

let sign signature private_key msg_len msg =
  Hacl.Ed25519.sign signature private_key msg_len msg

let verify public_key msg_len msg signature =
  Hacl.Ed25519.verify public_key msg_len msg signature
