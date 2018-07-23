module EverCrypt.StaticConfig

/// This module allows us to statically eliminate symbols from the resulting
/// library by setting, for instance, openssl to false.

inline_for_extraction let hacl = true
inline_for_extraction let vale = true
inline_for_extraction let openssl = false
inline_for_extraction let bcrypt = true
