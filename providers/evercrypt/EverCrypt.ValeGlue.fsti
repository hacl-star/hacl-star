module EverCrypt.ValeGlue

/// The functions is this module are implemented in C and do a little bit of
/// adapting / gluing before calling Vale. The implementation is in
/// c/evercrypt_vale_glue.c. Eventually the glue code should be written in Low*.

open EverCrypt.Helpers

///  SHA256

/// Incremental API
val sha256_init: state:uint32_p -> Stack_ unit
val sha256_update: state:uint32_p -> data:uint8_p -> Stack_ unit
val sha256_update_multi: state:uint32_p -> data:uint8_p -> n:uint32_t -> Stack_ unit
val sha256_update_last: state:uint32_p -> data:uint8_p -> n:uint32_t -> Stack_ unit
val sha256_finish: state:uint32_p -> data:uint8_p -> Stack_ unit
val sha256_hash: dst:uint8_p -> data:uint8_p -> n:uint32_t -> Stack_ unit

/// From what I can tell, we don't have a standalone API for Vale's SHA256, yet.
