module EverCrypt.Vale

open EverCrypt.Helpers

///  SHA256

/// Incremental API
val sha256_init: state:uint32_p -> Stack_ unit
val sha256_update: state:uint32_p -> data:uint8_p -> Stack_ unit
val sha256_update_multi: state:uint32_p -> data:uint8_p -> n:uint32_t -> Stack_ unit
val sha256_update_last: state:uint32_p -> data:uint8_p -> n:uint32_t -> Stack_ unit
val sha256_finish: state:uint32_p -> data:uint8_p -> unit

/// From what I can tell, we don't have a standalone API for Vale's SHA256, yet.
