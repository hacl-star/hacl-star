module EverCrypt

open FStar.HyperStack.ST
open EverCrypt.Helpers

include EverCrypt.Native

///  SHA256

/// Incremental API
val sha256_init: state:uint32_p -> Stack_ unit
val sha256_update: state:uint32_p -> data:uint8_p -> Stack_ unit
val sha256_update_multi: state:uint32_p -> data:uint8_p -> n:uint32_t -> Stack_ unit
val sha256_update_last: state:uint32_p -> data:uint8_p -> n:uint32_t -> Stack_ unit
val sha256_finish: state:uint32_p -> data:uint8_p -> Stack_ unit

/// Standalone API
val sha256_hash: dst:uint8_p -> src:uint8_p -> len:uint32_t -> Stack_ unit


///  SHA384

/// Incremental API
val sha384_init: state:uint64_p -> Stack_ unit
val sha384_update: state:uint64_p -> data:uint8_p -> Stack_ unit
val sha384_update_multi: state:uint64_p -> data:uint8_p -> n:uint32_t -> Stack_ unit
val sha384_update_last: state:uint64_p -> data:uint8_p -> n:uint32_t -> Stack_ unit
val sha384_finish: state:uint64_p -> data:uint8_p -> Stack_ unit

/// Standalone API
val sha384_hash: dst:uint8_p -> src:uint8_p -> len:uint32_t -> Stack_ unit


///  SHA512

/// Incremental API
val sha512_init: state:uint64_p -> Stack_ unit
val sha512_update: state:uint64_p -> data:uint8_p -> Stack_ unit
val sha512_update_multi: state:uint64_p -> data:uint8_p -> n:uint32_t -> Stack_ unit
val sha512_update_last: state:uint64_p -> data:uint8_p -> n:uint32_t -> Stack_ unit
val sha512_finish: state:uint64_p -> data:uint8_p -> Stack_ unit

/// Standalone API
val sha512_hash: dst:uint8_p -> src:uint8_p -> len:uint32_t -> Stack_ unit


/// Curve

val x25519: dst:uint8_p -> secret:uint8_p -> base:uint8_p -> Stack_ unit
