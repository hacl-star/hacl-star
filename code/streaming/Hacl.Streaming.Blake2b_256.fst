module Hacl.Streaming.Blake2b_256

module G = FStar.Ghost
module F = Hacl.Streaming.Functor

module Spec = Spec.Blake2
open Hacl.Impl.Blake2.Core
open Hacl.Streaming.Blake2

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

/// No key
inline_for_extraction noextract
let blake2b_256_no_key_alloca =
  F.alloca (blake2b_256 true 0ul) () (s Spec.Blake2B M256)
           (optional_key_blake2b true 0ul)

[@ (Comment "  State allocation function when there is no key")]
let blake2b_256_no_key_create_in =
  F.create_in (blake2b_256 true 0ul) () (s Spec.Blake2B M256)
              (optional_key_blake2b true 0ul)

[@ (Comment "  Update function when there is no key")]
let blake2b_256_no_key_update =
  F.update (blake2b_256 true 0ul) (G.hide ()) (s Spec.Blake2B M256)
           (optional_key_blake2b true 0ul)

[@ (Comment "  Finish function when there is no key")]
let blake2b_256_no_key_finish =
  F.mk_finish (blake2b_256 true 0ul) () (s Spec.Blake2B M256)
              (optional_key_blake2b true 0ul)

[@ (Comment "  Free state function when there is no key")]
let blake2b_256_no_key_free =
  F.free (blake2b_256 true 0ul) (G.hide ()) (s Spec.Blake2B M256)
         (optional_key_blake2b true 0ul)

/// With key
inline_for_extraction noextract
let blake2b_256_with_key_alloca (key_size : key_size_t Spec.Blake2B false) =
  F.alloca (blake2b_256 false key_size) () (s Spec.Blake2B M256)
           (optional_key_blake2b false key_size)

[@ (Comment "  State allocation function when using a (potentially null) key")]
let blake2b_256_with_key_create_in (key_size : key_size_t Spec.Blake2B false) =
  F.create_in (blake2b_256 false key_size) () (s Spec.Blake2B M256)
              (optional_key_blake2b false key_size)

[@ (Comment "  Update function when using a (potentially null) key")]
let blake2b_256_with_key_update (key_size : key_size_t Spec.Blake2B false) =
  F.update (blake2b_256 false key_size) (G.hide ()) (s Spec.Blake2B M256)
           (optional_key_blake2b false key_size)

[@ (Comment "  Finish function when using a (potentially null) key")]
let blake2b_256_with_key_finish (key_size : key_size_t Spec.Blake2B false) =
  F.mk_finish (blake2b_256 false key_size) () (s Spec.Blake2B M256)
              (optional_key_blake2b false key_size)

[@ (Comment "  Free state function when using a (potentially null) key")]
let blake2b_256_with_key_free (key_size : key_size_t Spec.Blake2B false) =
  F.free (blake2b_256 false key_size) (G.hide ()) (s Spec.Blake2B M256)
         (optional_key_blake2b false key_size)
