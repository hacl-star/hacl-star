module Hacl.Hash.SHA3

// Just a few combinators needed to instantiate the streaming functor.

open Spec.Hash.Definitions
open Hacl.Hash.Definitions

inline_for_extraction noextract
val init_256: init_st (|SHA3_256, ()|)

inline_for_extraction noextract
val update_256: update_st (|SHA3_256, ()|)

inline_for_extraction noextract
val update_multi_256: update_multi_st (|SHA3_256, ()|)

inline_for_extraction noextract
val update_last_256: update_last_st (|SHA3_256, ()|)

inline_for_extraction noextract
val finish_256: finish_st (|SHA3_256, ()|)
