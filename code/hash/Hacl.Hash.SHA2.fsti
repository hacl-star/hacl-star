module Hacl.Hash.SHA2

open Hacl.Hash.Definitions
open Spec.Hash.Definitions

inline_for_extraction noextract
val init_224: init_st (|SHA2_224, ()|)
inline_for_extraction noextract
val init_256: init_st (|SHA2_256, ()|)
inline_for_extraction noextract
val init_384: init_st (|SHA2_384, ()|)
inline_for_extraction noextract
val init_512: init_st (|SHA2_512, ()|)

inline_for_extraction noextract
val alloca_224: alloca_st (|SHA2_224, ()|)
inline_for_extraction noextract
val alloca_256: alloca_st (|SHA2_256, ()|)
inline_for_extraction noextract
val alloca_384: alloca_st (|SHA2_384, ()|)
inline_for_extraction noextract
val alloca_512: alloca_st (|SHA2_512, ()|)

inline_for_extraction noextract
val update_multi_224: update_multi_st (|SHA2_224, ()|)
inline_for_extraction noextract
val update_multi_256: update_multi_st (|SHA2_256, ()|)
inline_for_extraction noextract
val update_multi_384: update_multi_st (|SHA2_384, ()|)
inline_for_extraction noextract
val update_multi_512: update_multi_st (|SHA2_512, ()|)

inline_for_extraction noextract
val update_last_224: update_last_st (|SHA2_224, ()|)
inline_for_extraction noextract
val update_last_256: update_last_st (|SHA2_256, ()|)
inline_for_extraction noextract
val update_last_384: update_last_st (|SHA2_384, ()|)
inline_for_extraction noextract
val update_last_512: update_last_st (|SHA2_512, ()|)

inline_for_extraction noextract
val finish_224: finish_st (|SHA2_224, ()|)
inline_for_extraction noextract
val finish_256: finish_st (|SHA2_256, ()|)
inline_for_extraction noextract
val finish_384: finish_st (|SHA2_384, ()|)
inline_for_extraction noextract
val finish_512: finish_st (|SHA2_512, ()|)
