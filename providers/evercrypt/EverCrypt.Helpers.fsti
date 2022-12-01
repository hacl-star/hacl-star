module EverCrypt.Helpers

module B = LowStar.Buffer

open FStar.HyperStack.ST

/// Small helpers
inline_for_extraction noextract
let (!$) = C.String.((!$))

/// For the time being, we do not write any specifications and just try to reach
/// agreement on calling conventions. A series of convenient type abbreviations
/// follows.

effect Stack_ (a: Type) = Stack a (fun _ -> True) (fun _ _ _ -> True)

inline_for_extraction noextract
let uint8_t = UInt8.t
inline_for_extraction noextract
let uint16_t = UInt16.t
inline_for_extraction noextract
let uint32_t = UInt32.t
inline_for_extraction noextract
let uint64_t = UInt64.t

inline_for_extraction noextract
let uint8_p = B.buffer uint8_t
inline_for_extraction noextract
let uint16_p = B.buffer uint16_t
inline_for_extraction noextract
let uint32_p = B.buffer uint32_t
inline_for_extraction noextract
let uint64_p = B.buffer uint64_t

inline_for_extraction noextract
let uint8_pl (l:nat) = p:uint8_p {B.length p = l}
inline_for_extraction noextract
let uint8_l (p:uint8_p) = l:UInt32.t {B.length p = UInt32.v l}
