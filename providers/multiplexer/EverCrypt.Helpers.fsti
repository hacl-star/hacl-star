module EverCrypt.Helpers

open FStar.Buffer
open FStar.HyperStack.ST

/// Small helpers
inline_for_extraction noextract
let (!$) = C.String.((!$))

/// For the time being, we do not write any specifications and just try to reach
/// agreement on calling conventions. A series of convenient type abbreviations
/// follows.

effect Stack_ (a: Type) = Stack a (fun _ -> True) (fun _ _ _ -> True)

let uint8_t = UInt8.t
let uint16_t = UInt16.t
let uint32_t = UInt32.t
let uint64_t = UInt64.t

let uint8_p = buffer uint8_t
let uint16_p = buffer uint16_t
let uint32_p = buffer uint32_t
let uint64_p = buffer uint64_t
