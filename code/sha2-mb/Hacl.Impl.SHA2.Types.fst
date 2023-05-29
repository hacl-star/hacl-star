module Hacl.Impl.SHA2.Types

inline_for_extraction noextract
let uint8_1p = LowStar.Buffer.buffer FStar.UInt8.t

(* This allows generating pretty names for several types used in SHA2-MB,
   thus improving code quality. This also avoid an unpleasant dependency from
   SHA2-128 to SHA2-256. See #523 for discussion. *)
let uint8_2p = uint8_1p & uint8_1p
let uint8_3p = uint8_1p & uint8_2p
let uint8_4p = uint8_1p & uint8_3p
let uint8_5p = uint8_1p & uint8_4p
let uint8_6p = uint8_1p & uint8_5p
let uint8_7p = uint8_1p & uint8_6p
let uint8_8p = uint8_1p & uint8_7p

let uint8_2x4p = uint8_4p & uint8_4p
let uint8_2x8p = uint8_8p & uint8_8p
