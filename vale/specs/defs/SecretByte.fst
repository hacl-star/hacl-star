module SecretByte

module U8 = FStar.UInt8

inline_for_extraction
let t = U8.t

let reveal (x:t) : (Ghost.erased UInt8.t) =
  Ghost.hide x

inline_for_extraction
let uint_to_t (x:FStar.UInt.uint_t 8)
  =
  UInt8.uint_to_t x

let uv_inv (x : t) : Lemma
  (ensures (uint_to_t (v x) == x))
  [SMTPat (v x)] = ()

let vu_inv (x : FStar.UInt.uint_t 8) : Lemma
  (ensures (v (uint_to_t x) == x))
  [SMTPat (uint_to_t x)] = ()

let v_inj (x1 x2: t): Lemma
  (requires (v x1 == v x2))
  (ensures (x1 == x2))
  = ()
