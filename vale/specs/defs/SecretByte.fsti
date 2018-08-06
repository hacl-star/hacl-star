module SecretByte

// Type for secrets.  We don't reveal anything about them concretely
inline_for_extraction
val t:Type0

// But for specification purposes, we can obtain ghost copies
val reveal (x:t) : (Ghost.erased UInt8.t)

// Convenience function to simplify porting code from UInt8
let v (x:t) : GTot (nat) = UInt8.v (Ghost.reveal (reveal x))

inline_for_extraction
val uint_to_t (x:FStar.UInt.uint_t 8) : Pure t
  (requires True)
  (ensures (fun y -> v y = x))

val uv_inv (x : t) : Lemma
  (ensures (uint_to_t (v x) == x))
  [SMTPat (v x)]

val vu_inv (x : FStar.UInt.uint_t 8) : Lemma
  (ensures (v (uint_to_t x) == x))
  [SMTPat (uint_to_t x)]

val v_inj (x1 x2: t): Lemma
  (requires (v x1 == v x2))
  (ensures (x1 == x2))

