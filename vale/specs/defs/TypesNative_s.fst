module TypesNative_s

unfold let natN = Words_s.natN
unfold let pow2_norm = Words_s.pow2_norm

assume val reveal_iand (n:pos) (x y:natN (pow2_norm n)) : Lemma
  (requires True)
  (ensures Types_s.iand x y == FStar.UInt.logand #n x y)

assume val reveal_ixor (n:pos) (x y:natN (pow2_norm n)) : Lemma
  (requires True)
  (ensures Types_s.ixor x y == FStar.UInt.logxor #n x y)

assume val reveal_ior (n:pos) (x y:natN (pow2_norm n)) : Lemma
  (requires True)
  (ensures Types_s.ior x y == FStar.UInt.logor #n x y)

assume val reveal_inot (n:pos) (x:natN (pow2_norm n)) : Lemma
  (requires True)
  (ensures Types_s.inot x == FStar.UInt.lognot #n x)

assume val reveal_ishl (n:pos) (x:natN (pow2_norm n)) (y:nat) : Lemma
  (requires True)
  (ensures Types_s.ishl x y == FStar.UInt.shift_left #n x y)

assume val reveal_ishr (n:pos) (x:natN (pow2_norm n)) (y:nat) : Lemma
  (requires True)
  (ensures Types_s.ishr x y == FStar.UInt.shift_right #n x y)
