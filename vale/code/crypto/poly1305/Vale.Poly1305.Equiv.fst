module Vale.Poly1305.Equiv
open FStar.Mul

module BSeq = Lib.ByteSequence

// REVIEW: S and V use different smtencoding flags,
// so some equalities between S and V definitions aren't as obvious to Z3 as we might want.

unfold let pow2_128 = Vale.Def.Words_s.pow2_128
unfold let nat64 = Vale.Def.Words_s.nat64
unfold let iand #n = Vale.Def.Types_s.iand #n
unfold let size_nat = Lib.IntTypes.size_nat
unfold let uint_v #t #l = Lib.IntTypes.uint_v #t #l
unfold let uint8 = Lib.IntTypes.uint8
unfold let u64 = Lib.IntTypes.u64
unfold let logand #t #l = Lib.IntTypes.logand #t #l
unfold let repeati = Lib.LoopCombinators.repeati
unfold let repeat_blocks = Lib.Sequence.repeat_blocks
unfold let repeat_blocks_f = Lib.Sequence.repeat_blocks_f
unfold let sub #a #len = Lib.Sequence.sub #a #len
unfold let lbytes = Lib.ByteSequence.lbytes
unfold let uint_from_bytes_le #t #l = Lib.ByteSequence.uint_from_bytes_le #t #l
unfold let prime = S.prime
unfold let felem = S.felem
unfold let fadd = S.fadd
unfold let fmul = S.fmul
unfold let to_felem = S.to_felem
unfold let modp = V.modp
unfold let mod2_128 = V.mod2_128

#set-options "--z3rlimit 150 --max_fuel 1 --max_ifuel 1"

let rec lemma_poly1305_equiv_rec (text:bytes) (acc0:felem) (r:felem) (k:nat) : Lemma
  (requires k <= length text / size_block)
  (ensures (
    let f = S.poly1305_update1 r size_block in
    let repeat_f = repeat_blocks_f size_block text f (length text / size_block) in
    let pad = pow2 (8 * size_block) in
    V.poly1305_hash_blocks acc0 pad r (block_fun text) k == repeati k repeat_f acc0
  ))
  (decreases k)
  =
  let inp = block_fun text in
  let f = S.poly1305_update1 r size_block in
  let len = length text in
  let nb = len / size_block in
  let repeat_f = repeat_blocks_f size_block text f nb in
  let pad = pow2 (8 * size_block) in
  assert_norm (pow2 128 + pow2 128 < prime);
  if k = 0 then
    Lib.LoopCombinators.eq_repeati0 nb repeat_f acc0
  else
  (
    let kk = k - 1 in
    let hh = V.poly1305_hash_blocks acc0 pad r inp kk in
    let r0:felem = repeati kk repeat_f acc0 in
    let block = Seq.slice text (kk * size_block) (kk * size_block + size_block) in
    calc (==) {
      V.poly1305_hash_blocks acc0 pad r inp k;
      == {}
      modp ((hh + pad + inp kk) * r);
      == {assert_norm (modp ((hh + pad + inp kk) * r) == (hh + pad + inp kk) * r % prime)}
      (hh + pad + inp kk) * r % prime;
      == {FStar.Math.Lemmas.lemma_mod_mul_distr_l (hh + pad + inp kk) r prime}
      ((hh + pad + inp kk) % prime) * r % prime;
      == {lemma_poly1305_equiv_rec text acc0 r kk}
      ((pad + inp kk + r0) % prime) * r % prime;
      == {assert_norm (fmul (fadd (pad + inp kk) r0) r == ((pad + inp kk + r0) % prime) * r % prime)}
      fmul (fadd (pad + inp kk) r0) r;
      == { FStar.Math.Lemmas.lemma_mod_plus_distr_l (pad + inp kk) r0 prime }
      fmul (fadd (fadd pad (inp kk)) r0) r;
      == {}
      S.poly1305_update1 r size_block block (repeati kk repeat_f acc0);
    };
    calc (==) {
      S.poly1305_update1 r size_block block (repeati kk repeat_f acc0);
      == {}
      f block (repeati kk repeat_f acc0);
      == {}
      repeat_f kk (repeati kk repeat_f acc0);
      == {Lib.LoopCombinators.unfold_repeati nb repeat_f acc0 kk}
      repeati k repeat_f acc0;
    }
  )

let lemma_poly1305_equiv_last (text:bytes) (r:felem) (hBlocks:felem) : Lemma
  (ensures (
    let inp = block_fun text in
    let len = length text in
    let nb = len / size_block in
    let last = Seq.slice text (nb * size_block) len in
    let nExtra = len % size_block in
    let padLast = pow2 (nExtra * 8) in
    modp ((hBlocks + padLast + inp nb % padLast) * r) == S.poly1305_update1 r nExtra last hBlocks
  ))
  =
  let inp = block_fun text in
  let len = length text in
  let nb = len / size_block in
  let last = Seq.slice text (nb * size_block) len in
  let nExtra = len % size_block in
  let padLast = pow2 (nExtra * 8) in
  let x = nat_from_bytes_le last in
  Math.Lemmas.pow2_le_compat 128 (8 * nExtra);
  FStar.Math.Lemmas.modulo_lemma x padLast;
  assert_norm (x + padLast < prime);
  calc (==) {
    modp ((hBlocks + padLast + inp nb % padLast) * r);
    == {}
    modp ((x + padLast + hBlocks) * r);
    == {assert_norm (modp ((x + padLast + hBlocks) * r) == (x + padLast + hBlocks) * r % prime)}
    (x + padLast + hBlocks) * r % prime;
    == {FStar.Math.Lemmas.lemma_mod_mul_distr_l (x + padLast + hBlocks) r prime}
    ((x + padLast + hBlocks) % prime) * r % prime;
    == {assert_norm (((x + padLast + hBlocks) % prime) * r % prime == fmul (fadd (x + padLast) hBlocks) r)}
    fmul (fadd (x + padLast) hBlocks) r;
    == { FStar.Math.Lemmas.lemma_mod_plus_distr_l (x + padLast) hBlocks prime }
    fmul (fadd (fadd x padLast) hBlocks) r;
    == {}
    S.poly1305_update1 r nExtra last hBlocks;
  }

let lemma_poly1305_equiv_r (k:key) : Lemma
  (ensures (
    let key_bytes = slice k 0 16 in
    let key_r:nat128 = nat_from_bytes_le key_bytes in
    iand key_r 0x0ffffffc0ffffffc0ffffffc0fffffff == S.poly1305_encode_r key_bytes
  ))
  =
  let key_bytes:S.block = slice k 0 16 in
  let key_r:nat128 = nat_from_bytes_le key_bytes in
  let mask = 0x0ffffffc0ffffffc0ffffffc0fffffff in
  let rv = iand key_r mask in

  let lo = uint_from_bytes_le (sub key_bytes 0 8) in
  let hi = uint_from_bytes_le (sub key_bytes 8 8) in
  let mask0 = u64 0x0ffffffc0fffffff in
  let mask1 = u64 0x0ffffffc0ffffffc in
  let mlo = logand lo mask0 in
  let mhi = logand hi mask1 in
  assert_norm (pow2 128 < prime);
  let rs:felem = to_felem (uint_v mhi * pow2 64 + uint_v mlo) in
  assert_norm (rs == S.poly1305_encode_r key_bytes);

  let v_mask0:nat64 = 0x0ffffffc0fffffff in
  let v_mask1:nat64 = 0x0ffffffc0ffffffc in
  let v_lo:nat64 = uint_v lo in
  let v_hi:nat64 = uint_v hi in
  let lowerUpper128 = Vale.Poly1305.Math.lowerUpper128 in
  let v_lo_hi:nat128 = lowerUpper128 v_lo v_hi in
  let v_mask_0_1:nat128 = lowerUpper128 v_mask0 v_mask1 in
  let z0 = iand v_lo v_mask0 in
  let z1 = iand v_hi v_mask1 in
  let z = lowerUpper128 z0 z1 in
  let and64 = UInt.logand #64 in
  calc (==) {
    rv;
    == {}
    iand key_r mask;
    == {Hacl.Impl.Poly1305.Lemmas.uint_from_bytes_le_lemma key_bytes}
    iand (pow2 64 * v_hi + v_lo) mask;
    == {Vale.Poly1305.Math.lowerUpper128_reveal ()}
    iand v_lo_hi v_mask_0_1;
    == {Vale.Poly1305.Math.lemma_lowerUpper128_and v_lo_hi v_lo v_hi v_mask_0_1 v_mask0 v_mask1 z z0 z1}
    z;
    == {Vale.Poly1305.Math.lowerUpper128_reveal ()}
    z1 * pow2 64 + z0;
    == {Vale.Arch.TypesNative.reveal_iand_all 64}
    and64 v_hi v_mask1 * pow2 64 + and64 v_lo v_mask0;
    == {Lib.IntTypes.logand_spec hi mask1; Lib.IntTypes.logand_spec lo mask0}
    uint_v mhi * pow2 64 + uint_v mlo;
    == {}
    rs;
  }

let lemma_poly1305_equiv text k =
  let key_bytes = slice k 0 16 in
  let key_r:nat128 = nat_from_bytes_le key_bytes in
  let key_s:nat128 = nat_from_bytes_le (slice k 16 32) in
  let r = S.poly1305_encode_r key_bytes in
  lemma_poly1305_equiv_r k;
  let acc0 = 0 in
  let inp = block_fun text in
  let pad = pow2 (8 * size_block) in
  assert_norm (pad == pow2_128);
  let f = S.poly1305_update1 r size_block in
  let len = length text in
  let nb = len / size_block in
  let acc1 = repeati nb (repeat_blocks_f size_block text f nb) acc0 in
  let last = Seq.slice text (nb * size_block) len in
  let nExtra = len % size_block in
  let l = S.poly1305_update_last r in
  let repeat_f = repeat_blocks_f size_block text f nb in
  let hBlocks = V.poly1305_hash_blocks acc0 pad r inp nb in
  if nExtra = 0 then
  (
    lemma_poly1305_equiv_rec text acc0 r nb;
    Lib.Sequence.lemma_repeat_blocks size_block text f l acc0;
    calc (==) {
      V.poly1305_hash key_r key_s inp len;
      == {}
      mod2_128 (hBlocks + key_s);
      == {assert_norm (mod2_128 (hBlocks + key_s) == (hBlocks + key_s) % pow2 128)}
      (hBlocks + key_s) % pow2 128;
    };
    calc (==) {
      hBlocks <: int;
      == {lemma_poly1305_equiv_rec text acc0 r nb}
      repeati nb repeat_f acc0 <: felem;
    };
    calc (==) {
      repeati nb repeat_f acc0;
      == {}
      l nExtra last acc1;
      == {Lib.Sequence.lemma_repeat_blocks size_block text f l acc0}
      repeat_blocks #uint8 #felem size_block text f l acc0;
      == {}
      S.poly1305_update text acc0 r;
    };
    calc (==) {
      nat_to_bytes_le 16 (V.poly1305_hash key_r key_s inp len);
      == {}
      nat_to_bytes_le 16 ((S.poly1305_update text acc0 r + key_s) % pow2 128);
      == {}
      S.poly1305_mac text k;
    };
    ()
  )
  else
  (
    lemma_poly1305_equiv_rec text acc0 r nb;
    Lib.Sequence.lemma_repeat_blocks size_block text f l acc0;
    let padLast = pow2 (nExtra * 8) in
    let hLast = modp ((hBlocks + padLast + inp nb % padLast) * r) in
    calc (==) {
      V.poly1305_hash key_r key_s inp len;
      == {}
      mod2_128 (hLast + key_s);
      == {assert_norm (mod2_128 (hLast + key_s) == (hLast + key_s) % pow2 128)}
      (hLast + key_s) % pow2 128;
    };
    calc (==) {
      hBlocks <: int;
      == {lemma_poly1305_equiv_rec text acc0 r nb}
      repeati nb repeat_f acc0 <: felem;
    };
    calc (==) {
      S.poly1305_update1 r nExtra last (repeati nb repeat_f acc0);
      == {}
      l nExtra last acc1;
      == {Lib.Sequence.lemma_repeat_blocks size_block text f l acc0}
      repeat_blocks #uint8 #felem size_block text f l acc0;
      == {}
      S.poly1305_update text acc0 r;
    };
    lemma_poly1305_equiv_last text r hBlocks;
    calc (==) {
      nat_to_bytes_le 16 (V.poly1305_hash key_r key_s inp len);
      == {}
      nat_to_bytes_le 16 ((S.poly1305_update text acc0 r + key_s) % pow2 128);
      == {}
      S.poly1305_mac text k;
    };
    ()
  )
