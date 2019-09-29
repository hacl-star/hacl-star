module Hacl.Impl.Ed25519.PointCompress

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.ByteSequence
open Lib.Buffer

open Hacl.Bignum25519

module F51 = Hacl.Impl.Ed25519.Field51
module F56 = Hacl.Impl.Ed25519.Field56

#set-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0"


inline_for_extraction noextract
val x_mod_2:
  x:felem ->
  Stack uint64
    (requires fun h -> live h x)
    (ensures  fun h0 z h1 -> h0 == h1 /\ v z < 2 /\
      v z == F51.as_nat h0 x % 2
    )
let x_mod_2 x =
  (**) let h0 = get() in
  let x0 = x.(0ul) in
  let z  = x0 &. u64 1 in
  mod_mask_lemma x0 1ul;
  Lib.IntTypes.Compatibility.uintv_extensionality (u64 1) (mod_mask #U64 1ul);
  z

open FStar.Calc

let lemma_fits_in_prime_last_byte (b:lbytes 32) : Lemma
  (requires nat_from_bytes_le b < Spec.Curve25519.prime)
  (ensures v (Seq.index b 31) < pow2 7)
  = calc (==) {
      nat_from_bytes_le b <: nat;
     (==) { nat_from_intseq_le_slice_lemma b 31 }
     nat_from_intseq_le (Seq.slice b 0 31) +
       pow2 (31 * 8) * nat_from_intseq_le (Seq.slice b 31 32);
     (==) { nat_from_intseq_le_lemma0 (Seq.slice b 31 32) }
     nat_from_intseq_le (Seq.slice b 0 31) + pow2 (31*8) * v (Seq.index b 31);
    };
    assert (nat_from_intseq_le (Seq.slice b 0 31) < pow2 (31 * 8));
    calc (<) {
      pow2 (31*8) * v (Seq.index b 31);
      (<) { }
      Spec.Curve25519.prime - nat_from_intseq_le (Seq.slice b 0 31);
      (<=) { }
      Spec.Curve25519.prime;
      (<) { }
      pow2 255;
    };
    FStar.Math.Lemmas.lemma_div_lt_nat (pow2 (31*8) * v (Seq.index b 31)) 255 (31*8);
    calc (==) {
      (pow2 (31 *8) * v (Seq.index b 31))/ (pow2 (31*8));
      (==) { FStar.Math.Lemmas.swap_mul (pow2 (31*8)) (v (Seq.index b 31)) }
      (v (Seq.index b 31) * pow2 (31 *8)) / (pow2 (31*8));
      (==) { FStar.Math.Lemmas.cancel_mul_div (v (Seq.index b 31)) (pow2 (31*8)) }
      v (Seq.index b 31);
    };
    assert_norm (255 - 31 * 8 == 7)

inline_for_extraction noextract
val add_sign:
    out:lbuffer uint8 32ul
  -> x:uint64{v x < 2} ->
  Stack unit
    (requires fun h -> live h out /\ nat_from_bytes_le (as_seq h out) < Spec.Curve25519.prime)
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
      nat_from_bytes_le (as_seq h1 out) == nat_from_bytes_le (as_seq h0 out) + pow2 255 * (v x)
    )
let add_sign out x =
  (**) let h0 = get() in
  let xbyte = to_u8 x in
  let o31 = out.(31ul) in
  (**) FStar.Math.Lemmas.lemma_mult_le_left (pow2 7) (v x) 1;
  (**) assert (pow2 7 * (v x) <= pow2 7);
  (**) assert_norm (pow2 7 < pow2 8);
  (**) assert (v (xbyte <<. 7ul) == pow2 7 * (v x));
  out.(31ul) <- o31 +. (xbyte <<. 7ul);
  (**) let h1 = get() in
  (**) calc (==) {
  (**)   nat_from_intseq_le (as_seq h1 out) <: nat;
  (**)   (==) { nat_from_intseq_le_slice_lemma (as_seq h1 out) 31 }
  (**)   nat_from_intseq_le (Seq.slice (as_seq h1 out) 0 31) +
  (**)     pow2 (31 * 8) * nat_from_intseq_le (Seq.slice (as_seq h1 out) 31 32);
  (**)   (==) {
  (**)     calc (==) {
  (**)       pow2 (31 * 8) * nat_from_intseq_le (Seq.slice (as_seq h1 out) 31 32);
  (**)       (==) { calc (==) {
  (**)                nat_from_intseq_le (Seq.slice (as_seq h1 out) 31 32) <: nat;
  (**)                (==) { nat_from_intseq_le_lemma0 (Seq.slice (as_seq h1 out) 31 32) }
  (**)                v (o31 +. (xbyte <<. 7ul));
  (**)                (==) { calc (==) {
  (**)                         v (o31 +. (xbyte <<. 7ul)) <: nat;
  (**)                         (==) { }
  (**)                         (v o31 + v (xbyte <<. 7ul)) % pow2 8;
  (**)                         (==) { FStar.Math.Lemmas.lemma_mult_le_left (pow2 7) (v x) 1;
  (**)                                assert (pow2 7 * (v x) <= pow2 7);
  (**)                                assert_norm (pow2 7 < pow2 8);
  (**)                                lemma_fits_in_prime_last_byte (as_seq h0 out);
  (**)                                assert_norm (pow2 7 + pow2 7 == pow2 8);
  (**)                                FStar.Math.Lemmas.modulo_lemma (v o31 + pow2 7 * (v x)) (pow2 8)
  (**)                               }
  (**)                         v o31 + pow2 7 * (v x);
  (**)                         }; nat_from_intseq_le_lemma0 (Seq.slice (as_seq h0 out) 31 32)
  (**)                       }
  (**)                nat_from_intseq_le (Seq.slice (as_seq h0 out) 31 32) + pow2 7 * (v x);
  (**)            } }
  (**)       pow2 (31 * 8) * (nat_from_intseq_le (Seq.slice (as_seq h0 out) 31 32) + pow2 7 * (v x));
  (**)       (==) { FStar.Math.Lemmas.distributivity_add_right (pow2 (31 * 8))
  (**)              (nat_from_intseq_le (Seq.slice (as_seq h0 out) 31 32)) (pow2 7 * (v x)) }
  (**)       pow2 (31 * 8) * nat_from_intseq_le (Seq.slice (as_seq h0 out) 31 32) +
  (**)       pow2 (31 * 8) * pow2 7 * (v x);
  (**)       (==) { assert_norm (pow2 (31*8) * pow2 7 == pow2 255) }
  (**)       pow2 (31 * 8) * nat_from_intseq_le (Seq.slice (as_seq h0 out) 31 32) +
  (**)       pow2 255 * (v x);
  (**)     }
  (**)   }
  (**)   nat_from_intseq_le (Seq.slice (as_seq h1 out) 0 31) +
  (**)   pow2 (31 * 8) * nat_from_intseq_le (Seq.slice (as_seq h0 out) 31 32) +
  (**)   pow2 255 * (v x);
  (**)   (==) { nat_from_intseq_le_slice_lemma (as_seq h0 out) 31 }
  (**)   nat_from_bytes_le (as_seq h0 out) + pow2 255 * (v x);
  (**) }

inline_for_extraction noextract
val point_compress_:
    tmp:lbuffer uint64 15ul
  -> p:point ->
  Stack unit
    (requires fun h -> live h tmp /\ live h p /\ disjoint tmp p /\ F51.point_inv_t h p)
    (ensures  fun h0 _ h1 -> modifies (loc tmp) h0 h1 /\ (
      let zinv = Spec.Ed25519.modp_inv (F51.fevalh h0 (gsub p 10ul 5ul)) in
      let x = Spec.Curve25519.fmul (F51.fevalh h0 (gsub p 0ul 5ul)) zinv in
      let y = Spec.Curve25519.fmul (F51.fevalh h0 (gsub p 5ul 5ul)) zinv in
      F51.mul_inv_t h1 (gsub tmp 10ul 5ul) /\
      F51.fevalh h1 (gsub tmp 10ul 5ul) == y /\
      F51.as_nat h1 (gsub tmp 5ul 5ul) == x)
    )
let point_compress_ tmp p =
  let zinv = sub tmp 0ul  5ul in
  let x    = sub tmp 5ul  5ul in
  let out  = sub tmp 10ul 5ul in
  let px   = getx p in
  let py   = gety p in
  let pz   = getz p in

  inverse zinv pz;
  fmul x px zinv;
  reduce x;
  fmul out py zinv;
  reduce_513 out

val point_compress:
  out:lbuffer uint8 32ul
  -> p:point ->
  Stack unit
    (requires fun h -> live h out /\ live h p /\ F51.point_inv_t h p)
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
      as_seq h1 out == Spec.Ed25519.point_compress (F51.point_eval h0 p)
    )

let point_compress z p =
  push_frame();
  let tmp  = create 15ul (u64 0) in
  let zinv = sub tmp 0ul  5ul in
  let x    = sub tmp 5ul  5ul in
  let out  = sub tmp 10ul 5ul in

  point_compress_ tmp p;
  let b = x_mod_2 x in
  store_51 z out;
  add_sign z b;

  (**) let h3 = get() in
  (**) lemma_nat_from_to_bytes_le_preserves_value (as_seq h3 z) 32;
  (**) lemma_nat_to_from_bytes_le_preserves_value (as_seq h3 z) 32 (F51.fevalh h3 out);

  pop_frame()
