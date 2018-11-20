module EverCrypt.AEAD
open FStar.HyperStack.ST
open EverCrypt.Helpers
include Spec.AEAD (* TODO: discuss whether this should instead be an open *)
module HS = FStar.HyperStack
module B = LowStar.Buffer
module LM = LowStar.Modifies
module Spec = Spec.AEAD

[@CAbstractStruct]
val aead_state_s (a:aead_alg) : Type0

let aead_state (a:aead_alg) = B.pointer (aead_state_s a)

val repr (#a:aead_alg) (s:aead_state a) (h:HS.mem) : Spec.state a

val footprint (#a:aead_alg) (s:aead_state a) : LM.loc

val inv (#a:aead_alg) (s:aead_state a) (h:HS.mem) : prop

val frame_inv (#a:aead_alg) (s:aead_state a) (l:LM.loc) (h0 h1 : HS.mem)
  : Lemma
    (requires
      inv s h0 /\
      LM.modifies l h0 h1 /\
      LM.loc_disjoint l (footprint s))
    (ensures
      inv s h1)

val aead_create (r:HS.rid) (a:aead_alg {supported_aead_alg a}) (key:uint8_pl (Spec.aead_keyLen a))
  : ST (aead_state a)
    (requires fun h ->
      B.live h key)
    (ensures fun h0 s h1 ->
      LM.modifies LM.loc_none h0 h1 /\
      LM.fresh_loc (footprint s) h0 h1 /\
      LM.loc_includes (LM.loc_region_only true r) (footprint s) /\
      inv s h1 /\
      repr s h1 == Spec.aead_init (B.as_seq h0 key))

let plain_b = uint8_p //TODO: Change to enforce confidentiality

val aead_encrypt (#a:aead_alg) (s:aead_state a)
                 (iv:uint8_pl (Spec.aead_ivLen a))
                 (ad:uint8_p) (adlen:len_of ad)
                 (plain:plain_b) (plainlen:len_of plain)
                 (cipher:uint8_pl (UInt32.v plainlen))
                 (tag:uint8_pl (Spec.aead_tagLen a))
   : ST unit
       (requires fun h ->
         inv s h /\
         all_live h (as_buf_t_l [iv; ad; plain; cipher; tag]) /\
         all_disjoint (footprint s::as_loc_l [iv; ad; plain; cipher; tag]))
       (ensures fun h0 _ h1 ->
         inv s h1 /\
         LM.modifies (loc_union_l (footprint s::as_loc_l [cipher;tag])) h0 h1 /\ (
         let cipher_tag =
           Spec.aead_encrypt
             (repr s h0)
             (B.as_seq h0 iv)
             #(UInt32.v adlen)
             (B.as_seq h0 ad)
             #(UInt32.v plainlen)
             (B.as_seq h0 plain)
         in
         Seq.equal cipher_tag (B.as_seq h1 cipher `Seq.append` B.as_seq h1 tag)))

val aead_decrypt (#a:aead_alg) (s:aead_state a)
                 (iv:uint8_pl (Spec.aead_ivLen a))
                 (ad:uint8_p) (adlen:len_of ad)
                 (plain:plain_b) (plainlen:len_of plain)
                 (cipher:uint8_pl (UInt32.v plainlen))
                 (tag:uint8_pl (Spec.aead_tagLen a))
   : ST uint32_t
       (requires fun h ->
         inv s h /\
         all_live h (as_buf_t_l [iv; ad; plain; cipher; tag]) /\
         all_disjoint (footprint s::as_loc_l [iv; ad; plain; cipher; tag]))
       (ensures fun h0 r h1 ->
         inv s h1 /\
         LM.modifies (loc_union_l (footprint s::as_loc_l [plain])) h0 h1 /\ (
         let cipher_tag = B.as_seq h1 cipher `Seq.append` B.as_seq h1 tag in
         let plain_opt =
           Spec.aead_decrypt
             (repr s h0)
             (B.as_seq h0 iv)
             #(UInt32.v adlen)
             (B.as_seq h0 ad)
             #(UInt32.v plainlen)
             cipher_tag
         in
         match plain_opt with
         | None ->
           r <> 0ul

         | Some p ->
           r = 0ul /\
           Seq.equal p (B.as_seq h1 plain)
       ))

val aead_free (#a:aead_alg) (s:aead_state a)
   : ST unit
        (requires fun h ->
          inv s h)
        (ensures fun h0 _ h1 ->
          LM.modifies (footprint s) h0 h1)
