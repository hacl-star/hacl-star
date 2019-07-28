module Vale.Wrapper.X64.GCM_IV

open Vale.X64.CPU_Features_s
open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
module DV = LowStar.BufferView.Down
module UV = LowStar.BufferView.Up
open FStar.Mul
open Vale.Def.Words_s
open Vale.Def.Words.Seq_s
open Vale.AES.AES_s
open Vale.AES.GCM_s
open Vale.Interop.Base
open Vale.Def.Types_s
open Vale.AES.OptPublic

unfold
let uint8_p = B.buffer UInt8.t
let uint64 = UInt64.t

inline_for_extraction
val compute_iv
  (a:algorithm)
  (key:Ghost.erased (Seq.seq nat32))
  (iv_b:uint8_p)
  (num_bytes:UInt32.t)
  (j0_b:uint8_p)
  (extra_b:uint8_p)
  (hkeys_b:uint8_p) : Stack unit
  (requires fun h ->
    B.live h iv_b /\ B.live h extra_b /\ B.live h hkeys_b /\ B.live h j0_b /\

    B.length j0_b == 16 /\ B.length extra_b == 16 /\
    B.length hkeys_b == 128 /\ B.length iv_b == UInt32.v num_bytes /\
    UInt32.v num_bytes > 0 /\

    B.disjoint iv_b j0_b /\ B.disjoint iv_b extra_b /\ B.disjoint iv_b hkeys_b /\
    (B.disjoint j0_b extra_b \/ j0_b == extra_b) /\
    B.disjoint j0_b hkeys_b /\ B.disjoint hkeys_b extra_b /\

    pclmulqdq_enabled /\ avx_enabled /\

    is_aes_key_LE a (Ghost.reveal key) /\
    hkeys_reqs_pub (le_bytes_to_seq_quad32 (seq_uint8_to_seq_nat8 (B.as_seq h hkeys_b)))
      (reverse_bytes_quad32 (aes_encrypt_LE a (Ghost.reveal key) (Mkfour 0 0 0 0)))
  )
  (ensures fun h0 _ h1 ->
    B.modifies (B.loc_buffer j0_b `B.loc_union` B.loc_buffer extra_b) h0 h1 /\
    le_bytes_to_quad32 (seq_uint8_to_seq_nat8 (B.as_seq h1 j0_b)) ==
      compute_iv_BE (aes_encrypt_LE a (Ghost.reveal key) (Mkfour 0 0 0 0))
                    (seq_uint8_to_seq_nat8 (B.as_seq h0 iv_b)))
