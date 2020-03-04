module Vale.Wrapper.X64.Sha
open FStar.Mul

module UV = LowStar.BufferView.Up
module DV = LowStar.BufferView.Down
open Vale.Interop.Base
open Vale.AsLowStar.MemoryHelpers
open Vale.Def.Words.Seq_s
open Vale.SHA.Simplify_Sha
open Vale.Def.Types_s
open Vale.Def.Words_s
open Vale.Def.Words.Four_s
open Vale.Def.Words.Seq
open Vale.Lib.Seqs_s

friend Lib.IntTypes
friend Vale.SHA.SHA_helpers

#set-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

let math_aux (n:nat) : Lemma ( ((64 * n) * 1) / 16 == 4 * n) = ()


val lemma_k_reqs_equiv
  (k_b:ibuf_t TUInt32 TUInt128)
  (h:HS.mem) : Lemma
  (requires IB.live h k_b /\
    IB.length k_b == 64 /\
    Seq.equal (B.as_seq h k_b) (Spec.SHA2.Constants.k224_256))
  (ensures  (
    DV.length_eq (get_downview k_b);
    k_reqs (UV.as_seq h (UV.mk_buffer (get_downview k_b) Vale.Interop.Views.up_view128))))


#push-options "--z3cliopt smt.arith.nl=true"
let lemma_k_reqs_equiv k_b h =
  let db = get_downview k_b in
  DV.length_eq db;
  let ub = UV.mk_buffer db Vale.Interop.Views.up_view128 in
  let k_seq = UV.as_seq h ub in
  assert (Seq.equal (B.as_seq h k_b) k);
  UV.length_eq ub;
  let aux (i:nat{i < size_k_w_256/4}) : Lemma
    ((k_seq.[i]).lo0 == word_to_nat32 (k.[4 * i]) /\
    (k_seq.[i]).lo1 == word_to_nat32 (k.[4 * i + 1]) /\
    (k_seq.[i]).hi2 == word_to_nat32 (k.[4 * i + 2]) /\
    (k_seq.[i]).hi3 == word_to_nat32 (k.[4 * i + 3]))
    =
    let down_s = DV.as_seq h db in
    let s = B.as_seq h k_b in

    UV.as_seq_sel h ub i;
    // Proves
    // assert (k_seq.[i] == UV.sel h ub i);

    UV.get_sel h ub i;
    //Proves
    //assert (k_seq.[i] == Vale.Interop.Views.get128 (Seq.slice down_s (i*16) (i*16+16)));

    Vale.Interop.Views.get128_reveal ();
    // We get the following by revealing the definition of get128
    // let s_slice = seq_uint8_to_seq_nat8 (Seq.slice down_s (i*16) (i*16+16)) in
    // assert (k_seq.[i] == le_bytes_to_quad32 s_slice);

    le_bytes_to_quad32_reveal ();
    reveal_opaque (`%seq_to_seq_four_LE) (seq_to_seq_four_LE #nat8);
    // Revealing le_bytes_to_quad32 gives us the following
    assert (k_seq.[i] == Mkfour
                 (four_to_nat 8 (seq_to_four_LE (seq_uint8_to_seq_nat8
                   (Seq.slice down_s (i*16) (i*16+4)))))
                 (four_to_nat 8 (seq_to_four_LE (seq_uint8_to_seq_nat8
                   (Seq.slice down_s (i*16+4) (i*16+8)))))
                 (four_to_nat 8 (seq_to_four_LE (seq_uint8_to_seq_nat8
                   (Seq.slice down_s (i*16+8) (i*16+12)))))
                 (four_to_nat 8 (seq_to_four_LE (seq_uint8_to_seq_nat8
                   (Seq.slice down_s (i*16+12) (i*16+16))))));

    // Gives us that Seq.slice down_s (i*16) (i*16+4) == Vale.Interop.Views.put32 (Seq.index s (4*i)) and same for other indices
    DV.put_sel h db (4*4*i);
    DV.put_sel h db (4*(4*i+1));
    DV.put_sel h db (4*(4*i+2));
    DV.put_sel h db (4*(4*i+3));

    Vale.Interop.Views.put32_reveal ();

    // Apply the only lemmas without SMTPat to simplify the following patterns:
    // assert (four_to_nat 8 (
    //              seq_to_four_LE (
    //                seq_uint8_to_seq_nat8 (
    //                seq_nat8_to_seq_uint8 (
    //              four_to_seq_LE (
    //         nat_to_four 8 (UInt32.v (Seq.index s (4*i)))))))) ==
    //         UInt32.v (Seq.index s (4*i)));
    seq_to_four_to_seq_LE (nat_to_four 8 (UInt32.v (Seq.index s (4*i))));
    seq_to_four_to_seq_LE (nat_to_four 8 (UInt32.v (Seq.index s (4*i+1))));
    seq_to_four_to_seq_LE (nat_to_four 8 (UInt32.v (Seq.index s (4*i+2))));
    seq_to_four_to_seq_LE (nat_to_four 8 (UInt32.v (Seq.index s (4*i+3))))

  in Classical.forall_intro aux
#pop-options


val simplify_le_bytes_to_hash_uint32
  (b:buf_t TUInt32 TUInt128)
  (h:HS.mem) : Lemma
  (requires B.live h b /\ B.length b == 8)
  (ensures
  (reveal_word();
  DV.length_eq (get_downview b);
  Seq.equal
    (le_bytes_to_hash (le_seq_quad32_to_bytes (UV.as_seq h (UV.mk_buffer (get_downview b) Vale.Interop.Views.up_view128))))
    (B.as_seq h b)))

#push-options "--z3cliopt smt.arith.nl=true"
let simplify_le_bytes_to_hash_uint32 b h =
  let db = get_downview b in
  let down_s = DV.as_seq h db in
  DV.length_eq db;
  let ub = UV.mk_buffer db Vale.Interop.Views.up_view128 in
  UV.length_eq ub;
  let s_init = B.as_seq h b in
  let s = UV.as_seq h ub in
  let s' = le_seq_quad32_to_bytes s in
  let sf = le_bytes_to_hash s' in

  // Since Seq.length s' == 32, we have the following by def of le_bytes_to_hash
  assert (sf == seq_map nat32_to_word (seq_nat8_to_seq_nat32_LE s'));
  le_seq_quad32_to_bytes_reveal ();
  reveal_opaque (`%seq_four_to_seq_LE) (seq_four_to_seq_LE #nat32);
  // After revealing the previous def, the seq_nat8_to_seq_nat32_LE_to_nat8 simplifies
  assert (sf == seq_map nat32_to_word (seq_four_to_seq_LE s));

  let aux (i:nat {i < Seq.length sf}) : Lemma (Seq.index sf i = Seq.index s_init i)
    = let i' = i/4 in
      UV.as_seq_sel h ub i';
      UV.get_sel h ub i';
      reveal_opaque (`%seq_to_seq_four_LE) (seq_to_seq_four_LE #nat8);

      Vale.Interop.Views.get128_reveal ();
      le_bytes_to_quad32_reveal ();
      // Revealing these definitions gives us the following
      assert (Vale.Interop.Views.get128 (Seq.slice (DV.as_seq h db)
             (i' * 16) (i' * 16 + 16))
             == Mkfour
(four_to_nat 8 (seq_to_four_LE (seq_uint8_to_seq_nat8
                               (Seq.slice down_s (i'*16) (i'*16+4)))))
                               (four_to_nat 8 (seq_to_four_LE (seq_uint8_to_seq_nat8
                               (Seq.slice down_s (i'*16+4) (i'*16+8)))))
                               (four_to_nat 8 (seq_to_four_LE (seq_uint8_to_seq_nat8
                               (Seq.slice down_s (i'*16+8) (i'*16+12)))))
                               (four_to_nat 8 (seq_to_four_LE (seq_uint8_to_seq_nat8
                               (Seq.slice down_s (i'*16+12) (i'*16+16))))));

      // Gives us that Seq.slice down_s (i*16) (i*16+4) == Vale.Interop.Views.put32 (Seq.index s (4*i)) and same for other indices
      DV.put_sel h db (4*4*i');
      DV.put_sel h db (4*(4*i'+1));
      DV.put_sel h db (4*(4*i'+2));
      DV.put_sel h db (4*(4*i'+3));

      Vale.Interop.Views.put32_reveal ();

      // Apply the only lemmas without SMTPat to simplify the following patterns:
      // assert (four_to_nat 8 (
      //              seq_to_four_LE (
      //                seq_uint8_to_seq_nat8 (
      //                seq_nat8_to_seq_uint8 (
      //              four_to_seq_LE (
      //         nat_to_four 8 (UInt32.v (Seq.index s (4*i)))))))) ==
      //         UInt32.v (Seq.index s (4*i)));
      seq_to_four_to_seq_LE (nat_to_four 8 (UInt32.v (Seq.index s_init (4*i'))));
      seq_to_four_to_seq_LE (nat_to_four 8 (UInt32.v (Seq.index s_init (4*i'+1))));
      seq_to_four_to_seq_LE (nat_to_four 8 (UInt32.v (Seq.index s_init (4*i'+2))));
      seq_to_four_to_seq_LE (nat_to_four 8 (UInt32.v (Seq.index s_init (4*i'+3))));

      Vale.Interop.Views.get32_128_reveal ();
      assert (UInt32.uint_to_t (four_select (Seq.index s i') (i%4)) ==
        Seq.index (Seq.slice (B.as_seq h b) (i' * 4) (i'*4+4)) (i%4));
      assert (Seq.index (B.as_seq h b) i ==
        Seq.index (Seq.slice (B.as_seq h b) (i' * 4) (i'*4+4)) (i%4))
  in Classical.forall_intro aux;
  assert (Seq.equal sf s_init)
#pop-options

let sha256_update ctx_b in_b num_val k_b =
  let h0 = get() in
  DV.length_eq (get_downview in_b);
  bounded_buffer_addrs_all TUInt8 TUInt128 h0 in_b;
  DV.length_eq (get_downview ctx_b);
  DV.length_eq (get_downview k_b);
  lemma_k_reqs_equiv k_b h0;
  math_aux (UInt64.v num_val);
  as_vale_buffer_len #TUInt8 #TUInt128 in_b;
  let (x, _) = Vale.Stdcalls.X64.Sha.sha256_update ctx_b in_b num_val k_b () in
  let h1 = get() in
  reveal_word();
  simplify_le_bytes_to_hash_uint32 ctx_b h0;
  simplify_le_bytes_to_hash_uint32 ctx_b h1;
  lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 in_b h0;
  ()
