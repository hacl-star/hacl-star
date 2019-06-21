module Vale.SHA.Simplify_Sha

friend Vale.SHA.SHA_helpers

#set-options "--z3rlimit_factor 4"

open Vale.Def.Words_s
open Vale.Def.Words.Four_s
open Vale.Def.Words.Seq

#set-options "--z3rlimit 100"

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

    Vale.Def.Opaque_s.reveal_opaque Vale.Interop.Views.get128_def;
    // We get the following by revealing the definition of get128
    // let s_slice = seq_uint8_to_seq_nat8 (Seq.slice down_s (i*16) (i*16+16)) in
    // assert (k_seq.[i] == le_bytes_to_quad32 s_slice);

    Vale.Def.Opaque_s.reveal_opaque le_bytes_to_quad32_def;
    FStar.Pervasives.reveal_opaque (`%seq_to_seq_four_LE) (seq_to_seq_four_LE #nat8);
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

    Vale.Def.Opaque_s.reveal_opaque Vale.Interop.Views.put32_def;

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

open Vale.Lib.Seqs_s

let same_seq_downview8 (b:B.buffer UInt8.t) (h:HS.mem) : Lemma
  (DV.as_seq h (DV.mk_buffer_view b (Vale.Interop.Views.down_view8)) == B.as_seq h b) =
  let db = DV.mk_buffer_view b (Vale.Interop.Views.down_view8) in
  DV.length_eq db;
  let s = B.as_seq h b in
  let sdb = DV.as_seq h db in
  let aux (i:nat{i < B.length b}) : Lemma (Seq.index sdb i == Seq.index s i)
    = DV.as_seq_sel h db i;
      DV.get_sel h db i;
      Vale.Def.Opaque_s.reveal_opaque Vale.Interop.Views.put8_def
  in
  Classical.forall_intro aux;
  assert (Seq.equal s sdb)

#reset-options "--z3rlimit 60"
let lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 b h =
  let s_init = B.as_seq h b in
  let db = get_downview b in
  DV.length_eq db;
  let ub = UV.mk_buffer db Vale.Interop.Views.up_view128 in
  let s = UV.as_seq h ub in
  let s' = le_seq_quad32_to_bytes s in
  Vale.Def.Opaque_s.reveal_opaque le_seq_quad32_to_bytes_def;
  //definition given by reveal_opaque
  assert (s' == seq_four_to_seq_LE (seq_map (nat_to_four 8) (seq_four_to_seq_LE s)));
  let s_f = seq_nat8_to_seq_uint8 s' in
  UV.length_eq ub;
  let aux (i:nat{i < Seq.length s_f}) : Lemma (Seq.index s_init i == Seq.index s_f i) =
    FStar.Pervasives.reveal_opaque (`%seq_to_seq_four_LE) (seq_to_seq_four_LE #nat8);
    FStar.Pervasives.reveal_opaque (`%seq_four_to_seq_LE) (seq_four_to_seq_LE #nat8);
    FStar.Pervasives.reveal_opaque (`%seq_four_to_seq_LE) (seq_four_to_seq_LE #nat32);
    let i' = i/16 in
    UV.as_seq_sel h ub i';
    UV.get_sel h ub i';
    same_seq_downview8 b h;
    assert (Seq.index s i' == Vale.Interop.Views.get128 (Seq.slice s_init (i' `op_Multiply` 16) (i' `op_Multiply` 16 + 16)));
    Vale.Def.Opaque_s.reveal_opaque Vale.Interop.Views.get128_def;
    let s_slice = seq_uint8_to_seq_nat8 (Seq.slice s_init (i' `op_Multiply` 16) (i' `op_Multiply` 16 +16)) in
    Vale.Def.Opaque_s.reveal_opaque le_bytes_to_quad32_def;
    assert (seq_to_four_LE (seq_map (four_to_nat 8) (seq_to_seq_four_LE s_slice)) ==
            Seq.index s i')
  in Classical.forall_intro aux;
  assert (Seq.equal s_f s_init)

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
  Vale.Def.Opaque_s.reveal_opaque le_seq_quad32_to_bytes_def;
  FStar.Pervasives.reveal_opaque (`%seq_four_to_seq_LE) (seq_four_to_seq_LE #nat32);
  // After revealing the previous def, the seq_nat8_to_seq_nat32_LE_to_nat8 simplifies
  assert (sf == seq_map nat32_to_word (seq_four_to_seq_LE s));

  let aux (i:nat {i < Seq.length sf}) : Lemma (Seq.index sf i = Seq.index s_init i)
    = let i' = i/4 in
      UV.as_seq_sel h ub i';
      UV.get_sel h ub i';
      FStar.Pervasives.reveal_opaque (`%seq_to_seq_four_LE) (seq_to_seq_four_LE #nat8);

      Vale.Def.Opaque_s.reveal_opaque Vale.Interop.Views.get128_def;
      Vale.Def.Opaque_s.reveal_opaque le_bytes_to_quad32_def;
      // Revealing these definitions gives us the following
      assert (Vale.Interop.Views.get128 (Seq.slice (DV.as_seq h db)
             (i' `op_Multiply` 16) (i' `op_Multiply` 16 + 16))
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

      Vale.Def.Opaque_s.reveal_opaque Vale.Interop.Views.put32_def;

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

      Vale.Def.Opaque_s.reveal_opaque Vale.Interop.Views.get32_128_def;
      assert (UInt32.uint_to_t (four_select (Seq.index s i') (i%4)) ==
        Seq.index (Seq.slice (B.as_seq h b) (i' * 4) (i'*4+4)) (i%4));
      assert (Seq.index (B.as_seq h b) i ==
        Seq.index (Seq.slice (B.as_seq h b) (i' * 4) (i'*4+4)) (i%4))
  in Classical.forall_intro aux;
  assert (Seq.equal sf s_init)
