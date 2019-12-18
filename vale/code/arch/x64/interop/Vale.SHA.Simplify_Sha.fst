module Vale.SHA.Simplify_Sha
open FStar.Mul

friend Vale.SHA.SHA_helpers

#set-options "--z3rlimit_factor 4"

open Vale.Def.Words_s
open Vale.Def.Words.Four_s
open Vale.Def.Words.Seq

#set-options "--z3rlimit 100"

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
      Vale.Interop.Views.put8_reveal ()
  in
  Classical.forall_intro aux;
  assert (Seq.equal s sdb)

#reset-options "--z3rlimit 60"
let lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 b h =
  let s_init = B.as_seq h b in
  let db = get_downview b in
  DV.length_eq db;
  assert (Seq.length s_init == B.length b);
  let ub = UV.mk_buffer db Vale.Interop.Views.up_view128 in
  let s = UV.as_seq h ub in
  let s' = le_seq_quad32_to_bytes s in
  le_seq_quad32_to_bytes_reveal ();
  //definition given by reveal_opaque
  assert (s' == seq_four_to_seq_LE (seq_map (nat_to_four 8) (seq_four_to_seq_LE s)));
  let s_f = seq_nat8_to_seq_uint8 s' in
  UV.length_eq ub;
  let aux (i:nat{i < Seq.length s_f}) : Lemma (Seq.index s_init i == Seq.index s_f i) =
    reveal_opaque (`%seq_to_seq_four_LE) (seq_to_seq_four_LE #nat8);
    reveal_opaque (`%seq_four_to_seq_LE) (seq_four_to_seq_LE #nat8);
    reveal_opaque (`%seq_four_to_seq_LE) (seq_four_to_seq_LE #nat32);
    let i' = i/16 in
    UV.as_seq_sel h ub i';
    UV.get_sel h ub i';
    same_seq_downview8 b h;
    assert (Seq.index s i' == Vale.Interop.Views.get128 (Seq.slice s_init (i' * 16) (i' * 16 + 16)));
    Vale.Interop.Views.get128_reveal ();
    let s_slice = seq_uint8_to_seq_nat8 (Seq.slice s_init (i' * 16) (i' * 16 +16)) in
    le_bytes_to_quad32_reveal ();
    assert (seq_to_four_LE (seq_map (four_to_nat 8) (seq_to_seq_four_LE s_slice)) ==
            Seq.index s i')
  in Classical.forall_intro aux;
  assert (Seq.equal s_f s_init)
