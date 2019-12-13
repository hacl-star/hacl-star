module Vale.Interop.Views
open FStar.Mul

let inverses8 (u:unit) =
  FStar.Pervasives.reveal_opaque (`%get8) get8;
  FStar.Pervasives.reveal_opaque (`%put8) put8;
  let aux (x:Seq.lseq U8.t 1) : Lemma (put8 (get8 x) == x) =
    assert (Seq.equal x (put8 (get8 x)))
  in Classical.forall_intro aux

let inverses16 (u:unit) =
  FStar.Pervasives.reveal_opaque (`%get16) get16;
  FStar.Pervasives.reveal_opaque (`%put16) put16;
  let aux (x:Seq.lseq U8.t 2) : Lemma (put16 (get16 x) == x) =
    assert (Seq.equal x (put16 (get16 x)))
  in Classical.forall_intro aux

#set-options "--z3rlimit 40"

let inverses32 (u:unit) =
  FStar.Pervasives.reveal_opaque (`%get32) get32;
  FStar.Pervasives.reveal_opaque (`%put32) put32;
  Classical.forall_intro (four_to_seq_to_four_LE #nat8);
  Classical.forall_intro (seq_to_four_to_seq_LE #nat8)

#reset-options "--z3rlimit 20"
let inverses64 (u:unit) =
  FStar.Pervasives.reveal_opaque (`%get64) get64;
  FStar.Pervasives.reveal_opaque (`%put64) put64;
  Classical.forall_intro Vale.Arch.Types.le_nat64_to_bytes_to_nat64;
  Classical.forall_intro Vale.Arch.Types.le_bytes_to_nat64_to_bytes

let inverses128 (u:unit) =
  FStar.Pervasives.reveal_opaque (`%get128) get128;
  FStar.Pervasives.reveal_opaque (`%put128) put128;
  Classical.forall_intro Vale.Arch.Types.le_quad32_to_bytes_to_quad32;
  Classical.forall_intro Vale.Arch.Types.le_bytes_to_quad32_to_bytes

let get32_128_aux1 (x: Seq.lseq U32.t 4): Lemma (put32_128 (get32_128 x) == x) =
  FStar.Pervasives.reveal_opaque (`%put32_128) put32_128;
  FStar.Pervasives.reveal_opaque (`%get32_128) get32_128;
  let vg = get32_128 x in
  let vp = put32_128 vg in
  assert (Seq.equal x vp)

let put32_128_aux1 (x: quad32): Lemma (get32_128 (put32_128 x) == x) =
  FStar.Pervasives.reveal_opaque (`%put32_128) put32_128;
  FStar.Pervasives.reveal_opaque (`%get32_128) get32_128;
  ()

let inverses32_128 (u:unit) =
  FStar.Pervasives.reveal_opaque (`%get32_128) get32_128;
  FStar.Pervasives.reveal_opaque (`%put32_128) put32_128;
  Classical.forall_intro get32_128_aux1;
  Classical.forall_intro put32_128_aux1
