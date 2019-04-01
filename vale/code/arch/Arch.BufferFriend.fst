module Arch.BufferFriend
friend Lib.IntTypes
friend Lib.RawIntTypes
friend Lib.ByteSequence
friend LowStar.BufferView.Up
friend FStar.Endianness

module PU = X64.Poly1305.Util
module IT = Interop.Types
module PS = Poly_stdcalls
module BS = Lib.ByteSequence
module Raw = Lib.RawIntTypes

unfold let (.[]) = index

let to_bytes s = s
let of_bytes b = b

let lemma_to_bytes_slice b i j = ()
let lemma_of_bytes_slice b i j = ()

let lemma_up_as_seq_index #b h vb i =
  let s0 = DV.as_seq h (UV.as_down_buffer vb) in
  let v = UV.get_view vb in
  let n = UV.View?.n v in
  let start = i * n in
  let s_i = slice s0 start (start + n) in
  UV.as_seq_sel h vb i;
  assert (index (UV.as_seq h vb) i == UV.View?.get v s_i)

let same_seq_downview8 b h =
  let db = DV.mk_buffer_view b (Views.down_view8) in
  DV.length_eq db;
  let s = B.as_seq h b in
  let sdb = DV.as_seq h db in
  let aux (i:nat{i < B.length b}) : Lemma (Seq.index sdb i == Seq.index s i) 
    = DV.as_seq_sel h db i;
      DV.get_sel h db i;
      Opaque_s.reveal_opaque Views.put8_def
  in
  Classical.forall_intro aux;
  assert (Seq.equal s sdb)

let lemma_raw_nat_from_bytes_le_0 (b:BS.bytes) : Lemma
  (requires length b == 0)
  (ensures BS.nat_from_bytes_le b == 0)
  =
  ()

#reset-options "--z3cliopt smt.arith.nl=true"
let lemma_raw_nat_from_bytes_le_n (b:BS.bytes) : Lemma
  (requires length b > 0)
  (ensures BS.nat_from_bytes_le b == Raw.uint_to_nat b.[0] + pow2 8 * (BS.nat_from_bytes_le (slice b 1 (length b))))
  =
  ()

let rec lemma_le_to_n_is_nat_from_bytes (s:FE.bytes) =
  //FE.reveal_le_to_n s;
  if length s > 0 then lemma_le_to_n_is_nat_from_bytes (Seq.tail s)

let rec lemma_n_to_le_is_nat_to_bytes (len:nat) (n:nat) =
  //FE.reveal_n_to_le len n;
  if len > 0 then
  (
    FStar.Math.Lemmas.pow2_plus 8 (8 * (len - 1));
    lemma_n_to_le_is_nat_to_bytes (len - 1) (n / 256);
    ()
  );
  assert (equal (FE.n_to_le len n) (of_bytes (BS.nat_to_bytes_le len n)))
#reset-options

let nat_from_bytes_le_is_four_to_nat b =
  let s = b in
  lemma_raw_nat_from_bytes_le_n s; assert (b.[0] == s.[0]); let s = slice s 1 (length s) in
  lemma_raw_nat_from_bytes_le_n s; assert (b.[1] == s.[0]); let s = slice s 1 (length s) in
  lemma_raw_nat_from_bytes_le_n s; assert (b.[2] == s.[0]); let s = slice s 1 (length s) in
  lemma_raw_nat_from_bytes_le_n s; assert (b.[3] == s.[0]); let s = slice s 1 (length s) in
  lemma_raw_nat_from_bytes_le_0 s;
  assert_norm (
    BS.nat_from_bytes_le b ==
    Words.Four_s.four_to_nat 8 (Words.Four_s.four_map Raw.uint_to_nat (Words.Seq_s.seq_to_four_LE b))
  )

let nat_from_bytes_le_is_le_bytes_to_nat32 b =
  let open Words.Seq_s in
  let open Words.Four_s in
  let open Collections.Seqs_s in
  let sn = seq_uint8_to_seq_nat8 (of_bytes b) in
  let s = seq_nat8_to_seq_nat32_LE sn in
  calc (==) {
    le_bytes_to_nat32 sn;
    == {}
    four_to_nat 8 (Mkfour sn.[0] sn.[1] sn.[2] sn.[3]);
    == {nat_from_bytes_le_is_four_to_nat b}
    BS.nat_from_bytes_le b;
  }

let nat_from_bytes_le_is_le_bytes_to_nat64 b =
  let open Words.Seq_s in
  let open Words.Two_s in
  let open Words.Four_s in
  let open Collections.Seqs_s in
  let sn = seq_uint8_to_seq_nat8 (of_bytes b) in
  let s01 = seq_nat8_to_seq_nat32_LE sn in
  calc (==) {
    index s01 0;
    == {}
    index (seq_map (four_to_nat 8) (seq_to_seq_four_LE sn)) 0;
    == {}
    four_to_nat 8 (Mkfour sn.[0] sn.[1] sn.[2] sn.[3]);
    == {nat_from_bytes_le_is_le_bytes_to_nat32 (slice b 0 4)}
    BS.nat_from_bytes_le (slice b 0 4);
  };
  calc (==) {
    index s01 1;
    == {}
    index (seq_map (four_to_nat 8) (seq_to_seq_four_LE sn)) 1;
    == {}
    four_to_nat 8 (Mkfour sn.[4] sn.[5] sn.[6] sn.[7]);
    == {nat_from_bytes_le_is_le_bytes_to_nat32 (slice b 4 8)}
    BS.nat_from_bytes_le (slice b 4 8);
  };
  calc (==) {
    le_bytes_to_nat64 sn <: int;
    == {Opaque_s.reveal_opaque le_bytes_to_nat64_def}
    two_to_nat 32 (seq_to_two_LE s01) <: int;
    == {assert_norm (two_to_nat 32 (seq_to_two_LE s01) == index s01 0 + pow2 32 * index s01 1)}
    index s01 0 + pow2 32 * index s01 1;
    == {}
    BS.nat_from_bytes_le (slice b 0 4) + pow2 32 * BS.nat_from_bytes_le (slice b 4 8) <: int;
    == {BS.nat_from_bytes_le_slice_lemma #LI.SEC #8 b 4}
    BS.nat_from_bytes_le b <: int;
  }
