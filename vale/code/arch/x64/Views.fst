module Views

let inverses8 (u:unit) =
  reveal_opaque get8_def;
  reveal_opaque put8_def;
  let aux (x:Seq.lseq U8.t 1) : Lemma (put8 (get8 x) == x) =
    assert (Seq.equal x (put8 (get8 x)))
  in Classical.forall_intro aux

let inverses16 (u:unit) =
  reveal_opaque get16_def;
  reveal_opaque put16_def;
  let aux (x:Seq.lseq U8.t 2) : Lemma (put16 (get16 x) == x) =
    assert (Seq.equal x (put16 (get16 x)))
  in Classical.forall_intro aux

#set-options "--z3rlimit 40"

let inverses32 (u:unit) =
  reveal_opaque get32_def;
  reveal_opaque put32_def;
  let aux (x:Seq.lseq U8.t 4) : Lemma (put32 (get32 x) == x) =
    assert (Seq.equal x (put32 (get32 x)))
  in Classical.forall_intro aux

private
abstract
let get64_def_alt (s:Seq.lseq U8.t 8) : GTot UInt64.t =
  let open FStar.Mul in
  let s0 = Seq.slice s 0 4 in
  let u0 = get32_def s0 in
  let s1 = Seq.slice s 4 8 in
  let u1 = get32_def s1 in
  UInt64.uint_to_t (UInt32.v u0 +
                    UInt32.v u1 * 0x100000000)

let get64_def_alt_equiv (s:Seq.lseq U8.t 8)
  : Lemma (get64_def s == get64_def_alt s)
  = ()

let inverses64_def_aux (x:UInt64.t)
  : Lemma (get64_def (put64_def x) == x)
  = ()

#reset-options "--z3rlimit 30"
let inverses64_def_aux' (x:Seq.lseq U8.t 8)
  : Lemma (put64_def (get64_def x) `Seq.equal` x)
  = reveal_opaque get32_def;
    reveal_opaque put32_def;
    inverses32();
    get64_def_alt_equiv x;
    get64_def_alt_equiv (put64_def (get64_def x));
    inverses64_def_aux (get64_def x)

#reset-options "--z3rlimit 20"
let inverses64 (u:unit) =
  reveal_opaque get64_def;
  reveal_opaque put64_def;
  Classical.forall_intro inverses64_def_aux;
  Classical.forall_intro inverses64_def_aux'

let inverses128 (u:unit) =
  reveal_opaque get128_def;
  reveal_opaque put128_def;
  Classical.forall_intro  Arch.Types.le_quad32_to_bytes_to_quad32;
  Classical.forall_intro  Arch.Types.le_bytes_to_quad32_to_bytes

let get32_128_aux1 (x: Seq.lseq U32.t 4): Lemma (put32_128 (get32_128 x) == x) =
  reveal_opaque put32_128_def;
  reveal_opaque get32_128_def;
  let vg = get32_128 x in
  let vp = put32_128 vg in
  assert (Seq.equal x vp)

let put32_128_aux1 (x: quad32): Lemma (get32_128 (put32_128 x) == x) =
  reveal_opaque put32_128_def;
  reveal_opaque get32_128_def;
  ()
  
let inverses32_128 (u:unit) =
  reveal_opaque get32_128_def;
  reveal_opaque put32_128_def;
  Classical.forall_intro get32_128_aux1;
  Classical.forall_intro put32_128_aux1
