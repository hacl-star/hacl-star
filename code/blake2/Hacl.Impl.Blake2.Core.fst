module Hacl.Impl.Blake2.Core
module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.IntVector

module Spec = Spec.Blake2

#set-options "--max_fuel 0 --max_ifuel 1"

noextract inline_for_extraction
let zero_element (a:Spec.alg) (m:m_spec) : element_t a m =
  match a,m with
  | Spec.Blake2S,M128 -> (vec_zero U32 4)
  | Spec.Blake2S,M256 -> (vec_zero U32 4)
  | Spec.Blake2B,M256 -> (vec_zero U64 4)
  | _ -> Spec.zero a

noextract inline_for_extraction
let row_v #a #m h r =
  match a,m with
  | Spec.Blake2S,M128 -> vec_v (Lib.Sequence.index (as_seq h r) 0)
  | Spec.Blake2S,M256 -> vec_v (Lib.Sequence.index (as_seq h r) 0)
  | Spec.Blake2B,M256 -> vec_v (Lib.Sequence.index (as_seq h r) 0)
  | _ -> as_seq h r

let row_v_lemma #a #m h0 h1 r1 r2 = ()


#push-options "--z3rlimit 50"
let g_rowi_disjoint #a #m st idx1 idx2 =
  if idx1 <. idx2 then (
    assert (v (idx1 *. row_len a m) + v (row_len a m) <= v (idx2 *. row_len a m));
    assert (g_rowi st idx1 ==
	    gsub st (idx1 *. row_len a m) (row_len a m));
    assert (g_rowi st idx2 ==
	    gsub st (idx2 *. row_len a m) (row_len a m));
   LowStar.Monotonic.Buffer.loc_disjoint_gsub_buffer #_ #((LowStar.Buffer.trivial_preorder (element_t a m))) #((LowStar.Buffer.trivial_preorder (element_t a m))) st (idx1 *. row_len a m) (row_len a m) (LowStar.Buffer.trivial_preorder (element_t a m)) (idx2 *. row_len a m) (row_len a m) (LowStar.Buffer.trivial_preorder (element_t a m))
    )
  else if idx2 <. idx1 then (
    assert (v (idx2 *. row_len a m) + v (row_len a m) <= v (idx1 *. row_len a m));
    assert (g_rowi st idx2 ==
	    gsub st (idx2 *. row_len a m) (row_len a m));
    LowStar.Monotonic.Buffer.loc_disjoint_gsub_buffer #_ #((LowStar.Buffer.trivial_preorder (element_t a m))) #((LowStar.Buffer.trivial_preorder (element_t a m))) st (idx1 *. row_len a m) (row_len a m) (LowStar.Buffer.trivial_preorder (element_t a m)) (idx2 *. row_len a m) (row_len a m) (LowStar.Buffer.trivial_preorder (element_t a m)))
  else ()

let g_rowi_unchanged #a #m h0 h1 st i =
  assert (v (i *. row_len a m) + v (row_len a m) <= length st);
  LowStar.Monotonic.Buffer.as_seq_gsub #_ #(LowStar.Buffer.trivial_preorder (element_t a m)) #(LowStar.Buffer.trivial_preorder (element_t a m)) h0 st (i *. row_len a m) (row_len a m)
  (LowStar.Buffer.trivial_preorder (element_t a m));
  LowStar.Monotonic.Buffer.as_seq_gsub #_ #(LowStar.Buffer.trivial_preorder (element_t a m)) #(LowStar.Buffer.trivial_preorder (element_t a m)) h1 st (i *. row_len a m) (row_len a m)
  (LowStar.Buffer.trivial_preorder (element_t a m))

let g_rowi_disjoint_other #a #m #b st i x =
  assert (v (i *. row_len a m) + v (row_len a m) <= length st);
    LowStar.Monotonic.Buffer.loc_includes_gsub_buffer_r'  #_ #(LowStar.Buffer.trivial_preorder (element_t a m)) #(LowStar.Buffer.trivial_preorder (element_t a m)) st (i *. row_len a m) (row_len a m)
  (LowStar.Buffer.trivial_preorder (element_t a m))
#pop-options

inline_for_extraction noextract
let state_v (#a:Spec.alg) (#m:m_spec) (h:mem) (st:state_p a m) : GTot (Spec.state a) =
  let r0 = row_v h (g_rowi st 0ul) in
  let r1 = row_v h (g_rowi st 1ul) in
  let r2 = row_v h (g_rowi st 2ul) in
  let r3 = row_v h (g_rowi st 3ul) in
  Lib.Sequence.create4 r0 r1 r2 r3

#push-options "--z3rlimit 100"
let state_v_eq_lemma #a #m h0 h1 st1 st2 =
  assert (v (0ul *. row_len a m) == 0);
  LowStar.Monotonic.Buffer.as_seq_gsub #_ #(LowStar.Buffer.trivial_preorder (element_t a m)) #(LowStar.Buffer.trivial_preorder (element_t a m)) h0 st1 0ul (row_len a m)
  (LowStar.Buffer.trivial_preorder (element_t a m));
  assert (as_seq h0 (g_rowi st1 0ul) == Seq.slice (as_seq h0 st1) 0 (v (row_len a m)));
  assert (as_seq h0 (g_rowi st1 1ul) == Seq.slice (as_seq h0 st1) (v (1ul *. row_len a m)) (v (2ul *. row_len a m)));
  assert (as_seq h0 (g_rowi st1 2ul) == Seq.slice (as_seq h0 st1) (v (2ul *. row_len a m)) (v (3ul *. row_len a m)));
  assert (as_seq h0 (g_rowi st1 3ul) == Seq.slice (as_seq h0 st1) (v (3ul *. row_len a m)) (v (4ul *. row_len a m)));
  Lib.Sequence.eq_intro (as_seq h0 (g_rowi st1 0ul)) (as_seq h1 (g_rowi st2 0ul));
  Lib.Sequence.eq_intro (as_seq h0 (g_rowi st1 1ul)) (as_seq h1 (g_rowi st2 1ul));
  Lib.Sequence.eq_intro (as_seq h0 (g_rowi st1 2ul)) (as_seq h1 (g_rowi st2 2ul));
  Lib.Sequence.eq_intro (as_seq h0 (g_rowi st1 3ul)) (as_seq h1 (g_rowi st2 3ul));
  row_v_lemma h0 h1 (g_rowi st1 0ul) (g_rowi st2 0ul);
  Lib.Sequence.eq_intro (state_v h0 st1) (state_v h1 st2)
#pop-options

let state_v_rowi_lemma #a #m h st i = ()

let state_v_live_rowi_lemma #a #m h st i = ()

#push-options "--z3rlimit 50"
let modifies_one_row a m h0 h1 st i j =
    let ri = g_rowi st i in
    let rj = g_rowi st j in
    assert (live h0 ri);
    assert (live h0 rj);
    assert (modifies (loc ri) h0 h1);
    assert (disjoint rj ri);
    assert (as_seq h1 rj == as_seq h0 rj)

let modifies_row_state a m h0 h1 st i =
    Lib.Sequence.(eq_intro (state_v h1 st) ((state_v h0 st).[v i] <- row_v h1 (g_rowi st i)))
#pop-options


noextract inline_for_extraction
let rowi (#a:Spec.alg) (#m:m_spec) (st:state_p a m)  (idx:index_t) =
  sub st (idx *. row_len a m) (row_len a m)


noextract inline_for_extraction
let xor_row #a #m r1 r2 =
  match a,m with
  | Spec.Blake2S,M128 ->
    r1.(0ul) <- vec_xor #U32 #4 r1.(0ul) r2.(0ul)
  | Spec.Blake2S,M256 ->
    r1.(0ul) <- vec_xor #U32 #4 r1.(0ul) r2.(0ul)
  | Spec.Blake2B,M256 ->
    r1.(0ul) <- vec_xor #U64 #4 r1.(0ul) r2.(0ul)
  | _ -> map2T 4ul r1 (logxor #(Spec.wt a) #SEC) r1 r2


noextract inline_for_extraction
let add_row #a #m r1 r2 =
  match a,m with
  | Spec.Blake2S,M128 ->
    r1.(0ul) <- vec_add_mod #U32 #4 r1.(0ul) r2.(0ul)
  | Spec.Blake2S,M256 ->
    r1.(0ul) <- vec_add_mod #U32 #4 r1.(0ul) r2.(0ul)
  | Spec.Blake2B,M256 ->
    r1.(0ul) <- vec_add_mod #U64 #4 r1.(0ul) r2.(0ul)
  | _ -> map2T 4ul r1 (add_mod #(Spec.wt a) #SEC) r1 r2


#push-options "--z3rlimit 200"
noextract inline_for_extraction
let ror_row #a #m r1 r2 =
  match a,m with
  | Spec.Blake2S,M128 ->
    r1.(0ul) <- vec_rotate_right #U32 #4 r1.(0ul) r2
  | Spec.Blake2S,M256 ->
    r1.(0ul) <- vec_rotate_right #U32 #4 r1.(0ul) r2
  | Spec.Blake2B,M256 ->
    r1.(0ul) <- vec_rotate_right #U64 #4 r1.(0ul) r2
  | _ ->
    let r1:lbuffer (Spec.word_t a) 4ul = r1 in
    mapT 4ul r1 (rotate_right_i  r2) r1
#pop-options

#push-options "--z3rlimit 50"
noextract inline_for_extraction
let permr_row #a #m r1 n =
  [@inline_let]
  let n0 = n in
  [@inline_let]
  let n1 = (n+.1ul)%.4ul in
  [@inline_let]
  let n2 = (n+.2ul)%.4ul in
  [@inline_let]
  let n3 = (n+.3ul)%.4ul in
  match a,m with
  | Spec.Blake2S,M256
  | Spec.Blake2S,M128 ->
    let v0 : vec_t U32 4 = r1.(0ul) in
    let v1 : vec_t U32 4 = vec_rotate_right_lanes #U32 v0 n0 in
    Lib.Sequence.(eq_intro (create4 (vec_v v0).[v n0] (vec_v v0).[v n1] (vec_v v0).[v n2] (vec_v v0).[v n3]) (Lib.Sequence.(createi 4 (fun i -> (vec_v v0).[(i+v n)%4]))));
    Lib.Sequence.(eq_intro (Spec.rotr (vec_v v0) (v n)) (Lib.Sequence.(createi 4 (fun i -> (vec_v v0).[(i+v n)%4]))));
    r1.(0ul) <- v1
  | Spec.Blake2B,M256 ->
    let v0 : vec_t U64 4 = r1.(0ul) in
    let v1 : vec_t U64 4 = vec_rotate_right_lanes #U64 v0 n0 in
    Lib.Sequence.(eq_intro (create4 (vec_v v0).[v n0] (vec_v v0).[v n1] (vec_v v0).[v n2] (vec_v v0).[v n3]) (Lib.Sequence.(createi 4 (fun i -> (vec_v v0).[(i+v n)%4]))));
    Lib.Sequence.(eq_intro (Spec.rotr (vec_v v0) (v n)) (Lib.Sequence.(createi 4 (fun i -> (vec_v v0).[(i+v n)%4]))));
    r1.(0ul) <- v1
  | _ ->
    let h0 = ST.get() in
    let r1:lbuffer (Spec.word_t a) 4ul = r1 in
    let x0 = r1.(n0) in
    let x1 = r1.(n1) in
    let x2 = r1.(n2) in
    let x3 = r1.(n3) in
    r1.(0ul) <- x0;
    r1.(1ul) <- x1;
    r1.(2ul) <- x2;
    r1.(3ul) <- x3;
    let h1 = ST.get() in
    Lib.Sequence.(let s0 = as_seq h0 r1 in eq_intro (create4 x0 x1 x2 x3) (createi 4 (fun i -> s0.[(i+v n)%4])));
    Lib.Sequence.(let s0 = as_seq h0 r1 in eq_intro (Spec.rotr s0 (v n)) (Lib.Sequence.(createi 4 (fun i -> s0.[(i+v n)%4]))));
    Lib.Sequence.(eq_intro (as_seq h1 r1) (create4 x0 x1 x2 x3));
    ()
#pop-options

#push-options "--z3rlimit 50"
let create4_lemma #a x0 x1 x2 x3 =
  let open Lib.Sequence in
  let l : list a = [x0;x1;x2;x3] in
  assert_norm (List.Tot.length l = 4);
  let s1 : lseq a 4 = of_list l in
  let s2 : lseq a 4 = create4 x0 x1 x2 x3 in
  Seq.intro_of_list s2 l;
  eq_intro s1 s2
#pop-options

noextract inline_for_extraction
let alloc_row a m = create (row_len a m) (zero_element a m)

noextract inline_for_extraction
let create_row #a #m r w0 w1 w2 w3 =
  match a,m with
  | Spec.Blake2S,M256
  | Spec.Blake2S,M128
  | Spec.Blake2B,M256 ->
    r.(0ul) <- vec_load4 w0 w1 w2 w3
  | _ ->
    r.(0ul) <- w0;
    r.(1ul) <- w1;
    r.(2ul) <- w2;
    r.(3ul) <- w3;
    let h1 = ST.get() in
    Lib.Sequence.eq_intro (as_seq h1 r) (Lib.Sequence.create4 w0 w1 w2 w3)

noextract inline_for_extraction
let load_row #a #m r ws = create_row r ws.(0ul) ws.(1ul) ws.(2ul) ws.(3ul)

noextract inline_for_extraction
let store_row #a #m b r =
  match a,m with
  | Spec.Blake2S,M256
  | Spec.Blake2S,M128 ->
    vec_store_le #U32 #4 b r.(0ul)
  | Spec.Blake2B,M256 ->
    vec_store_le #U64 #4 b r.(0ul)
  | _ ->
    uints_to_bytes_le #(Spec.wt a) 4ul b r

noextract inline_for_extraction
val lemma_uints_to_bytes_le_i :
  #t : inttype{unsigned t /\ ~(U1? t)} ->
  #l : secrecy_level ->
  #len:size_nat{len * numbytes t < pow2 32} ->
  s : Lib.Sequence.lseq (uint_t t l) len ->
  i : size_nat {i < len} ->
  Lemma(Lib.Sequence.sub (Lib.ByteSequence.uints_to_bytes_le #t #l s) (i * numbytes t) (numbytes t) == Lib.ByteSequence.uint_to_bytes_le (Lib.Sequence.index s i))

noextract inline_for_extraction
let lemma_uints_to_bytes_le_i #t #l #len s i =
  let lemma_uints_to_bytes_le_i_j (#t : inttype{unsigned t /\ ~(U1? t)})
    (#l : secrecy_level)
    (#len:size_nat{len * numbytes t < pow2 32})
    (s : Lib.Sequence.lseq (uint_t t l) len)
    (i : size_nat {i < len})
    (j : size_nat {j < numbytes t}):
      Lemma(Lib.Sequence.index (Lib.ByteSequence.uints_to_bytes_le #t #l s) (i * numbytes t + j) == Lib.Sequence.index (Lib.ByteSequence.uint_to_bytes_le (Lib.Sequence.index s i)) j)
      [SMTPat (Lib.Sequence.index (Lib.ByteSequence.uints_to_bytes_le #t #l s) (i * numbytes t + j))] = 
    Lib.ByteSequence.index_uints_to_bytes_le #t #l #len s (i*numbytes t + j);
    assert (Lib.Sequence.index (Lib.ByteSequence.uints_to_bytes_le #t #l s) (i*numbytes t + j) ==
           Lib.Sequence.index (Lib.ByteSequence.uint_to_bytes_le (Lib.Sequence.index s i)) j) in
  

  Lib.Sequence.eq_intro (Lib.Sequence.sub (Lib.ByteSequence.uints_to_bytes_le #t #l s) (i * numbytes t) (numbytes t)) (Lib.ByteSequence.uint_to_bytes_le (Lib.Sequence.index s i))

noextract inline_for_extraction
val lemma_uints_to_from_bytes_le_preserves_value :
  #t : inttype{unsigned t /\ ~(U1? t)} ->
  #l : secrecy_level ->
  #len:size_nat{len * numbytes t < pow2 32} ->
  s : Lib.Sequence.lseq (uint_t t l) len ->
  Lemma(Lib.ByteSequence.uints_from_bytes_le #t #l (Lib.ByteSequence.uints_to_bytes_le #t #l s) == s)

let lemma_uints_to_from_bytes_le_preserves_value #t #l #len s =
  let lemma_uints_to_from_bytes_le_preserves_value_i
  (#t : inttype{unsigned t /\ ~(U1? t)})
  (#l : secrecy_level)
  (#len:size_nat{len * numbytes t < pow2 32})
  (s : Lib.Sequence.lseq (uint_t t l) len)
  (i : size_nat {i < len}) :
  Lemma(Lib.Sequence.index (Lib.ByteSequence.uints_from_bytes_le #t #l (Lib.ByteSequence.uints_to_bytes_le #t #l s)) i == Lib.Sequence.index s i)
  [SMTPat (Lib.Sequence.index (Lib.ByteSequence.uints_from_bytes_le #t #l (Lib.ByteSequence.uints_to_bytes_le #t #l s)) i)] =
  let b8 = Lib.ByteSequence.uints_to_bytes_le #t #l s in
  Lib.ByteSequence.index_uints_from_bytes_le #t #l #len b8 i;
  assert (Lib.Sequence.index (Lib.ByteSequence.uints_from_bytes_le b8) i ==
          Lib.ByteSequence.uint_from_bytes_le (Lib.Sequence.sub b8 (i * numbytes t) (numbytes t)));
  lemma_uints_to_bytes_le_i s i;
  assert (Lib.Sequence.sub b8 (i * numbytes t) (numbytes t) == Lib.ByteSequence.uint_to_bytes_le (Lib.Sequence.index s i));
  Lib.ByteSequence.lemma_uint_to_from_bytes_le_preserves_value (Lib.Sequence.index s i) in

  
  Lib.Sequence.eq_intro (Lib.ByteSequence.uints_from_bytes_le #t #l (Lib.ByteSequence.uints_to_bytes_le #t #l s)) s

noextract inline_for_extraction
let store_row32 #a #m b r =
  push_frame();
  let h0 = ST.get() in
  let b8 = create (size_row a) (u8 0) in
  store_row b8 r;
  let h1 = ST.get() in
  uints_from_bytes_le b b8;
  let h2 = ST.get() in
  assert (as_seq  h1 b8 == Lib.ByteSequence.uints_to_bytes_le #(Spec.wt a) (row_v h0 r));
  assert (as_seq  h2 b == Lib.ByteSequence.uints_from_bytes_le #(Spec.wt a) (as_seq h1 b8));
  Lib.Sequence.eq_intro (as_seq h2 b) (Spec.load_row (as_seq h2 b));
  assert (Spec.load_row (as_seq  h2 b) ==
          Lib.ByteSequence.uints_from_bytes_le (as_seq h1 b8));
  lemma_uints_to_from_bytes_le_preserves_value (row_v h0 r);
  pop_frame()

noextract inline_for_extraction
let gather_row #a #ms r m i0 i1 i2 i3 =
    create_row r m.(i0) m.(i1) m.(i2) m.(i3)

let alloc_state a m =
  create (4ul *. row_len a m) (zero_element a m)

let copy_state #a #m st2 st1 =
  copy #_ #_ #(4ul *. row_len a m) st2 st1

#push-options "--z3rlimit 100"
let load_state_from_state32 #a #m st st32 =
    let r0 = rowi st 0ul in
    let r1 = rowi st 1ul in
    let r2 = rowi st 2ul in
    let r3 = rowi st 3ul in
    let b0 = rowi st32 0ul in
    let b1 = rowi st32 1ul in
    let b2 = rowi st32 2ul in
    let b3 = rowi st32 3ul in
    g_rowi_disjoint_other #_ #_ #(word_t a) st 0ul st32;
    g_rowi_disjoint_other #_ #_ #(element_t a m) st32 0ul st;
    g_rowi_disjoint_other #_ #_ #(word_t a) st 1ul st32;
    g_rowi_disjoint_other #_ #_ #(element_t a m) st32 1ul st;
    g_rowi_disjoint_other #_ #_ #(word_t a) st 2ul st32;
    g_rowi_disjoint_other #_ #_ #(element_t a m) st32 2ul st;
    g_rowi_disjoint_other #_ #_ #(word_t a) st 3ul st32;
    g_rowi_disjoint_other #_ #_ #(element_t a m) st32 3ul st;
    assert (disjoint r0 st32);
    assert (disjoint r0 b0);
    assert (disjoint r1 st32);
    assert (disjoint r1 b1);
    let h0 = ST.get() in
    load_row r0 b0;
    load_row r1 b1;
    load_row r2 b2;
    load_row r3 b3;
    let h1 = ST.get() in
    Lib.Sequence.eq_intro (as_seq h0 b0) (Spec.load_row #a (as_seq h0 b0));
    Lib.Sequence.eq_intro (as_seq h0 b1) (Spec.load_row #a (as_seq h0 b1));
    Lib.Sequence.eq_intro (as_seq h0 b2) (Spec.load_row #a (as_seq h0 b2));
    Lib.Sequence.eq_intro (as_seq h0 b3) (Spec.load_row #a (as_seq h0 b3));
    assert(row_v h0 b0 == Spec.load_row (as_seq h0 b0));
    assert(row_v h1 r0 == row_v h0 b0);
    assert (state_v h1 st == state_v h0 st32)
#pop-options

#push-options "--z3rlimit 100"
let store_state_to_state32 #a #m st32 st =
    let r0 = rowi st 0ul in
    let r1 = rowi st 1ul in
    let r2 = rowi st 2ul in
    let r3 = rowi st 3ul in
    let b0 = rowi st32 0ul in
    let b1 = rowi st32 1ul in
    let b2 = rowi st32 2ul in
    let b3 = rowi st32 3ul in
    g_rowi_disjoint_other #_ #_ #(word_t a) st 0ul st32;
    g_rowi_disjoint_other #_ #_ #(element_t a m) st32 0ul st;
    g_rowi_disjoint_other #_ #_ #(word_t a) st 1ul st32;
    g_rowi_disjoint_other #_ #_ #(element_t a m) st32 1ul st;
    g_rowi_disjoint_other #_ #_ #(word_t a) st 2ul st32;
    g_rowi_disjoint_other #_ #_ #(element_t a m) st32 2ul st;
    g_rowi_disjoint_other #_ #_ #(word_t a) st 3ul st32;
    g_rowi_disjoint_other #_ #_ #(element_t a m) st32 3ul st;
    assert (disjoint r0 b0);
    assert (disjoint r1 b1);
    assert (disjoint r2 b2);
    assert (disjoint r3 b3);
    let h0 = ST.get() in
    store_row32 b0 r0;
    store_row32 b1 r1;
    store_row32 b2 r2;
    store_row32 b3 r3;
    let h1 = ST.get() in
    Lib.Sequence.eq_intro (as_seq h1 b0) (Spec.load_row #a (as_seq h1 b0));
    Lib.Sequence.eq_intro (as_seq h1 b1) (Spec.load_row #a (as_seq h1 b1));
    Lib.Sequence.eq_intro (as_seq h1 b2) (Spec.load_row #a (as_seq h1 b2));
    Lib.Sequence.eq_intro (as_seq h1 b3) (Spec.load_row #a (as_seq h1 b3));
    assert (state_v h1 st32 == state_v h0 st)
#pop-options
