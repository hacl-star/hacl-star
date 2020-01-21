module Hacl.Impl.Blake2.Core
module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.IntVector

module Spec = Spec.Blake2_Vec

inline_for_extraction
let zero_element (a:Spec.alg) (m:m_spec) : element_t a m =
  match a,m with
  | Spec.Blake2S,M128 -> (vec_zero U32 4)
  | Spec.Blake2S,M256 -> (vec_zero U32 4)
  | Spec.Blake2B,M256 -> (vec_zero U64 4)
  | _ -> Spec.zero a

inline_for_extraction
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
  create4 r0 r1 r2 r3

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


inline_for_extraction
let rowi (#a:Spec.alg) (#m:m_spec) (st:state_p a m)  (idx:index_t) =
  sub st (idx *. row_len a m) (row_len a m)


inline_for_extraction
let xor_row #a #m r1 r2 =
  match a,m with
  | Spec.Blake2S,M128 ->
    r1.(0ul) <- vec_xor #U32 #4 r1.(0ul) r2.(0ul)
  | Spec.Blake2S,M256 ->
    r1.(0ul) <- vec_xor #U32 #4 r1.(0ul) r2.(0ul)
  | Spec.Blake2B,M256 ->
    r1.(0ul) <- vec_xor #U64 #4 r1.(0ul) r2.(0ul)
  | _ -> map2T 4ul r1 (logxor #(Spec.wt a) #SEC) r1 r2


inline_for_extraction
let add_row #a #m r1 r2 =
  match a,m with
  | Spec.Blake2S,M128 ->
    r1.(0ul) <- vec_add_mod #U32 #4 r1.(0ul) r2.(0ul)
  | Spec.Blake2S,M256 ->
    r1.(0ul) <- vec_add_mod #U32 #4 r1.(0ul) r2.(0ul)
  | Spec.Blake2B,M256 ->
    r1.(0ul) <- vec_add_mod #U64 #4 r1.(0ul) r2.(0ul)
  | _ -> map2T 4ul r1 (add_mod #(Spec.wt a) #SEC) r1 r2


inline_for_extraction
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
    mapT 4ul r1 (rotate_right_i #(Spec.wt a) #SEC r2) r1


#push-options "--z3rlimit 50"
inline_for_extraction
let permr_row #a #m r1 n =
  let n0,n1,n2,n3 = n,(n+.1ul)%.4ul,(n+.2ul)%.4ul,(n+.3ul)%.4ul in
  match a,m with
  | Spec.Blake2S,M256
  | Spec.Blake2S,M128 ->
    let v0 : vec_t U32 4 = r1.(0ul) in
    let v1 : vec_t U32 4 = vec_permute4 #U32 v0 n0 n1 n2 n3 in
    Lib.Sequence.(eq_intro (create4 (vec_v v0).[v n0] (vec_v v0).[v n1] (vec_v v0).[v n2] (vec_v v0).[v n3]) (Lib.Sequence.(createi 4 (fun i -> (vec_v v0).[(i+v n)%4]))));
    Lib.Sequence.(eq_intro (Spec.rotr (vec_v v0) (v n)) (Lib.Sequence.(createi 4 (fun i -> (vec_v v0).[(i+v n)%4]))));
    r1.(0ul) <- v1
  | Spec.Blake2B,M256 ->
    let v0 : vec_t U64 4 = r1.(0ul) in
    let v1 : vec_t U64 4 = vec_permute4 #U64 v0 n0 n1 n2 n3 in
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
  assert_norm (List.Tot.index l 0 == x0);
  assert_norm (List.Tot.index l 1 == x1);
  assert_norm (List.Tot.index l 2 == x2);
  assert_norm (List.Tot.index l 3 == x3);
  let s1 : lseq a 4 = of_list l in
  let s2 : lseq a 4 = create4 x0 x1 x2 x3 in
  eq_intro s1 s2
#pop-options

inline_for_extraction
let alloc_row a m = create (row_len a m) (zero_element a m)


inline_for_extraction
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
    Lib.Sequence.eq_intro (as_seq h1 r) (create4 w0 w1 w2 w3)

inline_for_extraction
let load_row #a #m r ws = create_row r ws.(0ul) ws.(1ul) ws.(2ul) ws.(3ul)

inline_for_extraction
let store_row #a #m b r =
  match a,m with
  | Spec.Blake2S,M256
  | Spec.Blake2S,M128 ->
    vec_store_le #U32 #4 b r.(0ul)
  | Spec.Blake2B,M256 ->
    vec_store_le #U64 #4 b r.(0ul)
  | _ ->
    uints_to_bytes_le #(Spec.wt a) 4ul b r

#push-options "--z3rlimit 100"
inline_for_extraction
let gather_row #a #ms r m i0 i1 i2 i3 =
  let h0 = ST.get() in
  let nb = size (numbytes (Spec.wt a)) in
  let b0 = sub m (i0 *. nb) nb in
  let b1 = sub m (i1 *. nb) nb in
  let b2 = sub m (i2 *. nb) nb in
  let b3 = sub m (i3 *. nb) nb in
  as_seq_gsub h0 m (i0 *. nb) nb;
  as_seq_gsub h0 m (i1 *. nb) nb;
  as_seq_gsub h0 m (i2 *. nb) nb;
  as_seq_gsub h0 m (i3 *. nb) nb;
  assert (as_seq h0 b0 == Lib.Sequence.sub (as_seq h0 m) (v i0 * Spec.size_word a) (Spec.size_word a));
  assert (as_seq h0 b1 == Lib.Sequence.sub (as_seq h0 m) (v i1 * Spec.size_word a) (Spec.size_word a));
  assert (as_seq h0 b2 == Lib.Sequence.sub (as_seq h0 m) (v i2 * Spec.size_word a) (Spec.size_word a));
  assert (as_seq h0 b3 == Lib.Sequence.sub (as_seq h0 m) (v i3 * Spec.size_word a) (Spec.size_word a));
  let u0 = uint_from_bytes_le #(Spec.wt a) b0 in
  let u1 = uint_from_bytes_le #(Spec.wt a) b1 in
  let u2 = uint_from_bytes_le #(Spec.wt a) b2 in
  let u3 = uint_from_bytes_le #(Spec.wt a) b3 in
  assert (u0 == Lib.ByteSequence.uint_from_bytes_le (as_seq h0 b0));
  create_row r u0 u1 u2 u3
#pop-options

let alloc_state a m =
  create (4ul *. row_len a m) (zero_element a m)

let copy_state #a #m st2 st1 =
  copy #_ #_ #(4ul *. row_len a m) st2 st1

