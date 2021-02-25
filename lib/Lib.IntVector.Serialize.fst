module Lib.IntVector.Serialize

// the proofs are the same as in Lib.ByteSequence and Lib.ByteBuffer

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val vecs_from_bytes_le_f:
    vt:v_inttype
  -> w:width
  -> len:nat{len * (numbytes vt * w) <= max_size_t}
  -> b:lseq uint8 (len * (numbytes vt * w))
  -> i:nat{i < len} ->
  vec_t vt w

let vecs_from_bytes_le_f vt w len b i =
  vec_from_bytes_le vt w (LSeq.sub b (i * (numbytes vt * w)) (numbytes vt * w))

let vecs_from_bytes_le vt w len b =
  LSeq.createi len (vecs_from_bytes_le_f vt w len b)

let index_vecs_from_bytes_le vt w len b i = ()


val vecs_from_bytes_be_f:
    vt:v_inttype
  -> w:width
  -> len:nat{len * (numbytes vt * w) <= max_size_t}
  -> b:lseq uint8 (len * (numbytes vt * w))
  -> i:nat{i < len} ->
  vec_t vt w

let vecs_from_bytes_be_f vt w len b i =
  vec_from_bytes_be vt w (LSeq.sub b (i * (numbytes vt * w)) (numbytes vt * w))

let vecs_from_bytes_be vt w len b =
  LSeq.createi len (vecs_from_bytes_be_f vt w len b)

let index_vecs_from_bytes_be vt w len b i = ()


val vecs_to_bytes_le_f:
    #vt:v_inttype
  -> #w:width
  -> #len:nat{len * (numbytes vt * w) <= max_size_t}
  -> vl:lseq (vec_t vt w) len
  -> i:nat{i < len}
  -> unit ->
  unit & lseq uint8 (numbytes vt * w)

let vecs_to_bytes_le_f #vt #w #len vl i () =
  (), vec_to_bytes_le vl.[i]

let vecs_to_bytes_le #vt #w #len vl =
  let a_spec (i:nat{i <= len}) = unit in
  let _, o = generate_blocks (numbytes vt * w) len len a_spec
    (vecs_to_bytes_le_f #vt #w #len vl) () in
  o

let index_vecs_to_bytes_le #vt #w #len vl i =
  index_generate_blocks (numbytes vt * w) len len
    (vecs_to_bytes_le_f #vt #w #len vl) i


val vecs_to_bytes_be_f:
    #vt:v_inttype
  -> #w:width
  -> #len:nat{len * (numbytes vt * w) <= max_size_t}
  -> vl:lseq (vec_t vt w) len
  -> i:nat{i < len}
  -> unit ->
  unit & lseq uint8 (numbytes vt * w)

let vecs_to_bytes_be_f #vt #w #len vl i () =
  (), vec_to_bytes_be vl.[i]

let vecs_to_bytes_be #vt #w #len vl =
  let a_spec (i:nat{i <= len}) = unit in
  let _, o = generate_blocks (numbytes vt * w) len len a_spec
    (vecs_to_bytes_be_f #vt #w #len vl) () in
  o

let index_vecs_to_bytes_be #vt #w #len vl i =
  index_generate_blocks (numbytes vt * w) len len
    (vecs_to_bytes_be_f #vt #w #len vl) i


let vecs_load_le #vt #w #len o i =
  let h0 = ST.get () in
  fill h0 len o
  (fun h -> vecs_from_bytes_le_f vt w (v len) (as_seq h i))
  (fun j ->
    let h = ST.get () in
    let bj = sub i (j *! (size (numbytes vt) *! size w)) (size (numbytes vt) *! size w) in
    let r = vec_load_le vt w bj in
    as_seq_gsub h i (j *! (size (numbytes vt) *! size w)) (size (numbytes vt) *! size w);
    r);
  let h1 = ST.get () in
  eq_intro (as_seq h1 o) (vecs_from_bytes_le vt w (v len) (as_seq h0 i))


let vecs_load_be #vt #w #len o i =
  let h0 = ST.get () in
  fill h0 len o
  (fun h -> vecs_from_bytes_be_f vt w (v len) (as_seq h i))
  (fun j ->
    let h = ST.get () in
    let bj = sub i (j *! (size (numbytes vt) *! size w)) (size (numbytes vt) *! size w) in
    let r = vec_load_be vt w bj in
    as_seq_gsub h i (j *! (size (numbytes vt) *! size w)) (size (numbytes vt) *! size w);
    r);
  let h1 = ST.get () in
  eq_intro (as_seq h1 o) (vecs_from_bytes_be vt w (v len) (as_seq h0 i))


#set-options "--z3rlimit 100"

let vecs_store_le #vt #w #len o i =
  let h0 = ST.get () in
  [@ inline_let]
  let a_spec (i:nat{i <= v len}) = unit in

  fill_blocks h0 (size (numbytes vt) *! size w) len o a_spec
    (fun _ _ -> ())
    (fun _ -> LowStar.Buffer.loc_none)
    (fun h -> vecs_to_bytes_le_f (as_seq h i))
    (fun j -> vec_store_le (sub o (j *! (size (numbytes vt) *! size w)) (size (numbytes vt) *! size w)) i.(j));

  norm_spec [delta_only [`%vecs_to_bytes_le]] (vecs_to_bytes_le (as_seq h0 i))


let vecs_store_be #vt #w #len o i =
  let h0 = ST.get () in
  [@ inline_let]
  let a_spec (i:nat{i <= v len}) = unit in

  fill_blocks h0 (size (numbytes vt) *! size w) len o a_spec
    (fun _ _ -> ())
    (fun _ -> LowStar.Buffer.loc_none)
    (fun h -> vecs_to_bytes_be_f (as_seq h i))
    (fun j -> vec_store_be (sub o (j *! (size (numbytes vt) *! size w)) (size (numbytes vt) *! size w)) i.(j));

  norm_spec [delta_only [`%vecs_to_bytes_be]] (vecs_to_bytes_be (as_seq h0 i))
