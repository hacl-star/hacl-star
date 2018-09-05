(* Agile HMAC *)
module EverCrypt.HMAC

/// Agile specification

open EverCrypt.Helpers
open FStar.Integers
open FStar.Seq

let wrap (a:alg) (key: bytes{length key <= maxLength a}): GTot (lbseq (blockLength a))
=
  let key0 = if length key <= blockLength a then key else spec a key in
  let paddingLength = blockLength a - length key0 in
  key0 @| Seq.create paddingLength 0uy

private let wrap_lemma (a:alg) (key: bseq{Seq.length key <= maxLength a}): Lemma
  (requires length key > blockLength a)
  (ensures wrap a key == (
    let key0 = spec a key in
    let paddingLength = blockLength a - length key0 in
    key0 @| Seq.create paddingLength 0uy)) = ()

// better than Integer's [^^] to tame polymorphism in the proof?
inline_for_extraction
let xor8 (x y: uint8_t): uint8_t = x ^^ y

let xor (x: uint8_t) (v: bseq): GTot (lbseq (length v)) =
  Spec.Loops.seq_map (xor8 x) v

let rec xor_lemma (x: uint8_t) (v: bseq) : Lemma (requires True)
  (ensures (xor x v == Spec.Loops.seq_map2 xor8 (create (length v) x) v))
  (decreases (length v)) =
  let l = length v in
  if l = 0 then () else (
    let xs  = create l x in
    let xs' = create (l-1) x in
    lemma_eq_intro (tail xs) xs';
    xor_lemma x (tail v))
(*
    assert(// by induction
      xor (tail v) y == Spec.Loops.seq_map2 xor8 (tail v) ys');
    assert(// by definition
      Spec.Loops.seq_map (fun x -> xor8 x y) v ==
      cons
        (xor8 (head v) y)
        (Spec.Loops.seq_map (fun x -> xor8 x y) (tail v)));
    assert(// by definition
      xor v y ==
      cons
        (xor8 (head v) y)
        (xor (tail v) y));
    assert(// by definition
      Spec.Loops.seq_map2 xor8 v ys ==
      cons
        (xor8 (head v) (head ys))
        (Spec.Loops.seq_map2 xor8 (tail v) (tail ys)));
*)

let hmac a key data =
  assert(tagLength a + blockLength a <= maxLength a); // avoidable?
  let k = wrap a key in
  let h1 = spec a (xor 0x36uy k @| data) in
  let h2 = spec a (xor 0x5cuy k @| h1) in
  h2



/// Agile implementation

open FStar.HyperStack.ST
open FStar.Integers
open LowStar.Modifies
open LowStar.Buffer

module ST = FStar.HyperStack.ST

// we rely on the output being zero-initialized for the correctness of padding

[@"substitute"]
val wrap_key:
  a: ha ->
  output: uint8_pl (blockLength a) ->
  key: uint8_p {length key <= maxLength a /\ disjoint output key} ->
  len: UInt32.t {v len = length key} ->
  Stack unit
    (requires fun h0 ->
      live h0 output /\ live h0 key /\
      as_seq h0 output == Seq.create (blockLength a) 0uy)
    (ensures fun h0 _ h1 ->
      live h1 output /\ live h1 key /\ live h0 output /\ live h0 key /\
      as_seq h0 output == Seq.create (blockLength a) 0uy /\
      modifies (loc_buffer output) h0 h1 /\
      as_seq h1 output = wrap a (as_seq h0 key) )

let wrap_key a output key len =
  [@inline_let] //18-08-02 does *not* prevents unused-but-set-variable warning in C
  let i = if len <= blockLen a then len else tagLen a in
  let nkey = sub output 0ul i in
  let h0 = ST.get () in
  if len <= blockLen a then
    blit key 0ul nkey 0ul len
  else
    Hash.hash a nkey key len;
  let h1 = ST.get () in (
    let pad = sub output i (blockLen a - i) in
    Seq.lemma_eq_intro (as_seq h0 pad) (Seq.create (blockLength a - v i) 0uy);
    Seq.lemma_split (as_seq h1 output) (v i)
  )

// we pre-allocate the variable-type, variable length hash state,
// to avoid both verification and extraction problems.

val part1:
  a: alg -> 
  acc: state a ->
  s2: uint8_pl (blockLength a) ->
  data: uint8_p {
    length data + blockLength a  < pow2 32 /\ (*required by 32-bit length for update_last *)
    // length data + blockLength a <= maxLength a /\ (*always true*)
    disjoint data s2} ->
  len: UInt32.t {length data = v len} ->
  ST unit
    (requires fun h0 ->
      loc_disjoint (footprint acc h0) (loc_buffer s2) /\
      loc_disjoint (footprint acc h0) (loc_buffer data) /\
      invariant acc h0 /\
      live h0 s2 /\
      live h0 data)
    (ensures  fun h0 _ h1 ->
      live h1 s2 /\ live h1 data /\
      invariant acc h1 /\
      footprint acc h1 == footprint acc h0 /\ //18-08-02 avoidable? this footprint is constant!
      modifies (loc_union (footprint acc h0) (loc_buffer s2)) h0 h1 /\
      (
      let hash0 = Seq.slice (as_seq h1 s2) 0 (tagLength a) in
      length data + blockLength a <= maxLength a /\ (*always true, required by spec below*)
      hash0 == spec a (Seq.append (as_seq h0 s2) (as_seq h0 data))))

#reset-options "--max_fuel 0 --z3rlimit 1000" // without hints

// we use auxiliary functions only for clarity and proof modularity
[@"substitute"]
let part1 a (acc: state a) key data len =
  assert_norm(pow2 32 + blockLength a <= maxLength a);
  let ll = len % blockLen a in
  let lb = len - ll in
  let blocks = sub data 0ul lb in
  let last = offset data lb in
  Hash.init #(Ghost.hide a) acc;
  let h0 = ST.get() in //assume(bounded_counter acc h0 1);
  Hash.update
    #(Ghost.hide a)
    (Ghost.hide Seq.empty)
    acc key;
  let h1 = ST.get() in
  assert(
    let k = as_seq h0 key in
    FStar.Seq.lemma_eq_intro (Seq.append (Seq.empty #UInt8.t) k) k;
    repr acc h1 == hash0 k);
  Hash.update_multi
    #(Ghost.hide a)
    (Ghost.hide (as_seq h0 key))
    acc blocks lb;
  let h2 = ST.get() in
  assert_norm(blockLength a + v len <= maxLength a);
  Hash.update_last 
    #(Ghost.hide a)
    (Ghost.hide (Seq.append (as_seq h0 key) (as_seq h2 blocks)))
    acc last (blockLen a + len);
  let h3 = ST.get() in
  // assert(LowStar.Buffer.live h3 key);
  let tag = sub key 0ul (tagLen a) in (* Salvage memory *)
  Hash.finish #(Ghost.hide a) acc tag;
  let h4 = ST.get() in
  (
    modifies_trans (footprint acc h0) h0 h3 (loc_buffer key) h4; // should this implicitly trigger?
    let p = blockLength a in
    let key1 = as_seq h1 key in
    let blocks1 = as_seq h1 blocks in
    let acc1 = repr acc h1 in
    lemma_compress (acc0 #a) key1;
    assert(acc1 == hash0 key1);
    let v2 = key1 @| blocks1 in
    let acc2 = repr acc h2 in
    // assert (Seq.length key1 % p = 0);
    // assert (Seq.length blocks1 % p = 0);
    // assert (Seq.length v2 % p = 0);
    lemma_hash2 (acc0 #a) key1 blocks1;
    assert(acc2 == hash0 #a v2);
    let data1 = as_seq h1 data in
    let last1 = as_seq h1 last in
    let suffix1 = suffix a (p + v len) in
    Seq.lemma_eq_intro data1 (blocks1 @| last1);
    let acc3 = repr acc h3 in
    let ls = Seq.length suffix1 in
    assert((p + v len + ls) % p = 0);
    Math.Lemmas.lemma_mod_plus (v ll + ls) (1 + v len / p) p;
    assert((v ll + ls) % p = 0);
    lemma_hash2 (acc0 #a) v2 (last1 @| suffix1);
    assert(acc3 == hash0 #a (v2 @| (last1 @| suffix1)));
    Seq.append_assoc v2 last1 suffix1;
    Seq.append_assoc key1 blocks1 last1;
    assert(acc3 == hash0 #a ((key1 @| data1) @| suffix1));
    assert(extract acc3 == spec a (key1 @| data1)))

// the two parts have the same stucture; let's keep their proofs in sync.
[@"substitute"]
val part2:
  a: alg -> 
  acc: state a ->
  mac: uint8_pl (tagLength a) ->
  opad: uint8_pl (blockLength a) ->
  tag: uint8_pl (tagLength a) ->
  ST unit
    (requires fun h0 ->
      invariant acc h0 /\
      live h0 mac /\ live h0 opad /\ live h0 tag /\
      //18-08-02 anything more compact?
      disjoint mac opad /\ disjoint mac tag /\
      loc_disjoint (footprint acc h0) (loc_buffer opad) /\
      loc_disjoint (footprint acc h0) (loc_buffer tag) /\
      loc_disjoint (footprint acc h0) (loc_buffer mac))
    (ensures fun h0 _ h1 ->
      live h1 mac /\ live h1 opad /\ live h1 tag /\
      invariant acc h1 /\ footprint acc h1 == footprint acc h0 /\
      modifies (loc_union (footprint acc h0) (loc_buffer mac)) h0 h1 /\
      ( let payload = Seq.append (as_seq h0 opad) (as_seq h0 tag) in
        Seq.length payload <= maxLength a /\
        as_seq h1 mac = spec a payload))

[@"substitute"]
let part2 a acc mac opad tag =
  let totLen = blockLen a + tagLen a in
  assert_norm(v totLen <= maxLength a);
  let h0 = ST.get() in
  //assume(LowStar.Modifies.(loc_disjoint (footprint acc h0) (loc_buffer opad)));
  Hash.init #(Ghost.hide a) acc;
  Hash.update #(Ghost.hide a) (Ghost.hide Seq.empty) acc opad;
  let h1 = ST.get() in
  // assert(
  //   footprint acc h1 == footprint acc h0 /\
  //   LowStar.Buffer.live h1 mac /\
  //   LowStar.Modifies.(loc_disjoint (footprint acc h1) (loc_buffer mac)) );
  assert(
    let k = as_seq h0 opad in
    FStar.Seq.lemma_eq_intro (Seq.append (Seq.empty #UInt8.t) k) k;
    repr acc h1 == hash0 k);
  Hash.update_last #(Ghost.hide a) (Ghost.hide (as_seq h1 opad)) acc tag totLen;
  let h2 = ST.get() in
  // assert(
  //   LowStar.Buffer.live h2 mac /\
  //   LowStar.Modifies.(loc_disjoint (footprint acc h2) (loc_buffer mac)) );
  Hash.finish #(Ghost.hide a) acc mac;
  (
    let v1 = as_seq h1 opad in
    let acc1 = repr acc h1 in
    lemma_compress (acc0 #a) v1;
    assert(acc1 == hash0 v1);
    let tag1 = as_seq h1 tag in
    let suffix1 = suffix a (blockLength a + tagLength a) in
    let acc2 = repr acc h2 in
    lemma_hash2 (acc0 #a) v1 (tag1 @| suffix1);
    Seq.append_assoc v1 tag1 suffix1;
    assert(acc2 == hash0 ((v1 @| tag1) @| suffix1));
    assert(extract acc2 = spec a (v1 @| tag1)))

// similar spec as hmac with keylen = blockLen a
val hmac_core:
  a: alg -> 
  acc: state a ->
  tag: uint8_pl (tagLength a) ->
  key: uint8_pl (blockLength a) {disjoint key tag} ->
  data: uint8_p{
    length data + blockLength a < pow2 32 /\ (*required for 32-bit allocation*)
    // length data + blockLength a <= maxLength a /\ (*always true*)
    disjoint data key } ->
  datalen: UInt32.t {v datalen = length data} ->
  ST unit
  (requires fun h0 ->
    loc_disjoint (footprint acc h0) (loc_buffer tag) /\
    loc_disjoint (footprint acc h0) (loc_buffer key) /\
    loc_disjoint (footprint acc h0) (loc_buffer data) /\
    invariant acc h0 /\
    live h0 tag /\ live h0 key /\ live h0 data)
  (ensures fun h0 _ h1 ->
    invariant acc h1 /\ footprint acc h1 == footprint acc h0 /\
    live h1 tag /\ live h0 tag /\
    live h1 key /\ live h0 key /\
    live h1 data /\ live h0 data /\
    modifies (loc_union (footprint acc h0) (loc_buffer tag)) h0 h1 /\
    ( let k = as_seq h0 key in
      let k1 = xor 0x36uy k in
      let k2 = xor 0x5cuy k in
      length data + blockLength a <= maxLength a /\ ( (*always true*)
      let v1 = spec a (k1 @| as_seq h0 data) in
      Seq.length (k2 @| v1) <= maxLength a /\
      as_seq h1 tag == spec a (k2 @| v1))))

[@"substitute"]
val xor_bytes_inplace:
  a: uint8_p ->
  b: uint8_p ->
  len: UInt32.t {v len = length a /\ v len = length b} ->
  Stack unit
  (requires fun h0 -> disjoint a b /\ live h0 a /\ live h0 b)
  (ensures fun h0 _ h1 ->
    modifies (loc_buffer a) h0 h1 /\
    as_seq h1 a == Spec.Loops.seq_map2 xor8 (as_seq h0 a) (as_seq h0 b))
let xor_bytes_inplace a b len =
  let a = LowStar.ToFStarBuffer.new_to_old_st a in
  let b = LowStar.ToFStarBuffer.new_to_old_st b in
  C.Loops.in_place_map2 a b len xor8

// TODO small improvements: part1 and part2 could return their tags in
// mac, so that we can reuse the pad.


[@"substitute"]
let hmac_core a acc tag key data len =
  let h00 = ST.get() in
  push_frame ();
  let h01 = ST.get() in
  fresh_frame_modifies h00 h01; //18-08-02 a trigger would be nice!
  Hash.frame_invariant loc_none acc h00 h01;
  // assert(invariant acc h01);
  let ipad = alloca 0x36uy (blockLen a) in
  let h02 = ST.get() in
  //  assert (loc_in (footprint acc h01) h01);
  // TR: now works thanks to Hash.invariant_loc_in_footprint
  fresh_is_disjoint (loc_buffer ipad) (footprint acc h01)  h01 h02;
  let opad = alloca 0x5cuy (blockLen a) in
  xor_bytes_inplace ipad key (blockLen a);
  xor_bytes_inplace opad key (blockLen a);
  let h0 = ST.get() in
  modifies_address_liveness_insensitive_unused_in h01 h0;
  // assert(loc_in (footprint acc h0) h0);
  // TR: now works thanks to
  // modifies_address_liveness_insensitive_unused_in: if no
  // deallocations are performed, then all livenesses are preserved.
  frame_invariant (loc_union (loc_buffer ipad) (loc_buffer opad)) acc h01 h0;
  part1 a acc ipad data len;
  let h1 = ST.get() in
  let inner = sub ipad 0ul (tagLen a) in (* salvage memory *)
  part2 a acc tag opad inner;
  let h2 = ST.get() in
  pop_frame ();
  (
    let h3 = ST.get() in
    let k = as_seq h0 key in
    let k1: lbseq (blockLength a) = xor 0x36uy k in
    let k2: lbseq (blockLength a) = xor 0x5cuy k in
    let vdata = as_seq h0 data in
    let v1: lbseq (tagLength a) = as_seq h1 inner in
    assert_norm(blockLength a + tagLength a <= maxLength a);
    assert(Seq.length (k2 @| v1) <= maxLength a);
    let v2 = as_seq h2 tag in
    xor_lemma 0x36uy k;
    xor_lemma 0x5cuy k;
    // assert(k1 == as_seq h0 ipad);
    // assert(k2 == as_seq h1 opad);
    assert(v1 == spec a (k1 @| vdata));
    assert(v2 == spec a (k2 @| v1));

    // TR: modifies clause now automatically proven thanks to
    // pattern provided in Hash.loc_includes_union_l_footprint

    // 18-08-02 missing lemma? data and tag have the same base type.
    // assume(as_addr data = as_addr tag /\ live h2 tag ==> live h2 data);
    // TR: We don't need this lemma. In fact, here is a generic way
    // of proving that liveness of buffers is preserved: any
    // modified location that does not necessarily have its liveness
    // preserved (e.g. an abstract footprint) shall be disjoint from
    // any location whose liveness we want to preserve.
    modifies_liveness_insensitive_buffer (footprint acc h00) (loc_buffer tag) h00 h3 tag;
    modifies_liveness_insensitive_buffer (footprint acc h00) (loc_buffer tag) h00 h3 key;
    modifies_liveness_insensitive_buffer (footprint acc h00) (loc_buffer tag) h00 h3 data;

    //18-08-02 How to move those across pop?
    // assume(
    //   invariant acc h2 /\ footprint acc h2 == footprint acc h00 ==>
    //   invariant acc h3 /\ footprint acc h3 == footprint acc h00) )
    // TR: now works thanks to:
    // LowStar.Buffer.fresh_frame_loc_not_unused_in_disjoint
    frame_invariant (loc_region_only false (HyperStack.get_tip h1)) acc h2 h3
  )

let compute a mac key keylen data datalen =
  let h00 = ST.get() in
  push_frame ();
  assert_norm(pow2 32 + blockLength a <= maxLength a);
  assert(length data + blockLength a <= maxLength a);
  let keyblock = alloca 0x00uy (blockLen a) in
  let acc = Hash.create a in
  let h0 = ST.get() in
  wrap_key a keyblock key keylen;
  let h1 = ST.get() in
  Hash.frame_invariant (loc_buffer keyblock) acc h0 h1;
  Hash.frame_invariant_implies_footprint_preservation (loc_buffer keyblock) acc h0 h1;
  hmac_core a acc mac keyblock data datalen;
  let h2 = ST.get() in
  Hash.free #(Ghost.hide a) acc;
  pop_frame ();
  let hf = ST.get () in
  // TR: modifies clause proven by erasing all memory locations that
  // were unused in h00:
  LowStar.Buffer.modifies_only_not_unused_in (loc_buffer mac) h00 hf





(* 18-08-02 older stuff. Was:
// not much point in separating hmac_core? verbose, but it helps
// monomorphise stack allocations.

let compute a mac key keylen data datalen =
  push_frame ();
  assert_norm(pow2 32 <= maxLength a);
  let keyblock = Buffer.create 0x00uy (blockLen a) in
  wrap_key a keyblock key keylen;
  ( match a with
  | SHA256 ->
      push_frame();
      // 18-04-15 hardcoding the type to prevent extraction errors :(
      let acc = Buffer.create #UInt32.t (state_zero a) (state_size a) in
      hmac_core SHA256 acc mac keyblock data datalen;
      pop_frame()
  | SHA384 ->
      push_frame();
      let acc = Buffer.create #UInt64.t (state_zero a) (state_size a) in
      hmac_core SHA384 acc mac keyblock data datalen;
      pop_frame()
  | SHA512 ->
      push_frame();
      let acc = Buffer.create #UInt64.t (state_zero a) (state_size a) in
      hmac_core SHA512 acc mac keyblock data datalen;
      pop_frame());
  pop_frame ()

// 18-04-11 this alternative is leaky and does not typecheck.
// I get an error pointing to `sub_effect DIV ~> GST = lift_div_gst` in HyperStack

let compute a mac key keylen data datalen =
  push_frame ();
  let keyblock = Buffer.create 0x00uy (blockLen a) in
  assert_norm(pow2 32 <= maxLength a);
  wrap_key a keyblock key keylen;
  let acc =
    match a with
    | SHA256 -> Buffer.rcreate HyperStack.root 0ul (state_size a)
    | SHA384 -> Buffer.rcreate HyperStack.root 0UL (state_size a)
    | SHA512 -> Buffer.rcreate HyperStack.root 0UL (state_size a) in
  hmac_core SHA256 acc mac keyblock data datalen;
  pop_frame ()
*)
