(* Agile HMAC *)
module EverCrypt.HMAC

module S = FStar.Seq

/// Agile specification

open EverCrypt.Helpers
open FStar.Integers

let _: squash (inversion alg) = allow_inversion alg

noextract inline_for_extraction
let spec = Spec.Hash.Nist.hash

#set-options "--max_fuel 0 --max_ifuel 0"
let wrap (a:alg) (key: bytes{S.length key < max_input8 a}): GTot (lbytes (size_block a))
=
  let key0 = if S.length key <= size_block a then key else spec a key in
  let paddingLength = size_block a - S.length key0 in
  S.append key0 (S.create paddingLength 0uy)

let wrap_lemma (a:alg) (key: bytes{Seq.length key < max_input8 a}): Lemma
  (requires S.length key > size_block a)
  (ensures wrap a key == (
    let key0 = spec a key in
    let paddingLength = size_block a - S.length key0 in
    S.append key0 (S.create paddingLength 0uy))) = ()

// better than Integer's [^^] to tame polymorphism in the proof?
inline_for_extraction
let xor8 (x y: uint8_t): uint8_t = x ^^ y

let xor (x: uint8_t) (v: bytes): GTot (lbytes (S.length v)) =
  Spec.Loops.seq_map (xor8 x) v

#push-options "--max_fuel 1"
let rec xor_lemma (x: uint8_t) (v: bytes) : Lemma (requires True)
  (ensures (xor x v == Spec.Loops.seq_map2 xor8 (S.create (S.length v) x) v))
  (decreases (S.length v)) =
  let l = S.length v in
  if l = 0 then () else (
    let xs  = S.create l x in
    let xs' = S.create (l-1) x in
    S.lemma_eq_intro (S.tail xs) xs';
    xor_lemma x (S.tail v))
#pop-options

let hmac a key data =
  let k = wrap a key in
  let h1 = spec a S.(xor 0x36uy k @| data) in
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 32 < pow2 125);
  let h2 = spec a S.(xor 0x5cuy k @| h1) in
  h2


/// Agile implementation

open FStar.HyperStack.ST
open FStar.Integers
open LowStar.Modifies
open LowStar.Buffer

module ST = FStar.HyperStack.ST

// we rely on the output being zero-initialized for the correctness of padding

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 50"

inline_for_extraction
val wrap_key:
  a: ha ->
  output: uint8_pl (size_block a) ->
  key: uint8_p {length key < max_input8 a /\ disjoint output key} ->
  len: UInt32.t {v len = length key} ->
  Stack unit
    (requires fun h0 ->
      live h0 output /\ live h0 key /\
      as_seq h0 output == Seq.create (size_block a) 0uy)
    (ensures fun h0 _ h1 ->
      live h1 output /\ live h1 key /\ live h0 output /\ live h0 key /\
      as_seq h0 output == Seq.create (size_block a) 0uy /\
      modifies (loc_buffer output) h0 h1 /\
      as_seq h1 output == wrap a (as_seq h0 key) )

unfold
let block_len a = Hacl.Hash.Definitions.size_block_ul a

unfold
let tag_len a = Hacl.Hash.Definitions.size_hash_ul a

inline_for_extraction
let helper_smtpat (a: ha) (len: uint32_t{ v len < max_input8 a }):
  x:uint32_t { x <= block_len a } =
  if len <= block_len a then len else tag_len a

inline_for_extraction
let wrap_key a output key len =
  //[@inline_let] //18-08-02 does *not* prevents unused-but-set-variable warning in C
  let i = helper_smtpat a len in
  let nkey = sub output 0ul i in
  let zeroes = sub output i (block_len a - i) in
  assert (loc_disjoint (loc_buffer nkey) (loc_buffer zeroes));
  let h0 = ST.get () in
  assert (Seq.equal (as_seq h0 zeroes) (Seq.create (v (block_len a - i)) 0uy));
  if len <= block_len a then begin
    blit key 0ul nkey 0ul len;
    let h1 = ST.get () in
    assert (Seq.equal (as_seq h1 zeroes) (as_seq h0 zeroes));
    assert (Seq.equal (as_seq h1 nkey) (as_seq h0 key));
    assert (Seq.equal (as_seq h1 output) (S.append (as_seq h1 nkey) (as_seq h1 zeroes)));
    Seq.lemma_eq_elim (as_seq h1 output) (S.append (as_seq h1 nkey) (as_seq h1 zeroes));
    assert (as_seq h1 output == wrap a (as_seq h0 key))
  end else begin
    Hash.hash a nkey key len;
    let h1 = ST.get () in
    assert (Seq.equal (as_seq h1 zeroes) (as_seq h0 zeroes));
    assert (Seq.equal (as_seq h1 nkey) (spec a (as_seq h0 key)));
    assert (Seq.equal (as_seq h1 output) (S.append (as_seq h1 nkey) (as_seq h1 zeroes)));
    Seq.lemma_eq_elim (as_seq h1 output) (S.append (as_seq h1 nkey) (as_seq h1 zeroes));
    assert (as_seq h1 output == wrap a (as_seq h0 key))
  end


// we pre-allocate the variable-type, variable length hash state,
// to avoid both verification and extraction problems.

inline_for_extraction
val part1:
  a: alg -> 
  acc: state a ->
  s2: uint8_pl (size_block a) ->
  data: uint8_p {
    length data + size_block a  < pow2 32 /\ (*required by 32-bit length for update_last *)
    // length data + size_block a <= max_input8 a /\ (*always true*)
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
      let hash0 = Seq.slice (as_seq h1 s2) 0 (size_hash a) in
      length data + size_block a < max_input8 a /\ (*always true, required by spec below*)
      hash0 == spec a (Seq.append (as_seq h0 s2) (as_seq h0 data))))

let hash0 (#a:alg) (b:bytes_blocks a): GTot (acc a) =
  compress_many (acc0 #a) b

#push-options "--z3rlimit 100"

// we use auxiliary functions only for clarity and proof modularity
inline_for_extraction
let part1 a (acc: state a) key data len =
  assert (size_block a <= 128);
  assert_norm (pow2 61 <= pow2 125);
  assert (pow2 61 <= max_input8 a);
  assert_norm(pow2 32 + 128 <= pow2 61);
  let ll = len % block_len a in
  assert ((v len - v ll) % size_block a = 0);
  assert ((size_block a + v len - v ll) % size_block a = 0);
  let lb = len - ll in
  let blocks = sub data 0ul lb in
  let last = offset data lb in
  Hash.init #(Ghost.hide a) acc;
  let h0 = ST.get() in //assume(bounded_counter acc h0 1);
  assert (repr acc h0 == acc0 #a);
  Hash.update
    #(Ghost.hide a)
    acc key;
  let h1 = ST.get() in
  assert(
    let k = as_seq h0 key in
    FStar.Seq.lemma_eq_intro (Seq.append (Seq.empty #UInt8.t) k) k;
    repr acc h1 == hash0 k);
  Hash.update_multi
    #(Ghost.hide a)
    acc blocks lb;
  let h2 = ST.get() in
  assert_norm(size_block a + v len < max_input8 a);
  assert (repr acc h2 == hash0 S.(as_seq h0 key @| as_seq h0 blocks));
  Hash.update_last
    #(Ghost.hide a)
    acc last (Int.Cast.Full.uint32_to_uint64 (block_len a + len));
  let h3 = ST.get() in
  assert (v (Int.Cast.Full.uint32_to_uint64 (block_len a + len)) =
    size_block a + v len);
  assert (v (Int.Cast.Full.uint32_to_uint64 (block_len a + len)) = v (block_len a + len));
  assert (S.equal (as_seq h0 last) (as_seq h2 last));
  assert (repr acc h3 ==
    compress_many (hash0 (S.append (as_seq h0 key) (as_seq h0 blocks)))
      (S.append (as_seq h0 last) (Spec.Hash.Common.pad a (v (block_len a + len)))));
  // assert(LowStar.Buffer.live h3 key);
  let tag = sub key 0ul (tag_len a) in (* Salvage memory *)
  Hash.finish #(Ghost.hide a) acc tag;
  let h4 = ST.get() in
  (
    modifies_trans (footprint acc h0) h0 h3 (loc_buffer key) h4; // should this implicitly trigger?
    let p = size_block a in
    let key1 = as_seq h1 key in
    let blocks1 = as_seq h1 blocks in
    let acc1 = repr acc h1 in
    //lemma_compress (acc0 #a) key1;
    assert(acc1 == hash0 key1);
    let v2 = S.(key1 @| blocks1) in
    let acc2 = repr acc h2 in
    // assert (Seq.length key1 % p = 0);
    // assert (Seq.length blocks1 % p = 0);
    // assert (Seq.length v2 % p = 0);
    // lemma_hash2 (acc0 #a) key1 blocks1;
    assert(acc2 == hash0 #a v2);
    let data1 = as_seq h1 data in
    let last1 = as_seq h1 last in
    let suffix1 = Spec.Hash.Common.pad a (p + v len) in
    Seq.lemma_eq_intro data1 S.(blocks1 @| last1);
    let acc3 = repr acc h3 in
    let ls = Seq.length suffix1 in
    assert((p + v len + ls) % p = 0);
    Math.Lemmas.lemma_mod_plus (v ll + ls) (1 + v len / p) p;
    assert((v ll + ls) % p = 0);
    //lemma_hash2 (acc0 #a) v2 S.(last1 @| suffix1);
    assert(acc3 == hash0 #a S.(v2 @| (last1 @| suffix1)));
    Seq.append_assoc v2 last1 suffix1;
    Seq.append_assoc key1 blocks1 last1;
    assert(acc3 == hash0 #a S.((key1 @| data1) @| suffix1));
    assert(extract acc3 == spec a S.(key1 @| data1)))

// the two parts have the same stucture; let's keep their proofs in sync.
inline_for_extraction
val part2:
  a: alg -> 
  acc: state a ->
  mac: uint8_pl (size_hash a) ->
  opad: uint8_pl (size_block a) ->
  tag: uint8_pl (size_hash a) ->
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
        Seq.length payload < max_input8 a /\
        as_seq h1 mac = spec a payload))

#set-options "--z3rlimit 200"
inline_for_extraction
let part2 a acc mac opad tag =
  let totLen = block_len a + tag_len a in
  assert (size_block a <= 128);
  assert_norm (pow2 61 <= pow2 125);
  assert (pow2 61 <= max_input8 a);
  assert_norm(pow2 32 + 128 <= pow2 61);
  assert(v totLen < max_input8 a);
  let h0 = ST.get() in
  //assume(LowStar.Modifies.(loc_disjoint (footprint acc h0) (loc_buffer opad)));
  Hash.init #(Ghost.hide a) acc;
  Hash.update #(Ghost.hide a) acc opad;
  let h1 = ST.get() in
  // assert(
  //   footprint acc h1 == footprint acc h0 /\
  //   LowStar.Buffer.live h1 mac /\
  //   LowStar.Modifies.(loc_disjoint (footprint acc h1) (loc_buffer mac)) );
  assert(
    let k = as_seq h0 opad in
    FStar.Seq.lemma_eq_intro (Seq.append (Seq.empty #UInt8.t) k) k;
    repr acc h1 == hash0 k);
  Hash.update_last #(Ghost.hide a) acc tag (Int.Cast.Full.uint32_to_uint64 totLen);
  let h2 = ST.get() in
  // assert(
  //   LowStar.Buffer.live h2 mac /\
  //   LowStar.Modifies.(loc_disjoint (footprint acc h2) (loc_buffer mac)) );
  Hash.finish #(Ghost.hide a) acc mac;
  (
    let v1 = as_seq h1 opad in
    let acc1 = repr acc h1 in
    //lemma_compress (acc0 #a) v1;
    assert(acc1 == hash0 v1);
    let tag1 = as_seq h1 tag in
    let suffix1 = Spec.Hash.Common.pad a (size_block a + size_hash a) in
    let acc2 = repr acc h2 in
    //lemma_hash2 (acc0 #a) v1 S.(tag1 @| suffix1);
    Seq.append_assoc v1 tag1 suffix1;
    assert(acc2 == hash0 S.((v1 @| tag1) @| suffix1));
    assert(extract acc2 = spec a S.(v1 @| tag1)))

// similar spec as hmac with keylen = block_len a
inline_for_extraction
val hmac_core:
  a: alg -> 
  acc: state a ->
  tag: uint8_pl (size_hash a) ->
  key: uint8_pl (size_block a) {disjoint key tag} ->
  data: uint8_p{
    length data + size_block a < pow2 32 /\ (*required for 32-bit allocation*)
    // length data + size_block a <= max_input8 a /\ (*always true*)
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
      length data + size_block a < max_input8 a /\ ( (*always true*)
      let v1 = spec a S.(k1 @| as_seq h0 data) in
      Seq.length S.(k2 @| v1) < max_input8 a /\
      as_seq h1 tag == spec a S.(k2 @| v1))))

inline_for_extraction
val xor_bytes_inplace:
  a: uint8_p ->
  b: uint8_p ->
  len: UInt32.t {v len = length a /\ v len = length b} ->
  Stack unit
  (requires fun h0 -> disjoint a b /\ live h0 a /\ live h0 b)
  (ensures fun h0 _ h1 ->
    modifies (loc_buffer a) h0 h1 /\
    as_seq h1 a == Spec.Loops.seq_map2 xor8 (as_seq h0 a) (as_seq h0 b))
inline_for_extraction
let xor_bytes_inplace a b len =
  C.Loops.in_place_map2 a b len xor8

// TODO small improvements: part1 and part2 could return their tags in
// mac, so that we can reuse the pad.


inline_for_extraction
let hmac_core a acc tag key data len =
  let h00 = ST.get() in
  push_frame ();
  let h01 = ST.get() in
  fresh_frame_modifies h00 h01; //18-08-02 a trigger would be nice!
  Hash.frame_invariant loc_none acc h00 h01;
  // assert(invariant acc h01);
  let ipad = alloca 0x36uy (block_len a) in
  let h02 = ST.get() in
  //  assert (loc_in (footprint acc h01) h01);
  // TR: now works thanks to Hash.invariant_loc_in_footprint
  fresh_is_disjoint (loc_buffer ipad) (footprint acc h01)  h01 h02;
  let l = block_len a in
  let opad = alloca 0x5cuy l in
  xor_bytes_inplace ipad key l;
  xor_bytes_inplace opad key l;
  let h0 = ST.get() in
  modifies_address_liveness_insensitive_unused_in h01 h0;
  // assert(loc_in (footprint acc h0) h0);
  // TR: now works thanks to
  // modifies_address_liveness_insensitive_unused_in: if no
  // deallocations are performed, then all livenesses are preserved.
  frame_invariant (loc_union (loc_buffer ipad) (loc_buffer opad)) acc h01 h0;
  part1 a acc ipad data len;
  let h1 = ST.get() in
  let inner = sub ipad 0ul (tag_len a) in (* salvage memory *)
  part2 a acc tag opad inner;
  let h2 = ST.get() in
  pop_frame ();
  (
    let h3 = ST.get() in
    let k = as_seq h0 key in
    let k1: lbytes (size_block a) = xor 0x36uy k in
    let k2: lbytes (size_block a) = xor 0x5cuy k in
    let vdata = as_seq h0 data in
    let v1: lbytes (size_hash a) = as_seq h1 inner in
    assert_norm(size_block a + size_hash a <= max_input8 a);
    assert(Seq.length S.(k2 @| v1) < max_input8 a);
    let v2 = as_seq h2 tag in
    xor_lemma 0x36uy k;
    xor_lemma 0x5cuy k;
    // assert(k1 == as_seq h0 ipad);
    // assert(k2 == as_seq h1 opad);
    assert(Seq.equal v1 (spec a S.(k1 @| vdata)));
    assert(Seq.equal v2 (spec a S.(k2 @| v1)));

    // TR: modifies clause now automatically proven thanks to
    // pattern provided in Hash.loc_includes_union_l_footprint

    // 18-08-02 missing lemma? data and tag have the same base type.
    // assume(as_addr data = as_addr tag /\ live h2 tag ==> live h2 data);
    // TR: We don't need this lemma. In fact, here is a generic way
    // of proving that liveness of buffers is preserved: any
    // modified location that does not necessarily have its liveness
    // preserved (e.g. an abstract footprint) shall be disjoint from
    // any location whose liveness we want to preserve.
    assert (modifies (loc_union (footprint acc h00) (loc_buffer tag)) h00 h3);
    modifies_liveness_insensitive_buffer (footprint acc h00) (loc_buffer tag) h00 h3 tag;
    modifies_liveness_insensitive_buffer (footprint acc h00) (loc_buffer tag) h00 h3 key;
    modifies_liveness_insensitive_buffer (footprint acc h00) (loc_buffer tag) h00 h3 data;
    //modifies_liveness_insensitive_buffer (footprint acc h00) (loc_buffer tag) h00 h3 tag;
    //
    //
    //admit ();
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
  assert (size_block a <= 128);
  assert_norm (pow2 32 + 128 < pow2 61);
  assert_norm (pow2 61 < pow2 125);
  assert(pow2 32 + size_block a < max_input8 a);
  assert(length data + size_block a <= max_input8 a);
  let keyblock = alloca 0x00uy (block_len a) in
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
  assert_norm(pow2 32 <= max_input8 a);
  let keyblock = Buffer.create 0x00uy (block_len a) in
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
  let keyblock = Buffer.create 0x00uy (block_len a) in
  assert_norm(pow2 32 <= max_input8 a);
  wrap_key a keyblock key keylen;
  let acc =
    match a with
    | SHA256 -> Buffer.rcreate HyperStack.root 0ul (state_size a)
    | SHA384 -> Buffer.rcreate HyperStack.root 0UL (state_size a)
    | SHA512 -> Buffer.rcreate HyperStack.root 0UL (state_size a) in
  hmac_core SHA256 acc mac keyblock data datalen;
  pop_frame ()
*)
