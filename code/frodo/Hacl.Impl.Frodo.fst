module Hacl.Impl.Frodo

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.RawIntTypes
open Lib.PQ.Buffer
open FStar.Mul

open Hacl.Impl.PQ.Lib
open Hacl.Keccak
open Hacl.Impl.Frodo.Params

open LowStar.ModifiesPat
open LowStar.Modifies

module Buf = LowStar.Buffer
module ST = FStar.HyperStack.ST
module FLemmas = Spec.Frodo.Lemmas

let cshake_frodo = cshake128_frodo

val eq_u8: a:uint8 -> b:uint8 -> Tot bool
[@ "substitute"]
let eq_u8 a b = FStar.UInt8.(u8_to_UInt8 a =^ u8_to_UInt8 b)

val eq_u32_m:m:uint32 -> a:uint32 -> b:uint32 -> Tot bool
[@ "substitute"]
let eq_u32_m m a b = FStar.UInt32.(u32_to_UInt32 (a &. m) =^ u32_to_UInt32 (b &. m))

val matrix_eq:
  #n1:size_t -> #n2:size_t{v n1 * v n2 < max_size_t} ->
  m:size_t{0 < v m /\ v m <= 16} ->
  a:matrix_t n1 n2 -> b:matrix_t n1 n2 -> Stack bool
  (requires (fun h -> Buf.live h a /\ Buf.live h b))
  (ensures (fun h0 r h1 -> modifies loc_none h0 h1))
  [@"c_inline"]
let matrix_eq #n1 #n2 m a b =
  push_frame();
  let m = (u32 1 <<. size_to_uint32 m) -. u32 1 in
  let res:lbuffer bool 1 = create (size 1) (true) in
  let h0 = ST.get () in
  loop_nospec #h0 n1 res
  (fun i ->
    let h1 = ST.get () in
    loop_nospec #h1 n2 res
    (fun j ->
      let a1 = res.(size 0) in
      let a2 = eq_u32_m m (to_u32 (mget a i j)) (to_u32 (mget b i j)) in
      res.(size 0) <- a1 && a2
    )
  );
  let res = res.(size 0) in
  pop_frame();
  res

val lbytes_eq:
  #len:size_t -> a:lbytes len -> b:lbytes len -> Stack bool
  (requires (fun h -> Buf.live h a /\ Buf.live h b))
  (ensures (fun h0 r h1 -> modifies loc_none h0 h1))
  [@"c_inline"]
let lbytes_eq #len a b =
  push_frame();
  let res:lbuffer bool 1 = create (size 1) (true) in
  let h0 = ST.get () in
  loop_nospec #h0 len res
  (fun i ->
    let a1 = res.(size 0) in
    let a2 = eq_u8 a.(i) b.(i) in
    res.(size 0) <- a1 && a2
  );
  let res = res.(size 0) in
  pop_frame();
  res

let bytes_mu =  normalize_term ((params_extracted_bits *! params_nbar *! params_nbar) /. size 8)
let crypto_publickeybytes = normalize_term (bytes_seed_a +! (params_logq *! params_n *! params_nbar) /. size 8)
let crypto_secretkeybytes =
  assert_norm (v crypto_bytes + v crypto_publickeybytes + 2 * v params_n * v params_nbar < max_size_t);
  normalize_term (crypto_bytes +! crypto_publickeybytes +! size 2 *! params_n *! params_nbar)
let crypto_ciphertextbytes = normalize_term (((params_nbar *! params_n +! params_nbar *! params_nbar) *! params_logq) /. size 8 +! crypto_bytes)

#reset-options "--z3rlimit 50 --max_fuel 0"
val ec:
  b:size_t{v b < v params_logq} -> k:uint16 -> Tot uint16
  [@ "substitute"]
let ec b a =
  shift_left #U16 a (size_to_uint32 (params_logq -. b))

val dc:
  b:size_t{v b < v params_logq} -> c:uint16 -> Tot uint16
  [@ "substitute"]
let dc b c =
  let res1 = (c +. (u16 1 <<. size_to_uint32 (params_logq -. b -. size 1))) >>. size_to_uint32 (params_logq -. b) in
  res1 &. ((u16 1 <<. size_to_uint32 b) -. u16 1)

val frodo_key_encode:
  b:size_t{v b <= 8} ->
  a:lbytes ((params_nbar *! params_nbar *! b) /. size 8) ->
  res:matrix_t params_nbar params_nbar -> Stack unit
  (requires (fun h -> Buf.live h a /\ Buf.live h res /\ Buf.disjoint a res))
  (ensures (fun h0 _ h1 -> Buf.live h1 res /\ modifies (loc_buffer res) h0 h1))
  [@"c_inline"]
let frodo_key_encode b a res =
  push_frame();
  let n2 = params_nbar /. size 8 in
  let aLen = (params_nbar *! params_nbar *! b) /. size 8 in
  let v8 = create (size 8) (u8 0) in
  let h0 = ST.get () in
  let inv (h1:mem) (j:nat{j <= v params_nbar}) =
    Buf.live h1 res /\ Buf.live h1 v8 /\ modifies (loc_union (loc_buffer res) (loc_buffer v8)) h0 h1 in
  let f' (i:size_t{0 <= v i /\ v i < v params_nbar}): Stack unit
      (requires (fun h -> inv h (v i)))
      (ensures (fun _ _ h2 -> inv h2 (v i + 1))) =
      let h0 = ST.get () in
      let inv1 (h1:mem) (j:nat{j <= v n2}) =
        Buf.live h1 res /\ Buf.live h1 v8 /\ modifies (loc_union (loc_buffer res) (loc_buffer v8)) h0 h1 in
      let f1 (j:size_t{0 <= v j /\ v j < v n2}): Stack unit
        (requires (fun h -> inv1 h (v j)))
        (ensures (fun _ _ h2 -> inv1 h2 (v j + 1))) =
          copy (sub v8 (size 0) b) b (sub #uint8 #(v aLen) #(v b) a ((i +! j) *! b) b);
          let vij = uint_from_bytes_le #U64 v8 in
          let h1 = ST.get () in
          loop_nospec #h1 (size 8) res
          (fun k ->
            let ak = (vij >>. size_to_uint32 (b *! k)) &. ((u64 1 <<. size_to_uint32 b) -. u64 1) in
            let resij = ec b (to_u16 ak) in
            mset res i (size 8 *! j +! k) resij
          ) in

      Lib.Loops.for (size 0) n2 inv1 f1 in
  Lib.Loops.for (size 0) params_nbar inv f';
  pop_frame()

val frodo_key_decode:
  b:size_t{v b <= 8} ->
  a:matrix_t params_nbar params_nbar ->
  res:lbytes ((params_nbar *! params_nbar *! b) /. size 8) -> Stack unit
  (requires (fun h -> Buf.live h a /\ Buf.live h res /\ Buf.disjoint a res))
  (ensures (fun h0 r h1 -> Buf.live h1 res /\ modifies (loc_buffer res) h0 h1))
  [@"c_inline"]
let frodo_key_decode b a res =
  push_frame();
  let n2 = params_nbar /. size 8 in
  let resLen = (params_nbar *! params_nbar *! b) /. size 8 in
  let v8 = create (size 8) (u8 0) in
  let templong:lbuffer uint64 1 = create (size 1) (u64 0) in
  let h0 = ST.get () in
  let inv (h1:mem) (j:nat{j <= v params_nbar}) =
    Buf.live h1 res /\ Buf.live h1 v8 /\ Buf.live h1 templong /\
    modifies (loc_union (loc_buffer res) (loc_union (loc_buffer v8) (loc_buffer templong))) h0 h1 in
  let f' (i:size_t{0 <= v i /\ v i < v params_nbar}): Stack unit
      (requires (fun h -> inv h (v i)))
      (ensures (fun _ _ h2 -> inv h2 (v i + 1))) =
      let h0 = ST.get () in
      let inv1 (h1:mem) (j:nat{j <= v n2}) =
        Buf.live h1 res /\ Buf.live h1 v8 /\ Buf.live h1 templong /\
        modifies (loc_union (loc_buffer res) (loc_union (loc_buffer v8) (loc_buffer templong))) h0 h1 in
      let f1 (j:size_t{0 <= v j /\ v j < v n2}): Stack unit
        (requires (fun h -> inv1 h (v j)))
        (ensures (fun _ _ h2 -> inv1 h2 (v j + 1))) =
          templong.(size 0) <- u64 0;
          let h1 = ST.get () in
          loop_nospec #h1 (size 8) templong
          (fun k ->
            let aij = dc b (mget a i (size 8 *! j +! k)) in
            templong.(size 0) <- templong.(size 0) |. (to_u64 aij <<. size_to_uint32 (b *! k))
          );
          uint_to_bytes_le #U64 v8 (templong.(size 0));
          copy (sub res ((i +! j) *! b) b) b (sub #uint8 #8 #(v b) v8 (size 0) b) in

      Lib.Loops.for (size 0) n2 inv1 f1 in
  Lib.Loops.for (size 0) params_nbar inv f';
  pop_frame()

val frodo_pack:
  n1:size_t -> n2:size_t{v n1 * v n2 < max_size_t /\ v n2 % 8 = 0} ->
  a:matrix_t n1 n2 ->
  d:size_t{v d * v n1 < max_size_t /\ v d * v n1 * v n2 < max_size_t /\ v d <= 16} ->
  res:lbytes (d *! n1 *! n2 /. size 8) -> Stack unit
  (requires (fun h -> Buf.live h a /\ Buf.live h res /\ Buf.disjoint a res))
  (ensures (fun h0 r h1 -> Buf.live h1 res /\ modifies (loc_buffer res) h0 h1))
  [@"c_inline"]
let frodo_pack n1 n2 a d res =
  push_frame();
  let maskd = (u32 1 <<. size_to_uint32 d) -. u32 1 in
  let templong:lbuffer uint128 1 = create (size 1) (to_u128 (u64 0)) in
  let v16 = create (size 16) (u8 0) in
  let n28 = n2 /. size 8 in
  let resLen = d *! n1 *! n2 /. size 8 in

  let h0 = ST.get () in
  let inv (h1:mem) (j:nat{j <= v n1}) =
    Buf.live h1 res /\ Buf.live h1 v16 /\ Buf.live h1 templong /\
    modifies (loc_union (loc_buffer res) (loc_union (loc_buffer v16) (loc_buffer templong))) h0 h1 in
  let f' (i:size_t{0 <= v i /\ v i < v n1}): Stack unit
      (requires (fun h -> inv h (v i)))
      (ensures (fun _ _ h2 -> inv h2 (v i + 1))) =
      let h0 = ST.get () in
      let inv1 (h1:mem) (j:nat{j <= v n28}) =
        Buf.live h1 res /\ Buf.live h1 v16 /\ Buf.live h1 templong /\
        modifies (loc_union (loc_buffer res) (loc_union (loc_buffer v16) (loc_buffer templong))) h0 h1 in
      let f1 (j:size_t{0 <= v j /\ v j < v n28}): Stack unit
        (requires (fun h -> inv1 h (v j)))
        (ensures (fun _ _ h2 -> inv1 h2 (v j + 1))) =
          templong.(size 0) <- to_u128 (u64 0);
          let h1 = ST.get () in
          loop_nospec #h1 (size 8) templong
          (fun k ->
            assert (8 * v j + v k < v n2);
            let aij = to_u32 (mget a i (size 8 *! j +! k)) &. maskd in
            templong.(size 0) <- templong.(size 0) |. (to_u128 aij <<. size_to_uint32 (size 7 *! d -! d *! k))
          );
          uint_to_bytes_be #U128 v16 (templong.(size 0));
	  FLemmas.lemma_matrix_index_repeati (v n1) (v n2) (v d) (v i) (v j);
	  assert (((v i * v n2 / 8 + v j) * v d) + v d <= v resLen);
          copy (sub res ((i *! n2 /. size 8 +! j) *! d) d) d (sub #uint8 #16 #(v d) v16 (size 16 -! d) d) in

      Lib.Loops.for (size 0) n28 inv1 f1 in
  Lib.Loops.for (size 0) n1 inv f';
  pop_frame()

val frodo_unpack:
  n1:size_t -> n2:size_t{v n1 * v n2 < max_size_t /\ v n2 % 8 = 0} ->
  d:size_t{v d * v n1 < max_size_t /\ v d * v n1 * v n2 < max_size_t /\ v d <= 16} ->
  b:lbytes (d *! n1 *! n2 /. size 8) ->
  res:matrix_t n1 n2 -> Stack unit
  (requires (fun h -> Buf.live h b /\ Buf.live h res /\ Buf.disjoint b res))
  (ensures (fun h0 r h1 -> Buf.live h1 res /\ modifies (loc_buffer res) h0 h1))
  [@"c_inline"]
let frodo_unpack n1 n2 d b res =
  push_frame();
  let maskd = (u32 1 <<. size_to_uint32 d) -. u32 1 in
  let v16:lbytes (size 16) = create (size 16) (u8 0) in
  let n28 = n2 /. size 8 in
  let bLen = d *! n1 *! n2 /. size 8 in

  let h0 = ST.get () in
  let inv (h1:mem) (j:nat{j <= v n1}) =
    Buf.live h1 res /\ Buf.live h1 v16 /\ modifies (loc_union (loc_buffer res) (loc_buffer v16)) h0 h1 in
  let f' (i:size_t{0 <= v i /\ v i < v n1}): Stack unit
      (requires (fun h -> inv h (v i)))
      (ensures (fun _ _ h2 -> inv h2 (v i + 1))) =
      let h0 = ST.get () in
      let inv1 (h1:mem) (j:nat{j <= v n28}) =
        Buf.live h1 res /\ Buf.live h1 v16 /\ modifies (loc_union (loc_buffer res) (loc_buffer v16)) h0 h1 in
      let f1 (j:size_t{0 <= v j /\ v j < v n28}): Stack unit
        (requires (fun h -> inv1 h (v j)))
        (ensures (fun _ _ h2 -> inv1 h2 (v j + 1))) =
          assert (v i * v n2 < v n1 * v n2);
          FLemmas.lemma_matrix_index_repeati (v n1) (v n2) (v d) (v i) (v j);
          assert (v ((i *! n2 /. size 8 +! j) *! d) + v d <= v bLen);
          let bij = sub #_ #(v bLen) #(v d) b ((i *! n2 /. size 8 +! j) *! d) d in
          copy (sub #_ #_ #(v d) v16 (size 16 -! d) d) d bij;
          let templong = uint_from_bytes_be #U128 v16 in
          let h1 = ST.get () in
          loop_nospec #h1 (size 8) res
          (fun k ->
            let resij = to_u32 (templong >>. size_to_uint32 (size 7 *! d -! d *! k)) &. maskd in
            assert (8 * v j + v k < v n2);
            mset res i (size 8 *! j +! k) (to_u16 resij)
          ) in

      Lib.Loops.for (size 0) n28 inv1 f1 in
  Lib.Loops.for (size 0) n1 inv f';
  pop_frame()

val frodo_sample: r:uint16 -> Stack uint16
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> modifies loc_none h0 h1))
  [@"c_inline"]
let frodo_sample r =
  push_frame();
  let prnd = r >>. u32 1 in
  let sign = r &. u16 1 in
  let sample:lbuffer uint16 1 = create (size 1) (u16 0) in
  let ctr = cdf_table_len -! size 1 in

  let h0 = ST.get () in
  loop_nospec #h0 ctr sample
  (fun j ->
    recall cdf_table;
    let tj = cdf_table.(j) in
    let sample0 = sample.(size 0) in
    sample.(size 0) <- sample0 +. (to_u16 (to_u32 (tj -. prnd)) >>. u32 15)
  );
  let s0 = sample.(size 0) in
  let res = ((lognot sign +. u16 1) ^. s0) +. sign in
  pop_frame();
  res

val frodo_sample_matrix:
  n1:size_t -> n2:size_t{0 < 2 * v n1 * v n2 /\ 2 * v n1 * v n2 < max_size_t} ->
  seed_len:size_t{v seed_len > 0} -> seed:lbytes seed_len -> ctr:uint16 ->
  res:matrix_t n1 n2 -> Stack unit
  (requires (fun h -> Buf.live h seed /\ Buf.live h res /\ Buf.disjoint seed res))
  (ensures (fun h0 r h1 -> Buf.live h1 res /\ modifies (loc_buffer res) h0 h1))
  [@"c_inline"]
let frodo_sample_matrix n1 n2 seed_len seed ctr res =
  push_frame();
  let r = create (size 2 *! n1 *! n2) (u8 0) in
  cshake_frodo seed_len seed ctr (size 2 *! n1 *! n2) r;
  let h0 = ST.get () in
  loop_nospec #h0 n1 res
  (fun i ->
    let h0 = ST.get () in
    loop_nospec #h0 n2 res
    (fun j ->
      FLemmas.lemma_matrix_index_repeati1 (v n1) (v n2) (v i) (v j);
      let resij = sub r (size 2 *! (n2 *! i +! j)) (size 2) in
      mset res i j (frodo_sample (uint_from_bytes_le #U16 resij))
    )
  );
  pop_frame()

val frodo_sample_matrix_tr:
  n1:size_t -> n2:size_t{0 < 2 * v n1 * v n2 /\ 2 * v n1 * v n2 < max_size_t} ->
  seed_len:size_t{v seed_len > 0} -> seed:lbytes seed_len -> ctr:uint16 ->
  res:matrix_t n1 n2 -> Stack unit
  (requires (fun h -> Buf.live h seed /\ Buf.live h res /\ Buf.disjoint seed res))
  (ensures (fun h0 r h1 -> Buf.live h1 res /\ modifies (loc_buffer res) h0 h1))
  [@"c_inline"]
let frodo_sample_matrix_tr n1 n2 seed_len seed ctr res =
  push_frame();
  let r = create (size 2 *! n1 *! n2) (u8 0) in
  cshake_frodo seed_len seed ctr (size 2 *! n1 *! n2) r;
  let h0 = ST.get () in
  loop_nospec #h0 n1 res
  (fun i ->
    let h0 = ST.get () in
    loop_nospec #h0 n2 res
    (fun j ->
      FLemmas.lemma_matrix_index_repeati2 (v n1) (v n2) (v i) (v j);
      let resij = sub r (size 2 *! (n1 *! j +! i)) (size 2) in
      mset res i j (frodo_sample (uint_from_bytes_le #U16 resij))
    )
  );
  pop_frame()

val frodo_gen_matrix_cshake:
  n:size_t{0 < 2 * v n /\ 2 * v n < max_size_t /\ v n * v n < max_size_t} ->
  seed_len:size_t{v seed_len > 0} -> seed:lbytes seed_len ->
  res:matrix_t n n -> Stack unit
  (requires (fun h -> Buf.live h seed /\ Buf.live h res /\ Buf.disjoint seed res))
  (ensures (fun h0 r h1 -> Buf.live h1 res /\ modifies (loc_buffer res) h0 h1))
  [@"c_inline"]
let frodo_gen_matrix_cshake n seed_len seed res =
  push_frame();
  let r:lbytes (size 2 *! n) = create (size 2 *! n) (u8 0) in
  let h0 = ST.get () in
  let inv (h1:mem) (j:nat{j <= v n}) =
    Buf.live h1 res /\ Buf.live h1 r /\ modifies (loc_union (loc_buffer res) (loc_buffer r)) h0 h1 in
  let f' (i:size_t{0 <= v i /\ v i < v n}): Stack unit
    (requires (fun h -> inv h (v i)))
    (ensures (fun _ _ h2 -> inv h2 (v i + 1))) =
      let ctr = size_to_uint32 (size 256 +. i) in
      cshake128_frodo seed_len seed (to_u16 ctr) (size 2 *! n) r;
      let h0 = ST.get () in
      loop_nospec #h0 n res
      (fun j ->
        let resij = sub r (size 2 *! j) (size 2) in
        mset res i j (uint_from_bytes_le #U16 resij)
      ) in
  Lib.Loops.for (size 0) n inv f';
  pop_frame()

let frodo_gen_matrix = frodo_gen_matrix_cshake

val matrix_to_lbytes:
  #n1:size_t -> #n2:size_t{2 * v n1 < max_size_t /\ 2 * v n1 * v n2 < max_size_t} ->
  m:matrix_t n1 n2 -> res:lbytes (size 2 *! n1 *! n2) -> Stack unit
  (requires (fun h -> Buf.live h m /\ Buf.live h res /\ Buf.disjoint m res))
  (ensures (fun h0 r h1 -> Buf.live h1 res /\ modifies (loc_buffer res) h0 h1))
  [@"c_inline"]
let matrix_to_lbytes #n1 #n2 m res =
  let h0 = ST.get () in
  loop_nospec #h0 n1 res
  (fun i ->
    let h0 = ST.get () in
    loop_nospec #h0 n2 res
    (fun j ->
      FLemmas.lemma_matrix_index_repeati2 (v n1) (v n2) (v i) (v j);
      assert (2 * (v j * v n1 + v i) + 2 <= 2 * v n1 * v n2);
      uint_to_bytes_le (sub res (size 2 *! (j *! n1 +! i)) (size 2)) (mget m i j)
    )
  )

val matrix_from_lbytes:
  #n1:size_t -> #n2:size_t{2 * v n1 < max_size_t /\ 2 * v n1 * v n2 < max_size_t} ->
  b:lbytes (size 2 *! n1 *! n2) ->
  res:matrix_t n1 n2 -> Stack unit
  (requires (fun h -> Buf.live h b /\ Buf.live h res /\ Buf.disjoint b res))
  (ensures (fun h0 r h1 -> Buf.live h1 res /\ modifies (loc_buffer res) h0 h1))
  [@"c_inline"]
let matrix_from_lbytes #n1 #n2 b res =
  let h0 = ST.get () in
  loop_nospec #h0 n1 res
  (fun i ->
    let h0 = ST.get () in
    loop_nospec #h0 n2 res
    (fun j ->
      FLemmas.lemma_matrix_index_repeati2 (v n1) (v n2) (v i) (v j);
      assert (2 * (v j * v n1 + v i) + 2 <= 2 * v n1 * v n2);
      mset res i j (uint_from_bytes_le #U16 (sub b (size 2 *! (j *! n1 +! i)) (size 2)))
    )
  )

assume val randombytes_init_:
  entropy_input:lbytes (size 48) -> Stack unit
  (requires (fun h -> Buf.live h entropy_input))
  (ensures (fun h0 r h1 -> Buf.live h1 entropy_input))

assume val randombytes_:
  len:size_t -> res:lbytes len -> Stack unit
  (requires (fun h -> Buf.live h res))
  (ensures (fun h0 r h1 -> Buf.live h1 res /\ modifies (loc_buffer res) h0 h1))

val frodo_mul_add_as_plus_e:
  seed_a:lbytes bytes_seed_a ->
  s_matrix:matrix_t params_n params_nbar ->
  e_matrix:matrix_t params_n params_nbar ->
  b_matrix:matrix_t params_n params_nbar ->  Stack unit
  (requires (fun h -> Buf.live h seed_a /\ Buf.live h s_matrix /\
    Buf.live h e_matrix /\ Buf.live h b_matrix /\ Buf.disjoint b_matrix seed_a /\
    Buf.disjoint s_matrix b_matrix /\ Buf.disjoint b_matrix e_matrix))
  (ensures (fun h0 r h1 -> Buf.live h1 b_matrix /\ modifies (loc_buffer b_matrix) h0 h1))
  #reset-options "--z3rlimit 150 --max_fuel 0"
  [@"c_inline"]
let frodo_mul_add_as_plus_e seed_a s_matrix e_matrix b_matrix =
  push_frame();
  let a_matrix = matrix_create params_n params_n in
  frodo_gen_matrix params_n bytes_seed_a seed_a a_matrix;
  matrix_mul a_matrix s_matrix b_matrix;
  matrix_add b_matrix e_matrix;
  pop_frame()

val frodo_mul_add_as_plus_e_pack:
  seed_a:lbytes bytes_seed_a ->
  seed_e:lbytes crypto_bytes ->
  b:lbytes (params_logq *! params_n *! params_nbar /. size 8) ->
  s:lbytes (size 2 *! params_n *! params_nbar) -> Stack unit
  (requires (fun h -> Buf.live h seed_a /\ Buf.live h seed_e /\
    Buf.live h s /\ Buf.live h b /\ Buf.disjoint b s /\
    Buf.disjoint seed_a b /\ Buf.disjoint seed_e b /\
    Buf.disjoint seed_a s /\ Buf.disjoint seed_e s))
  (ensures (fun h0 r h1 -> Buf.live h1 s /\ Buf.live h1 b /\
    modifies (loc_union (loc_buffer b) (loc_buffer s)) h0 h1))
  #reset-options "--z3rlimit 150 --max_fuel 0"
  [@"c_inline"]
let frodo_mul_add_as_plus_e_pack seed_a seed_e b s =
  push_frame();
  let b_matrix = matrix_create params_n params_nbar in
  let s_matrix = matrix_create params_n params_nbar in
  let e_matrix = matrix_create params_n params_nbar in
  frodo_sample_matrix_tr params_n params_nbar crypto_bytes seed_e (u16 1) s_matrix;
  frodo_sample_matrix params_n params_nbar crypto_bytes seed_e (u16 2) e_matrix;
  frodo_mul_add_as_plus_e seed_a s_matrix e_matrix b_matrix;
  frodo_pack params_n params_nbar b_matrix params_logq b;
  matrix_to_lbytes s_matrix s;
  pop_frame()

val crypto_kem_keypair:
  pk:lbytes crypto_publickeybytes ->
  sk:lbytes crypto_secretkeybytes -> Stack uint32
  (requires (fun h -> Buf.live h pk /\ Buf.live h sk /\ Buf.disjoint pk sk))
  (ensures (fun h0 r h1 -> Buf.live h1 pk /\ Buf.live h1 sk /\
    modifies (loc_union (loc_buffer pk) (loc_buffer sk)) h0 h1))
let crypto_kem_keypair pk sk =
  push_frame();
  let coins = create (size 2 *! crypto_bytes +! bytes_seed_a) (u8 0) in
  randombytes_ (size 2 *! crypto_bytes +! bytes_seed_a) coins;
  let s:lbytes crypto_bytes = sub coins (size 0) crypto_bytes in
  let seed_e = sub coins crypto_bytes crypto_bytes in
  let z = sub coins (size 2 *! crypto_bytes) bytes_seed_a in

  assert_norm (v crypto_publickeybytes = v bytes_seed_a + (v params_logq * v params_n * v params_nbar) / 8);
  let seed_a = sub pk (size 0) bytes_seed_a in
  cshake_frodo bytes_seed_a z (u16 0) bytes_seed_a seed_a;

  let b:lbytes (params_logq *! params_n *! params_nbar /. size 8) = sub pk bytes_seed_a (crypto_publickeybytes -! bytes_seed_a) in
  assert_norm (v crypto_secretkeybytes = v crypto_bytes + v crypto_publickeybytes + 2 * v params_n * v params_nbar);
  let s_matrix = sub sk (crypto_bytes +! crypto_publickeybytes) (size 2 *! params_n *! params_nbar) in
  frodo_mul_add_as_plus_e_pack seed_a seed_e b s_matrix;

  copy (sub sk (size 0) crypto_bytes) crypto_bytes s;
  copy (sub sk crypto_bytes crypto_publickeybytes) crypto_publickeybytes pk;
  pop_frame();
  (u32 0)

val frodo_mul_add_sa_plus_e:
  seed_a:lbytes bytes_seed_a ->
  seed_e:lbytes crypto_bytes ->
  sp_matrix:matrix_t params_nbar params_n ->
  bp_matrix:matrix_t params_nbar params_n -> Stack unit
  (requires (fun h -> Buf.live h seed_a /\ Buf.live h seed_e /\
    Buf.live h bp_matrix /\ Buf.live h sp_matrix /\
    Buf.disjoint bp_matrix sp_matrix /\ Buf.disjoint bp_matrix seed_a /\
    Buf.disjoint bp_matrix seed_e))
  (ensures (fun h0 r h1 -> Buf.live h1 bp_matrix /\ modifies (loc_buffer bp_matrix) h0 h1))
  [@"c_inline"]
let frodo_mul_add_sa_plus_e seed_a seed_e sp_matrix bp_matrix =
  push_frame();
  let ep_matrix = matrix_create params_nbar params_n in
  let a_matrix  = matrix_create params_n params_n in

  frodo_gen_matrix params_n bytes_seed_a seed_a a_matrix;
  frodo_sample_matrix params_nbar params_n crypto_bytes seed_e (u16 5) ep_matrix;

  matrix_mul sp_matrix a_matrix bp_matrix;
  matrix_add bp_matrix ep_matrix;
  pop_frame()

val frodo_mul_add_sb_plus_e_plus_mu:
  b:lbytes ((params_logq *! params_n *! params_nbar) /. size 8) ->
  seed_e:lbytes crypto_bytes ->
  coins:lbytes ((params_nbar *! params_nbar *! params_extracted_bits) /. size 8) ->
  sp_matrix:matrix_t params_nbar params_n ->
  v_matrix:matrix_t params_nbar params_nbar -> Stack unit
  (requires (fun h -> Buf.live h b /\ Buf.live h seed_e /\
    Buf.live h coins /\ Buf.live h v_matrix /\ Buf.live h sp_matrix /\
    Buf.disjoint v_matrix b /\ Buf.disjoint v_matrix seed_e /\
    Buf.disjoint v_matrix coins /\ Buf.disjoint v_matrix sp_matrix))
  (ensures (fun h0 r h1 -> Buf.live h1 v_matrix /\ modifies (loc_buffer v_matrix) h0 h1))
  [@"c_inline"]
let frodo_mul_add_sb_plus_e_plus_mu b seed_e coins sp_matrix v_matrix =
  push_frame();
  let epp_matrix = matrix_create params_nbar params_nbar in
  let b_matrix   = matrix_create params_n params_nbar in
  let mu_encode  = matrix_create params_nbar params_nbar in

  frodo_sample_matrix params_nbar params_nbar crypto_bytes seed_e (u16 6) epp_matrix;
  frodo_unpack params_n params_nbar params_logq b b_matrix;
  frodo_key_encode params_extracted_bits coins mu_encode;

  matrix_mul sp_matrix b_matrix v_matrix;
  matrix_add v_matrix epp_matrix;
  matrix_add v_matrix mu_encode;

  pop_frame()

val crypto_kem_enc_ct_pack:
  seed_a:lbytes bytes_seed_a ->
  seed_e:lbytes crypto_bytes ->
  coins:lbytes ((params_nbar *! params_nbar *! params_extracted_bits) /. size 8) ->
  b:lbytes ((params_logq *! params_n *! params_nbar) /. size 8) ->
  sp_matrix:matrix_t params_nbar params_n ->
  ct:lbytes crypto_ciphertextbytes -> Stack unit
  (requires (fun h -> Buf.live h seed_a /\ Buf.live h seed_e /\
    Buf.live h coins /\ Buf.live h b /\ Buf.live h sp_matrix /\
    Buf.live h ct))
  (ensures (fun h0 r h1 -> Buf.live h1 ct /\ modifies (loc_buffer ct) h0 h1))
  [@"c_inline"]
let crypto_kem_enc_ct_pack seed_a seed_e coins b sp_matrix ct =
  push_frame();
  let c1Len = (params_logq *! params_nbar *! params_n) /. size 8 in
  let c2Len = (params_logq *! params_nbar *! params_nbar) /. size 8 in

  let bp_matrix = matrix_create params_nbar params_n in
  frodo_mul_add_sa_plus_e seed_a seed_e sp_matrix bp_matrix;
  assert_norm (v crypto_ciphertextbytes = ((v params_nbar * v params_n + v params_nbar * v params_nbar) * v params_logq) / 8 + v crypto_bytes);
  frodo_pack params_nbar params_n bp_matrix params_logq (sub ct (size 0) c1Len);

  let v_matrix   = matrix_create params_nbar params_nbar in
  frodo_mul_add_sb_plus_e_plus_mu b seed_e coins sp_matrix v_matrix;
  frodo_pack params_nbar params_nbar v_matrix params_logq (sub ct c1Len c2Len);
  pop_frame()

val crypto_kem_enc_ct:
  pk:lbytes crypto_publickeybytes ->
  g:lbytes (size 3 *! crypto_bytes){3 * v crypto_bytes < max_size_t} ->
  coins:lbytes ((params_nbar *! params_nbar *! params_extracted_bits) /. size 8) ->
  ct:lbytes crypto_ciphertextbytes -> Stack unit
  (requires (fun h -> Buf.live h pk /\ Buf.live h g /\
    Buf.live h coins /\ Buf.live h ct /\ Buf.disjoint g ct /\
    Buf.disjoint ct pk /\ Buf.disjoint ct coins))
  (ensures (fun h0 r h1 -> Buf.live h1 ct /\ modifies (loc_buffer ct) h0 h1))
  [@"c_inline"]
let crypto_kem_enc_ct pk g coins ct =
  push_frame();
  assert_norm (v crypto_ciphertextbytes = ((v params_nbar * v params_n + v params_nbar * v params_nbar) * v params_logq) / 8 + v crypto_bytes);
  assert_norm (v crypto_publickeybytes = v bytes_seed_a + (v params_logq * v params_n * v params_nbar) / 8);
  let c1Len = (params_logq *! params_nbar *! params_n) /. size 8 in
  let c2Len = (params_logq *! params_nbar *! params_nbar) /. size 8 in
  let c12Len = c1Len +! c2Len in
  let seed_a = sub #uint8 #_ #(v bytes_seed_a) pk (size 0) bytes_seed_a in
  let seed_e = sub #uint8 #_ #(v crypto_bytes) g (size 0) crypto_bytes in
  let b = sub #uint8 #_ #(v ((params_logq *! params_n *! params_nbar) /. size 8)) pk bytes_seed_a (crypto_publickeybytes -! bytes_seed_a) in
  let sp_matrix = matrix_create params_nbar params_n in
  frodo_sample_matrix params_nbar params_n crypto_bytes seed_e (u16 4) sp_matrix;

  crypto_kem_enc_ct_pack seed_a seed_e coins b sp_matrix ct;
  let d = sub #uint8 #_ #(v crypto_bytes) g (size 2 *! crypto_bytes) crypto_bytes in
  copy (sub ct c12Len crypto_bytes) crypto_bytes d;
  pop_frame()

val crypto_kem_enc_ss:
  g:lbytes (size 3 *! crypto_bytes) ->
  ct:lbytes crypto_ciphertextbytes ->
  ss:lbytes crypto_bytes -> Stack unit
  (requires (fun h -> Buf.live h g /\ Buf.live h ct /\ Buf.live h ss /\
    Buf.disjoint ct ss /\ Buf.disjoint g ct /\ Buf.disjoint g ss))
  (ensures (fun h0 r h1 -> Buf.live h1 ss /\ modifies (loc_buffer ss) h0 h1))
  [@"c_inline"]
let crypto_kem_enc_ss g ct ss =
  push_frame();
  assert_norm (v crypto_ciphertextbytes = ((v params_nbar * v params_n + v params_nbar * v params_nbar) * v params_logq) / 8 + v crypto_bytes);
  let c1Len = (params_logq *! params_nbar *! params_n) /. size 8 in
  let c2Len = (params_logq *! params_nbar *! params_nbar) /. size 8 in
  let c12Len = c1Len +! c2Len in
  let ss_init_len = c12Len +! size 2 *! crypto_bytes in
  let ss_init:lbytes ss_init_len = create ss_init_len (u8 0) in

  let k = sub #uint8 #_ #(v crypto_bytes) g crypto_bytes crypto_bytes in
  let d = sub #uint8 #_ #(v crypto_bytes) g (size 2 *! crypto_bytes) crypto_bytes in

  copy (sub ss_init (size 0) c12Len) c12Len (sub #uint8 #_ #(v c12Len) ct (size 0) c12Len);
  copy (sub ss_init c12Len crypto_bytes) crypto_bytes k;
  copy (sub ss_init (ss_init_len -! crypto_bytes) crypto_bytes) crypto_bytes d;
  cshake_frodo ss_init_len ss_init (u16 7) crypto_bytes ss;
  pop_frame()

val crypto_kem_enc:
  ct:lbytes crypto_ciphertextbytes -> ss:lbytes crypto_bytes ->
  pk:lbytes crypto_publickeybytes -> Stack uint32
  (requires (fun h -> Buf.live h ct /\ Buf.live h ss /\ Buf.live h pk /\
    Buf.disjoint ct ss /\ Buf.disjoint ct pk /\ Buf.disjoint ss pk))
  (ensures (fun h0 r h1 -> Buf.live h1 ct /\ Buf.live h1 ss /\
    modifies (loc_union (loc_buffer ct) (loc_buffer ss)) h0 h1))
let crypto_kem_enc ct ss pk =
  push_frame();
  assert_norm (v crypto_ciphertextbytes = ((v params_nbar * v params_n + v params_nbar * v params_nbar) * v params_logq) / 8 + v crypto_bytes);
  assert_norm (v crypto_publickeybytes = v bytes_seed_a + (v params_logq * v params_n * v params_nbar) / 8);
  assert_norm (v bytes_mu = v ((params_nbar *. params_nbar *. params_extracted_bits) /. size 8));

  let coins = create ((params_nbar *! params_nbar *! params_extracted_bits) /. size 8) (u8 0) in
  randombytes_ ((params_nbar *! params_nbar *! params_extracted_bits) /. size 8) coins;

  let pk_coins = create (crypto_publickeybytes +! bytes_mu) (u8 0) in
  copy (sub pk_coins (size 0) crypto_publickeybytes) crypto_publickeybytes pk;
  copy (sub pk_coins crypto_publickeybytes bytes_mu) bytes_mu coins;

  let g:lbytes (size 3 *! crypto_bytes) = create (size 3 *! crypto_bytes) (u8 0) in
  cshake_frodo (crypto_publickeybytes +! bytes_mu) pk_coins (u16 3) (size 3 *! crypto_bytes) g;

  crypto_kem_enc_ct pk g coins ct;
  crypto_kem_enc_ss g ct ss;
  pop_frame();
  (u32 0)

val frodo_sub_mul_c_minus_bs:
  sk:lbytes crypto_secretkeybytes ->
  bp_matrix:matrix_t params_nbar params_n ->
  c_matrix:matrix_t params_nbar params_nbar ->
  mu_decode:lbytes (params_nbar *! params_nbar *! params_extracted_bits /. size 8) -> Stack unit
  (requires (fun h -> Buf.live h sk /\ Buf.live h bp_matrix /\
    Buf.live h c_matrix /\ Buf.live h mu_decode))
  (ensures (fun h0 r h1 -> Buf.live h1 mu_decode /\ modifies (loc_buffer mu_decode) h0 h1))
  [@"c_inline"]
let frodo_sub_mul_c_minus_bs sk bp_matrix c_matrix mu_decode =
  push_frame();
  assert_norm (v crypto_secretkeybytes = v crypto_bytes + v crypto_publickeybytes + 2 * v params_n * v params_nbar);
  let s_matrix  = matrix_create params_n params_nbar in
  matrix_from_lbytes (sub sk (crypto_bytes +! crypto_publickeybytes) (size 2 *! params_n *! params_nbar)) s_matrix;

  let m_matrix  = matrix_create params_nbar params_nbar in
  matrix_mul bp_matrix s_matrix m_matrix;
  matrix_sub c_matrix m_matrix;
  frodo_key_decode params_extracted_bits m_matrix mu_decode;
  pop_frame()


val crypto_kem_dec_ss:
  ct:lbytes crypto_ciphertextbytes ->
  g:lbytes (size 3 *! crypto_bytes) ->
  kp_s:lbytes crypto_bytes ->
  ss:lbytes crypto_bytes -> Stack unit
  (requires (fun h -> Buf.live h ct /\ Buf.live h g /\
    Buf.live h kp_s /\ Buf.live h ss /\
    Buf.disjoint ss ct /\ Buf.disjoint ss g /\ Buf.disjoint ss kp_s))
  (ensures (fun h0 r h1 -> Buf.live h1 ss /\ modifies (loc_buffer ss) h0 h1))
  [@"c_inline"]
let crypto_kem_dec_ss ct g kp_s ss =
  push_frame();
  assert_norm (v crypto_ciphertextbytes = ((v params_nbar * v params_n + v params_nbar * v params_nbar) * v params_logq) / 8 + v crypto_bytes);
  let c1Len = (params_logq *! params_nbar *! params_n) /. size 8 in
  let c2Len = (params_logq *! params_nbar *! params_nbar) /. size 8 in
  let c1 = sub #uint8 #_ #(v c1Len) ct (size 0) c1Len in
  let c2 = sub #uint8 #_ #(v c2Len) ct c1Len c2Len in
  let d = sub #uint8 #_ #(v crypto_bytes) ct (c1Len +! c2Len) crypto_bytes in

  let ss_init_len = c1Len +! c2Len +! size 2 *! crypto_bytes in
  let ss_init:lbytes ss_init_len = create ss_init_len (u8 0) in
  copy (sub ss_init (size 0) c1Len) c1Len c1;
  copy (sub ss_init c1Len c2Len) c2Len c2;
  copy (sub ss_init (c1Len +! c2Len) crypto_bytes) crypto_bytes kp_s;
  copy (sub ss_init (ss_init_len -! crypto_bytes) crypto_bytes) crypto_bytes d;

  cshake_frodo ss_init_len ss_init (u16 7) crypto_bytes ss;
  pop_frame()

let pk_mu_decode_len =
  assert_norm (v crypto_publickeybytes + v params_nbar * v params_nbar * v params_extracted_bits / 8 < max_size_t);
  normalize_term (crypto_publickeybytes +! params_nbar *! params_nbar *! params_extracted_bits /. size 8)

val crypto_kem_dec_ss1:
  pk_mu_decode:lbytes pk_mu_decode_len ->
  bp_matrix:matrix_t params_nbar params_n ->
  c_matrix:matrix_t params_nbar params_nbar ->
  sk:lbytes crypto_secretkeybytes ->
  ct:lbytes crypto_ciphertextbytes ->
  ss:lbytes crypto_bytes -> Stack unit
  (requires (fun h -> Buf.live h pk_mu_decode /\ Buf.live h bp_matrix /\
    Buf.live h c_matrix /\ Buf.live h sk /\ Buf.live h ct /\
    Buf.live h ss /\ Buf.disjoint ss ct /\ Buf.disjoint ss sk))
  (ensures (fun h0 r h1 -> Buf.live h1 ss /\ modifies (loc_buffer ss) h0 h1))
  [@"c_inline"]
let crypto_kem_dec_ss1 pk_mu_decode bp_matrix c_matrix sk ct ss =
  push_frame();
  assert_norm (v crypto_ciphertextbytes = ((v params_nbar * v params_n + v params_nbar * v params_nbar) * v params_logq) / 8 + v crypto_bytes);
  assert_norm (v crypto_secretkeybytes = v crypto_bytes + v crypto_publickeybytes + 2 * v params_n * v params_nbar);
  assert_norm (v crypto_publickeybytes = v bytes_seed_a + (v params_logq * v params_n * v params_nbar) / 8);
  assert_norm (v pk_mu_decode_len = v crypto_publickeybytes + v params_nbar * v params_nbar * v params_extracted_bits / 8);
  let s = sub #uint8 #_ #(v crypto_bytes) sk (size 0) crypto_bytes in
  let pk = sub #uint8 #_ #(v crypto_publickeybytes) sk crypto_bytes crypto_publickeybytes in
  let seed_a = sub #uint8 #_ #(v bytes_seed_a) pk (size 0) bytes_seed_a in
  let b = sub #uint8 #_ #(v ((params_logq *! params_n *! params_nbar) /. size 8)) pk bytes_seed_a (crypto_publickeybytes -! bytes_seed_a) in

  let mu_decode_len = params_nbar *! params_nbar *! params_extracted_bits /. size 8 in
  let g = create (size 3 *! crypto_bytes) (u8 0) in
  cshake_frodo (crypto_publickeybytes +! mu_decode_len) pk_mu_decode (u16 3) (size 3 *! crypto_bytes) g;
  let seed_ep = sub #uint8 #_ #(v crypto_bytes) g (size 0) crypto_bytes in
  let kp = sub #uint8 #_ #(v crypto_bytes) g crypto_bytes crypto_bytes in
  let dp = sub #uint8 #_ #(v crypto_bytes) g (size 2 *! crypto_bytes) crypto_bytes in

  let sp_matrix  = matrix_create params_nbar params_n in
  frodo_sample_matrix params_nbar params_n crypto_bytes seed_ep (u16 4) sp_matrix;

  let bpp_matrix = matrix_create params_nbar params_n in
  frodo_mul_add_sa_plus_e seed_a seed_ep sp_matrix bpp_matrix;

  let v_matrix   = matrix_create params_nbar params_nbar in
  let mu_decode  = sub pk_mu_decode crypto_publickeybytes (params_nbar *! params_nbar *! params_extracted_bits /. size 8) in
  frodo_mul_add_sb_plus_e_plus_mu b seed_ep mu_decode sp_matrix v_matrix;

  let c1Len = (params_logq *! params_nbar *! params_n) /. size 8 in
  let c2Len = (params_logq *! params_nbar *! params_nbar) /. size 8 in
  let d = sub #uint8 #_ #(v crypto_bytes) ct (c1Len +! c2Len) crypto_bytes in
  let b1 = lbytes_eq d dp in
  let b2 = matrix_eq params_logq bp_matrix bpp_matrix in
  let b3 = matrix_eq params_logq c_matrix v_matrix in
  let kp_s = if (b1 && b2 && b3) then kp else s in
  crypto_kem_dec_ss ct g kp_s ss;
  pop_frame()

val crypto_kem_dec:
  ss:lbytes crypto_bytes -> ct:lbytes crypto_ciphertextbytes ->
  sk:lbytes crypto_secretkeybytes -> Stack uint32
  (requires (fun h -> Buf.live h ss /\ Buf.live h ct /\ Buf.live h sk /\
    Buf.disjoint ss ct /\ Buf.disjoint ss sk))
  (ensures (fun h0 r h1 -> Buf.live h1 ss /\ modifies (loc_buffer ss) h0 h1))
let crypto_kem_dec ss ct sk =
  push_frame();
  assert_norm (v crypto_ciphertextbytes = ((v params_nbar * v params_n + v params_nbar * v params_nbar) * v params_logq) / 8 + v crypto_bytes);
  assert_norm (v crypto_secretkeybytes = v crypto_bytes + v crypto_publickeybytes + 2 * v params_n * v params_nbar);
  assert_norm (v crypto_publickeybytes = v bytes_seed_a + (v params_logq * v params_n * v params_nbar) / 8);
  assert_norm (v pk_mu_decode_len = v crypto_publickeybytes + v params_nbar * v params_nbar * v params_extracted_bits / 8);

  let c1Len = (params_logq *! params_nbar *! params_n) /. size 8 in
  let c2Len = (params_logq *! params_nbar *! params_nbar) /. size 8 in
  let c1 = sub #uint8 #_ #(v c1Len) ct (size 0) c1Len in
  let c2 = sub #uint8 #_ #(v c2Len) ct c1Len c2Len in
  let d = sub #uint8 #_ #(v crypto_bytes) ct (c1Len +! c2Len) crypto_bytes in

  let bp_matrix = matrix_create params_nbar params_n in
  let c_matrix  = matrix_create params_nbar params_nbar in
  frodo_unpack params_nbar params_n params_logq c1 bp_matrix;
  frodo_unpack params_nbar params_nbar params_logq c2 c_matrix;

  let mu_decode_len = params_nbar *! params_nbar *! params_extracted_bits /. size 8 in
  let mu_decode = create (params_nbar *! params_nbar *! params_extracted_bits /. size 8) (u8 0) in
  frodo_sub_mul_c_minus_bs sk bp_matrix c_matrix mu_decode;

  let pk_mu_decode = create (crypto_publickeybytes +! mu_decode_len) (u8 0) in
  let pk = sub #uint8 #_ #(v crypto_publickeybytes) sk crypto_bytes crypto_publickeybytes in
  copy (sub pk_mu_decode (size 0) crypto_publickeybytes) crypto_publickeybytes pk;
  copy (sub #_ #(v crypto_publickeybytes + v mu_decode_len) #(v mu_decode_len) pk_mu_decode crypto_publickeybytes mu_decode_len) mu_decode_len mu_decode;

  crypto_kem_dec_ss1 pk_mu_decode bp_matrix c_matrix sk ct ss;
  pop_frame();
  (u32 0)
