module Hacl.Impl.Frodo

open FStar.HyperStack.All
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Buffer
open Lib.ByteBuffer
open FStar.Mul
open FStar.Math.Lemmas

open Hacl.Impl.PQ.Lib
open Hacl.Keccak

val eq_u8: a:uint8 -> b:uint8 -> Tot bool
[@ "substitute"]
let eq_u8 a b = FStar.UInt8.(u8_to_UInt8 a =^ u8_to_UInt8 b)

val eq_u16_m:m:uint16 -> a:uint16 -> b:uint16 -> Tot bool
[@ "substitute"]
let eq_u16_m m a b = FStar.UInt16.(u16_to_UInt16 (a &. m) =^ u16_to_UInt16 (b &. m))

val matrix_eq:
  #n1:size_t -> #n2:size_t -> m:size_t{v m > 0} ->
  a:matrix_t n1 n2 -> b:matrix_t n1 n2 -> Stack bool
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> True))
  [@"c_inline"]
let matrix_eq #n1 #n2 m a b =
  admit();
  let m = (u16 1 <<. size_to_uint32 m) -. u16 1 in
  let res:lbuffer bool 1 = create (size 1) (true) in
  let h0 = FStar.HyperStack.ST.get () in
  loop_nospec #h0 n1 res
  (fun i ->
    loop_nospec #h0 n2 res
    (fun j ->
      let a1 = res.(size 0) in
      let a2 = eq_u16_m m (mget a i j) (mget b i j) in
      res.(size 0) <- a1 && a2
    )
  );
  res.(size 0)

val lbytes_eq:
  #len:size_t -> a:lbytes (v len) -> b:lbytes (v len) -> Stack bool
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> True))
  [@"c_inline"]
let lbytes_eq #len a b =
  admit();
  let res:lbuffer bool 1 = create (size 1) (true) in
  let h0 = FStar.HyperStack.ST.get () in
  loop_nospec #h0 len res
  (fun i ->
    let a1 = res.(size 0) in
    let a2 = eq_u8 a.(i) b.(i) in
    res.(size 0) <- a1 && a2
  );
  res.(size 0)

//FrodoKEM-640
let params_n = size 64 //640
let params_logq = size 15
let params_extracted_bits = size 2
let crypto_bytes = size 16
let cshake_frodo = cshake128_frodo
let cdf_table_len = size 12

let cdf_table : lbuffer uint16 (v cdf_table_len) =
  let cdf_table0: list uint16 =
    [u16 4727; u16 13584; u16 20864; u16 26113; u16 29434; u16 31278; u16 32176; u16 32560; u16 32704; u16 32751; u16 32764; u16 32767] in
  assert_norm(List.Tot.length cdf_table0 = v cdf_table_len);
  createL_global
    [u16 4727; u16 13584; u16 20864; u16 26113; u16 29434; u16 31278;
     u16 32176; u16 32560; u16 32704; u16 32751; u16 32764; u16 32767]

let bytes_seed_a = size 16
let params_nbar = size 8
let params_q = size 32768 //2 ** params_logq

let bytes_mu =  normalize_term ((params_extracted_bits *. params_nbar *. params_nbar) /. size 8)
let crypto_publickeybytes = normalize_term (bytes_seed_a +. (params_logq *. params_n *. params_nbar) /. size 8)
let crypto_secretkeybytes = normalize_term (crypto_bytes +. crypto_publickeybytes +. size 2 *. params_n *. params_nbar)
let crypto_ciphertextbytes = normalize_term (((params_nbar *. params_n +. params_nbar *. params_nbar) *. params_logq) /. size 8 +. crypto_bytes)

#reset-options "--z3rlimit 50 --max_fuel 0"
val ec:b:size_t -> k:uint16 -> Tot uint16
  [@ "substitute"]
let ec b a =
  assume (v (params_logq -. b) < 16);
  shift_left #U16 a (size_to_uint32 (params_logq -. b))

val dc:b:size_t -> c:uint16 -> Tot uint16
  [@ "substitute"]
let dc b c =
  assume (v (params_logq -. b -. size 1) < 16);
  assume (v (params_logq -. b) < 16);
  let res1 = (c +. (u16 1 <<. size_to_uint32 (params_logq -. b -. size 1))) >>. size_to_uint32 (params_logq -. b) in
  res1 &. ((u16 1 <<. size_to_uint32 b) -. u16 1)

val frodo_key_encode:
  b:size_t{v ((params_nbar *. params_nbar *. b) /. size 8) < max_size_t /\ v b <= 8} ->
  a:lbytes (v ((params_nbar *. params_nbar *. b) /. size 8)) ->
  res:matrix_t params_nbar params_nbar -> Stack unit
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> True))
  [@"c_inline"]
let frodo_key_encode b a res =
  admit();
  let aLen = (params_nbar *. params_nbar *. b) /. size 8 in
  let v8 = create (size 8) (u8 0) in
  let h0 = FStar.HyperStack.ST.get () in
  loop_nospec #h0 params_nbar res
  (fun i ->
    loop_nospec #h0 (normalize_term (params_nbar /. size 8)) res
    (fun j ->
      copy (sub v8 (size 0) b) b (sub #uint8 #(v aLen) #(v b) a ((i+.j)*.b) b);
      let vij = uint_from_bytes_le v8 in
      loop_nospec #h0 (size 8) res
      (fun k ->
	let ak = (vij >>. size_to_uint32 (b *. k)) &. ((u64 1 <<. size_to_uint32 b) -. u64 1) in
        let resij = ec b (to_u16 ak) in
        mset res i (size 8 *. j +. k) resij
      )
    )
  )

val frodo_key_decode:
  b:size_t{v ((params_nbar *. params_nbar *. b) /. size 8) < max_size_t /\ v b <= 8} ->
  a:matrix_t params_nbar params_nbar ->
  res:lbytes (v ((params_nbar *. params_nbar *. b) /. size 8)) -> Stack unit
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> True))
  [@"c_inline"]
let frodo_key_decode b a res =
  admit();
  let resLen = (params_nbar *. params_nbar *. b) /. size 8 in
  let v8 = create (size 8) (u8 0) in
  let templong:lbuffer uint64 1 = create (size 1) (u64 0) in
  let h0 = FStar.HyperStack.ST.get () in
  loop_nospec #h0 params_nbar res
  (fun i ->
    loop_nospec #h0 (normalize_term (params_nbar /. size 8)) res
    (fun j ->
      templong.(size 0) <- u64 0;
      loop_nospec #h0 (size 8) templong
      (fun k ->
	let aij = dc b (mget a i (size 8 *. j +. k)) in
	templong.(size 0) <- templong.(size 0) |. (to_u64 aij <<. size_to_uint32 (b *. k))
      );
      uint_to_bytes_le #U64 v8 (templong.(size 0));
      copy (sub res ((i +. j) *. b) b) b (sub #uint8 #8 #(v b) v8 (size 0) b)
    )
  )

val frodo_pack:
  n1:size_t -> n2:size_t{v n1 * v n2 < max_size_t /\ v n2 % 8 = 0} ->
  a:matrix_t n1 n2 ->
  d:size_t{v ((d *. n1 *. n2) /. size 8) < max_size_t /\ v d <= 16} ->
  res:lbytes (v ((d *. n1 *. n2) /. size 8)) -> Stack unit
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> True))
  [@"c_inline"]
let frodo_pack n1 n2 a d res =
  admit();
  let maskd = (u16 1 <<. size_to_uint32 d) -. u16 1 in
  let templong:lbuffer uint128 1 = create (size 1) (to_u128 (u64 0)) in
  let v16 = create (size 16) (u8 0) in
  let n28 = n2 /. size 8 in
  let h0 = FStar.HyperStack.ST.get () in
  loop_nospec #h0 n1 res
  (fun i ->
    loop_nospec #h0 n28 res
    (fun j ->
      templong.(size 0) <- (to_u128 (u64 0));
      loop_nospec #h0 (size 8) templong
      (fun k ->
	let aij = (mget a i (size 8 *. j +. k)) &. maskd in
	templong.(size 0) <- templong.(size 0) |. (to_u128 aij <<. size_to_uint32 (size 7 *. d -. d *. k))
      );
      uint_to_bytes_be #U128 v16 (templong.(size 0));
      copy (sub res ((i *. n2 /. size 8 +. j) *. d) d) d (sub #uint8 #16 #(v d) v16 (size 16 -. d) d)
    )
  )

val frodo_unpack:
  n1:size_t -> n2:size_t{v n1 * v n2 < max_size_t /\ v n2 % 8 = 0} ->
  d:size_t{v ((d *. n1 *. n2) /. size 8) < max_size_t /\ v d <= 16} ->
  b:lbytes (v ((d *. n1 *. n2) /. size 8)) ->
  res:matrix_t n1 n2 -> Stack unit
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> True))
  [@"c_inline"]
let frodo_unpack n1 n2 d b res =
  admit();
  let maskd = (u16 1 <<. size_to_uint32 d) -. u16 1 in
  let v16 = create (size 16) (u8 0) in
  let n28 = n2 /. size 8 in
  let h0 = FStar.HyperStack.ST.get () in
  loop_nospec #h0 n1 res
  (fun i ->
    loop_nospec #h0 n28 res
    (fun j ->
      copy (sub v16 (size 16 -. d) d) d (sub #uint8 #_ #(v d) b ((i *. n2 /. size 8 +. j) *. d) d);
      let templong = uint_from_bytes_be #U128 v16 in
      loop_nospec #h0 (size 8) res
      (fun k ->
	let resij = to_u16 (templong >>. size_to_uint32 (size 7 *. d -. d *. k)) &. maskd in
	mset res i (size 8 *. j +. k) resij
      )
    )
  )


val frodo_sample: r:uint16 -> Stack uint16
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> True))
  [@"c_inline"]
let frodo_sample r =
  admit();
  let prnd = r >>. u32 1 in
  let sample:lbuffer uint16 1 = create (size 1) (u16 0) in
  let sign = r &. u16 1 in

  let h0 = FStar.HyperStack.ST.get () in
  let ctr = cdf_table_len -. size 1 in
  loop_nospec #h0 ctr sample
  (fun j ->
    let tj = cdf_table.(j) in
    let sample0 = sample.(size 0) in
    sample.(size 0) <- sample0 +. (to_u16 (to_u32 (tj -. prnd)) >>. u32 15)
  );
  //((-sign) ^. sample.(size 0)) +.sign
  //(FStar.Math.Lib.powx (-1) (uint_to_nat r0)) * e
  (lognot sign +. u16 1) ^. sample.(size 0)


val frodo_sample_matrix:
  n1:size_t -> n2:size_t{2 * v n1 * v n2 < max_size_t} ->
  seed_len:size_t -> seed:lbytes (v seed_len) -> ctr:uint16 ->
  res:matrix_t n1 n2 -> Stack unit
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> True))
  [@"c_inline"]
let frodo_sample_matrix n1 n2 seed_len seed ctr res =
  admit();
  let r = create (size 2 *. n1 *. n2) (u8 0) in
  cshake_frodo seed_len seed ctr (size 2 *. n1 *. n2) r;
  let h0 = FStar.HyperStack.ST.get () in
  loop_nospec #h0 n1 res
  (fun i ->
    loop_nospec #h0 n2 res
    (fun j ->
      let resij = sub r (size 2 *. (n2 *. i +. j)) (size 2) in
      mset res i j (frodo_sample (uint_from_bytes_le #U16 resij))
    )
  )

val frodo_sample_matrix_tr:
  n1:size_t -> n2:size_t{2 * v n1 * v n2 < max_size_t} ->
  seed_len:size_t -> seed:lbytes (v seed_len) -> ctr:uint16 ->
  res:matrix_t n1 n2 -> Stack unit
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> True))
  [@"c_inline"]
let frodo_sample_matrix_tr n1 n2 seed_len seed ctr res =
  admit();
  let r = create (size 2 *. n1 *. n2) (u8 0) in
  cshake_frodo seed_len seed ctr (size 2 *. n1 *. n2) r;
  let h0 = FStar.HyperStack.ST.get () in
  loop_nospec #h0 n1 res
  (fun i ->
    loop_nospec #h0 n2 res
    (fun j ->
      let resij = sub r (size 2 *. (n1 *. j +. i)) (size 2) in
      mset res i j (frodo_sample (uint_from_bytes_le #U16 resij))
    )
  )

val frodo_gen_matrix_cshake:
  n:size_t{2 * v n < max_size_t} ->
  seed_len:size_t -> seed:lbytes (v seed_len) ->
  res:matrix_t n n -> Stack unit
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> True))
  [@"c_inline"]
let frodo_gen_matrix_cshake n seed_len seed res =
  admit();
  let r = create (size 2 *. n) (u8 0) in
  let h0 = FStar.HyperStack.ST.get () in
  loop_nospec #h0 n res
  (fun i ->
    cshake128_frodo seed_len seed (u16 256 +. to_u16 i) (size 2 *. n) r;
    loop_nospec #h0 n res
    (fun j ->
      let resij = sub r (size 2 *. j) (size 2) in
      mset res i j (uint_from_bytes_le #U16 resij)
    )
  )

let frodo_gen_matrix = frodo_gen_matrix_cshake

val matrix_to_lbytes:
  #n1:size_t -> #n2:size_t -> m:matrix_t n1 n2 ->
  res:lbytes (v (size 2 *. n1 *. n2)) -> Stack unit
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> True))
  [@"c_inline"]
let matrix_to_lbytes #n1 #n2 m res =
  admit();
  let h0 = FStar.HyperStack.ST.get () in
  loop_nospec #h0 n1 res
  (fun i ->
    loop_nospec #h0 n2 res
    (fun j ->
      uint_to_bytes_le (sub res (size 2 *. (j *. n1 +. i)) (size 2)) (mget m i j)
    )
  )

val matrix_from_lbytes:
  #n1:size_t -> #n2:size_t -> b:lbytes (v (size 2 *. n1 *. n2)) ->
  m:matrix_t n1 n2 -> Stack unit
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> True))
  [@"c_inline"]
let matrix_from_lbytes #n1 #n2 b res =
  admit();
  let h0 = FStar.HyperStack.ST.get () in
  loop_nospec #h0 n1 res
  (fun i ->
    loop_nospec #h0 n2 res
    (fun j ->
      mset res i j (uint_from_bytes_le #U16 (sub b (size 2 *. (j *. n1 +. i)) (size 2)))
    )
  )

val crypto_kem_keypair:
  coins:lbytes (v (size 2 *. crypto_bytes +. bytes_seed_a)){v (size 2 *. crypto_bytes +. bytes_seed_a) < max_size_t} ->
  pk:lbytes (v crypto_publickeybytes) ->
  sk:lbytes (v crypto_secretkeybytes) -> Stack unit
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> True))
let crypto_kem_keypair coins pk sk =
  admit();
  let seed_a = sub pk (size 0) bytes_seed_a in
  let b = sub pk bytes_seed_a (crypto_publickeybytes -. bytes_seed_a) in
  let a_matrix = matrix_create params_n params_n in
  let s_matrix = matrix_create params_n params_nbar in
  let e_matrix = matrix_create params_n params_nbar in
  let b_matrix = matrix_create params_n params_nbar in

  let s:lbytes (v crypto_bytes) = sub coins (size 0) crypto_bytes in
  let seed_e = sub coins crypto_bytes crypto_bytes in
  let z = sub coins (size 2 *. crypto_bytes) bytes_seed_a in
  cshake_frodo bytes_seed_a z (u16 0) bytes_seed_a seed_a;

  frodo_gen_matrix params_n bytes_seed_a seed_a a_matrix;
  frodo_sample_matrix_tr params_n params_nbar crypto_bytes seed_e (u16 1) s_matrix;
  frodo_sample_matrix params_n params_nbar crypto_bytes seed_e (u16 2) e_matrix;
  matrix_mul a_matrix s_matrix b_matrix;
  matrix_add b_matrix e_matrix;
  frodo_pack params_n params_nbar b_matrix params_logq b;
  copy (sub sk (size 0) crypto_bytes) crypto_bytes s;
  copy (sub sk crypto_bytes crypto_publickeybytes) crypto_publickeybytes pk;
  matrix_to_lbytes s_matrix (sub sk (crypto_bytes +. crypto_publickeybytes) (size 2 *. params_n *. params_nbar))

//{v bytes_mu = v ((params_nbar *. params_nbar *. params_extracted_bits) /. size 8)}
val crypto_kem_enc:
  coins:lbytes (v ((params_nbar *. params_nbar *. params_extracted_bits) /. size 8)) ->
  pk:lbytes (v crypto_publickeybytes) ->
  ct:lbytes (v crypto_ciphertextbytes) -> ss:lbytes (v crypto_bytes) -> Stack unit
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> True))
let crypto_kem_enc coins pk ct ss =
  admit();
  let seed_a = sub #uint8 #_ #(v bytes_seed_a) pk (size 0) bytes_seed_a in
  let b = sub #uint8 #_ #(v ((params_logq *. params_n *. params_nbar) /. size 8)) pk bytes_seed_a (crypto_publickeybytes -. bytes_seed_a) in

  let g:lbytes (v (size 3 *. crypto_bytes)) = create (size 3 *. crypto_bytes) (u8 0) in
  let pk_coins = create (crypto_publickeybytes +. bytes_mu) (u8 0) in
  copy (sub pk_coins (size 0) crypto_publickeybytes) crypto_publickeybytes pk;
  copy (sub pk_coins crypto_publickeybytes bytes_mu) bytes_mu coins;
  cshake_frodo (crypto_publickeybytes +. bytes_mu) pk_coins (u16 3) (size 3 *. crypto_bytes) g;
  let seed_e = sub #uint8 #_ #(v crypto_bytes) g (size 0) crypto_bytes in
  let k = sub #uint8 #_ #(v crypto_bytes) g crypto_bytes crypto_bytes in
  let d = sub #uint8 #_ #(v crypto_bytes) g (size 2 *.crypto_bytes) crypto_bytes in

  let sp_matrix = matrix_create params_nbar params_n in
  let ep_matrix = matrix_create params_nbar params_n in
  let a_matrix  = matrix_create params_n params_n in
  let bp_matrix = matrix_create params_nbar params_n in

  frodo_sample_matrix params_nbar params_n crypto_bytes seed_e (u16 4) sp_matrix;
  frodo_sample_matrix params_nbar params_n crypto_bytes seed_e (u16 5) ep_matrix;
  frodo_gen_matrix params_n bytes_seed_a seed_a a_matrix;
  matrix_mul sp_matrix a_matrix bp_matrix;
  matrix_add bp_matrix ep_matrix;
  let c1Len = (params_logq *. params_nbar *. params_n) /. size 8 in
  frodo_pack params_nbar params_n bp_matrix params_logq (sub ct (size 0) c1Len);

  let epp_matrix = matrix_create params_nbar params_nbar in
  let b_matrix   = matrix_create params_n params_nbar in
  let v_matrix   = matrix_create params_nbar params_nbar in
  let mu_encode  = matrix_create params_nbar params_nbar in

  frodo_sample_matrix params_nbar params_nbar crypto_bytes seed_e (u16 6) epp_matrix;
  frodo_unpack params_n params_nbar params_logq b b_matrix;
  matrix_mul sp_matrix b_matrix v_matrix;
  matrix_add v_matrix epp_matrix;
  frodo_key_encode params_extracted_bits coins mu_encode;
  matrix_add v_matrix mu_encode;
  let c2Len = (params_logq *. params_nbar *. params_nbar) /. size 8 in
  frodo_pack params_nbar params_nbar v_matrix params_logq (sub ct c1Len c2Len);

  let ss_init_len = c1Len +. c2Len +. size 2 *. crypto_bytes in
  let ss_init:lbytes (v ss_init_len) = create ss_init_len (u8 0) in
  cshake_frodo ss_init_len ss_init (u16 7) crypto_bytes ss;
  copy (sub ct (c1Len +. c2Len) crypto_bytes) crypto_bytes d

val crypto_kem_dec:
  ct:lbytes (v crypto_ciphertextbytes) -> sk:lbytes (v crypto_secretkeybytes) ->
  ss:lbytes (v crypto_bytes) -> Stack unit
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> True))
let crypto_kem_dec ct sk ss =
  admit();
  let c1Len = (params_logq *. params_nbar *. params_n) /. size 8 in
  let c2Len = (params_logq *. params_nbar *. params_nbar) /. size 8 in
  let c1 = sub #uint8 #_ #(v c1Len) ct (size 0) c1Len in
  let c2 = sub #uint8 #_ #(v c2Len) ct c1Len c2Len in
  let d = sub #uint8 #_ #(v crypto_bytes) ct (c1Len +. c2Len) crypto_bytes in

  let s_matrix  = matrix_create params_n params_nbar in
  let bp_matrix = matrix_create params_nbar params_n in
  let c_matrix  = matrix_create params_nbar params_nbar in
  let m_matrix  = matrix_create params_nbar params_nbar in
  let mu_decode_len = params_extracted_bits *. params_nbar *. params_nbar /. size 8 in
  let mu_decode = create mu_decode_len (u8 0) in

  let s = sub #uint8 #_ #(v crypto_bytes) sk (size 0) crypto_bytes in
  let pk = sub #uint8 #_ #(v crypto_publickeybytes) sk crypto_bytes crypto_publickeybytes in
  matrix_from_lbytes (sub sk (crypto_bytes +. crypto_publickeybytes) (size 2 *. params_n *. params_nbar)) s_matrix;
  let seed_a = sub #uint8 #_ #(v bytes_seed_a) pk (size 0) bytes_seed_a in
  let b = sub #uint8 #_ #(v c1Len) pk bytes_seed_a (crypto_publickeybytes -. bytes_seed_a) in

  frodo_unpack params_nbar params_n params_logq c1 bp_matrix;
  frodo_unpack params_nbar params_nbar params_logq c2 c_matrix;
  matrix_mul bp_matrix s_matrix m_matrix;
  matrix_sub c_matrix m_matrix; //modifies m_matrix
  frodo_key_decode params_extracted_bits m_matrix mu_decode;

  let g:lbytes (v (size 3 *. crypto_bytes)) = create (size 3 *. crypto_bytes) (u8 0) in
  let pk_mu_decode = create (crypto_publickeybytes +. mu_decode_len) (u8 0) in
  copy (sub pk_mu_decode (size 0) crypto_publickeybytes) crypto_publickeybytes pk;
  copy (sub pk_mu_decode crypto_publickeybytes mu_decode_len) mu_decode_len mu_decode;
  cshake_frodo (crypto_publickeybytes +. mu_decode_len) pk_mu_decode (u16 3) (size 3 *. crypto_bytes) g;
  let seed_ep = sub #uint8 #_ #(v crypto_bytes) g (size 0) crypto_bytes in
  let kp = sub #uint8 #_ #(v crypto_bytes)  g crypto_bytes crypto_bytes in
  let dp = sub #uint8 #_ #(v crypto_bytes) g (size 2 *. crypto_bytes) crypto_bytes in

  let sp_matrix  = matrix_create params_nbar params_n in
  let ep_matrix  = matrix_create params_nbar params_n in
  let a_matrix   = matrix_create params_n params_n in
  let bpp_matrix = matrix_create params_nbar params_n in
  frodo_sample_matrix params_nbar params_n crypto_bytes seed_ep (u16 4) sp_matrix;
  frodo_sample_matrix params_nbar params_n crypto_bytes seed_ep (u16 5) ep_matrix;
  frodo_gen_matrix params_n bytes_seed_a seed_a a_matrix;
  matrix_mul sp_matrix a_matrix bpp_matrix;
  matrix_add bpp_matrix ep_matrix;

  let epp_matrix = matrix_create params_nbar params_nbar in
  let b_matrix   = matrix_create params_n params_nbar in
  let v_matrix   = matrix_create params_nbar params_nbar in
  frodo_sample_matrix params_nbar params_nbar crypto_bytes seed_ep (u16 6) epp_matrix;
  frodo_unpack params_n params_nbar params_logq b b_matrix;
  matrix_mul sp_matrix b_matrix v_matrix;
  matrix_add v_matrix epp_matrix;

  let mu_encode = matrix_create params_nbar params_nbar in
  frodo_key_encode params_extracted_bits mu_decode mu_encode;
  matrix_add v_matrix mu_encode; //cp_matrix = v_matrix

  let ss_init_len = c1Len +. c2Len +. size 2 *. crypto_bytes in
  let ss_init:lbytes (v ss_init_len) = create ss_init_len (u8 0) in
  copy (sub ss_init (size 0) c1Len) c1Len c1;
  copy (sub ss_init c1Len c2Len) c2Len c2;
  copy (sub ss_init (ss_init_len -. crypto_bytes) crypto_bytes) crypto_bytes d;

  //let bcond = (lbytes_eq d dp) && (matrix_eq params_q bp_matrix bpp_matrix) && (matrix_eq params_q c_matrix cp_matrix) in
  let bcond = true in
  (if (bcond) then
    copy (sub ss_init (c1Len +. c2Len) crypto_bytes) crypto_bytes kp
   else
    copy (sub ss_init (c1Len +. c2Len) crypto_bytes) crypto_bytes s);

  cshake_frodo ss_init_len ss_init (u16 7) crypto_bytes ss
