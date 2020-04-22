module Hacl.Test.ECDSA

open FStar.HyperStack.ST
open Test.Lowstarize

open Lib.IntTypes

open Hacl.Impl.ECDSA
open Spec.ECDSA.Test.Vectors

module L = Test.Lowstarize
module B = LowStar.Buffer

#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"

noextract
let sigver_vectors_tmp = List.Tot.map
  (fun x -> h x.msg, h x.qx, h x.qy, h x.r, h x.s, x.result)
  sigver_vectors

noextract
let siggen_vectors_tmp = List.Tot.map
  (fun x -> h x.msg', h x.d, h x.qx', h x.qy', h x.k, h x.r', h x.s')
  siggen_vectors

%splice[sigver_vectors_low]
  (lowstarize_toplevel "sigver_vectors_tmp" "sigver_vectors_low")

%splice[siggen_vectors_low]
  (lowstarize_toplevel "siggen_vectors_tmp" "siggen_vectors_low")

// Cheap alternative to friend Lib.IntTypes needed because Test.Lowstarize uses UInt8.t
assume val declassify_uint8: squash (uint8 == UInt8.t)

let vec8 = L.lbuffer UInt8.t

let sigver_vector = vec8 & vec8 & vec8 & vec8 & vec8 & bool

let siggen_vector = vec8 & vec8 & vec8 & vec8 & vec8 & vec8 & vec8

// This could replace TestLib.compare_and_print
val compare_and_print: b1:B.buffer UInt8.t -> b2:B.buffer UInt8.t -> len:UInt32.t
  -> Stack bool
  (requires fun h0 -> B.live h0 b1 /\ B.live h0 b2 /\ B.length b1 == v len /\ B.length b2 == v len)
  (ensures  fun h0 _ h1 -> B.modifies B.loc_none h0 h1)
let compare_and_print b1 b2 len =
  push_frame();
  LowStar.Printf.(printf "Expected: %xuy\n" len b1 done);
  LowStar.Printf.(printf "Computed: %xuy\n" len b2 done);
  let b = Lib.ByteBuffer.lbytes_eq #len b1 b2 in
  if b then
    LowStar.Printf.(printf "PASS\n" done)
  else
    LowStar.Printf.(printf "FAIL\n" done);
  pop_frame();
  b

let test_sigver (vec:sigver_vector) : Stack unit (requires fun _ -> True) (ensures fun _ _ _ -> True) =
  let max_msg_len = 0 in
  let LB msg_len msg,
      LB qx_len qx,
      LB qy_len qy,
      LB r_len r,
      LB s_len s,
      result = vec
  in
  B.recall msg;
  B.recall qx;
  B.recall qy;
  B.recall r;
  B.recall s;
  // We need to check this at runtime because Low*-ized vectors don't carry any refinements
  if not (qx_len = 32ul && qy_len = 32ul && r_len = 32ul && s_len = 32ul)
  then C.exit (-1l)
  else
    begin
    push_frame();
    let qxy = B.alloca (u8 0) 64ul in
    B.blit qx 0ul qxy 0ul 32ul;
    B.blit qy 0ul qxy 32ul 32ul;
    let result' = ecdsa_p256_sha2_verify msg_len msg qxy r s in
    if result' = result then ()
    else
      begin
      LowStar.Printf.(printf "FAIL\n" done);
      C.exit 1l
      end;
    pop_frame()
    end


val check_bound: b:Lib.Buffer.lbuffer uint8 32ul -> Stack bool
  (requires fun h -> Lib.Buffer.live h b)
  (ensures  fun h0 r h1 ->
    h0 == h1 /\
    r == (Lib.ByteSequence.nat_from_bytes_be (Lib.Buffer.as_seq h0 b) <
          Spec.ECDSAP256.Definition.prime_p256_order))

let check_bound b =
  let open FStar.Mul in
  let open Lib.ByteSequence in
  let open Spec.ECDSAP256.Definition in
  [@inline_let]
  let q1 = normalize_term (prime_p256_order % pow2 64) in
  [@inline_let]
  let q2 = normalize_term ((prime_p256_order / pow2 64) % pow2 64) in
  [@inline_let]
  let q3 = normalize_term ((prime_p256_order / pow2 128) % pow2 64) in
  [@inline_let]
  let q4 = normalize_term (((prime_p256_order / pow2 128) / pow2 64) % pow2 64) in
  assert_norm (pow2 128 * pow2 64 == pow2 192);
  assert (prime_p256_order == q1 + pow2 64 * q2 + pow2 128 * q3 + pow2 192 * q4); 
  let q1 = mk_int #U64 #PUB q1 in
  let q2 = mk_int #U64 #PUB q2 in
  let q3 = mk_int #U64 #PUB q3 in
  let q4 = mk_int #U64 #PUB q4 in

  let h0 = get () in
  let x1 = Lib.ByteBuffer.uint_from_bytes_be #U64 (Lib.Buffer.sub b 0ul 8ul) in
  let x2 = Lib.ByteBuffer.uint_from_bytes_be #U64 (Lib.Buffer.sub b 8ul 8ul) in
  let x3 = Lib.ByteBuffer.uint_from_bytes_be #U64 (Lib.Buffer.sub b 16ul 8ul) in
  let x4 = Lib.ByteBuffer.uint_from_bytes_be #U64 (Lib.Buffer.sub b 24ul 8ul) in

  nat_from_intseq_be_slice_lemma (Lib.Buffer.as_seq h0 b) 8;
  lemma_reveal_uint_to_bytes_be #U64 (Lib.Sequence.slice (Lib.Buffer.as_seq h0 b) 0 8);

  nat_from_intseq_be_slice_lemma (Lib.Sequence.slice (Lib.Buffer.as_seq h0 b) 8 32) 8;
  lemma_reveal_uint_to_bytes_be #U64 (Lib.Sequence.slice (Lib.Buffer.as_seq h0 b) 8 16);

  nat_from_intseq_be_slice_lemma (Lib.Sequence.slice (Lib.Buffer.as_seq h0 b) 16 32) 8;
  lemma_reveal_uint_to_bytes_be #U64 (Lib.Sequence.slice (Lib.Buffer.as_seq h0 b) 16 24);

  nat_from_intseq_be_slice_lemma (Lib.Sequence.slice (Lib.Buffer.as_seq h0 b) 24 32) 8;
  lemma_reveal_uint_to_bytes_be #U64 (Lib.Sequence.slice (Lib.Buffer.as_seq h0 b) 24 32);

  let x1 = Lib.RawIntTypes.u64_to_UInt64 x1 in
  let x2 = Lib.RawIntTypes.u64_to_UInt64 x2 in
  let x3 = Lib.RawIntTypes.u64_to_UInt64 x3 in
  let x4 = Lib.RawIntTypes.u64_to_UInt64 x4 in
  x1 <. q4 || (x1 =. q4 &&
    (x2 <. q3 || (x2 =. q3 &&
      (x3 <. q2 || (x3 =. q2 && x4 <. q1)))))


let test_siggen (vec:siggen_vector) : Stack unit (requires fun _ -> True) (ensures fun _ _ _ -> True) =
  let max_msg_len = 0 in
  let LB msg_len msg,
      LB d_len d,
      LB qx_len qx,
      LB qy_len qy,
      LB k_len k,
      LB r_len r,
      LB s_len s = vec
  in
  B.recall msg;
  B.recall d;
  B.recall qx;
  B.recall qy;
  B.recall k;
  B.recall r;
  B.recall s;

  if not (k_len = 32ul && d_len = 32ul) then
    C.exit (-1l);

  let bound_k = check_bound k in
  let bound_d = check_bound d in

  // We need to check this at runtime because Low*-ized vectors don't carry any refinements
  if not (bound_k && bound_d &&
          qx_len = 32ul && qy_len = 32ul && r_len = 32ul && s_len = 32ul)
  then C.exit (-1l)
  else
    begin
    push_frame();
    let rs  = B.alloca (u8 0) 64ul in
    let qxy = B.alloca (u8 0) 64ul in
    B.blit qx 0ul qxy 0ul 32ul;
    B.blit qy 0ul qxy 32ul 32ul;

    let flag = ecdsa_p256_sha2_sign rs msg_len msg d k in
    if Lib.RawIntTypes.u64_to_UInt64 flag = 0uL then
      begin
      let okr = compare_and_print (B.sub rs 0ul 32ul) r 32ul in
      let oks = compare_and_print (B.sub rs 32ul 32ul) s 32ul in
      if okr && oks then
        begin
        let result = ecdsa_p256_sha2_verify msg_len msg qxy r s in
        if not result then
          begin
          LowStar.Printf.(printf "FAIL: verification\n" done);
          C.exit 1l
          end
        end
      else
        begin
        LowStar.Printf.(printf "FAIL: signing\n" done);
        C.exit 1l
        end
      end
    else
      begin
      LowStar.Printf.(printf "FAIL: signing\n" done);
      C.exit 1l
      end;
    pop_frame()
    end


inline_for_extraction noextract
let test_many #a (label:C.String.t)
  (f:a -> Stack unit (fun _ -> True) (fun _ _ _ -> True)) (vec: L.lbuffer a)
=
  C.String.print label;
  C.String.(print !$"\n");
  let L.LB len vs = vec in
  let f (i:UInt32.t{0 <= v i /\ v i < v len}): Stack unit
    (requires fun h -> True)
    (ensures fun h0 _ h1 -> True)
  =
    let open LowStar.BufferOps in
    B.recall vs;
    LowStar.Printf.(printf "ECDSA Test %ul/%ul\n" (i +! 1ul) len done);
    f vs.(i)
  in
  C.Loops.for 0ul len (fun _ _ -> True) f


let main () : St C.exit_code =
  test_many C.String.(!$"[ECDSA SigVer]") test_sigver sigver_vectors_low;
  test_many C.String.(!$"[ECDSA SigGen]") test_siggen siggen_vectors_low;
  C.EXIT_SUCCESS
