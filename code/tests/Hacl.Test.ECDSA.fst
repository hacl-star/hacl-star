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

#push-options "--lax"

%splice[sigver_vectors_low] 
  (lowstarize_toplevel "sigver_vectors_tmp" "sigver_vectors_low")

noextract
let siggen_vectors_tmp = List.Tot.map 
  (fun x -> h x.msg', h x.d, h x.qx', h x.qy', h x.k, h x.r', h x.s')
  siggen_vectors

%splice[siggen_vectors_low] 
  (lowstarize_toplevel "siggen_vectors_tmp" "siggen_vectors_low")

#pop-options

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
    let result' = ecdsa_p256_sha2_verify_u8 msg_len msg qxy r s in
    if result' = result then ()
    else 
      begin
      LowStar.Printf.(printf "FAIL\n" done);
      C.exit 1l
      end;
    pop_frame()
    end

val reverse_inplace_state: n:size_nat -> i:size_nat{i <= n / 2} -> Type0
let reverse_inplace_state n i = Lib.Sequence.lseq uint8 n

noextract
val reverse_inplace_inner: n:size_nat -> i:size_nat{i < n / 2}
  -> reverse_inplace_state n i -> reverse_inplace_state n (i + 1)
let reverse_inplace_inner n i s =
  let open Lib.Sequence in
  let tmp = s.[i] in
  let s = s.[i] <- s.[n - i - 1] in
  s.[n - i - 1] <- tmp

noextract
val reverse_inplace_spec: n:size_nat -> s:Lib.Sequence.lseq uint8 n -> Lib.Sequence.lseq uint8 n
let reverse_inplace_spec n s =
    Lib.LoopCombinators.repeat_gen (n / 2) (reverse_inplace_state n)
      (reverse_inplace_inner n) s

val reverse_inplace: n:size_t{0 < v n} -> a:Lib.Buffer.lbuffer uint8 n -> Stack unit
  (requires fun h0 -> Lib.Buffer.live h0 a)
  (ensures  fun h0 _ h1 ->
    Lib.Buffer.modifies1 a h0 h1 /\ 
    Lib.Buffer.as_seq h1 a == reverse_inplace_spec (v n) (Lib.Buffer.as_seq h0 a))

let reverse_inplace n a =
  let open Lib.Buffer in
  push_frame();
  let h0 = get() in
  loop h0 (n /. size 2) (reverse_inplace_state (v n))
    (fun h i -> as_seq h a)
    (fun i -> loc a)
    (fun h0 -> reverse_inplace_inner (v n))
    (fun i ->
      Lib.LoopCombinators.unfold_repeat_gen (v n / 2)
        (reverse_inplace_state (v n))
        (reverse_inplace_inner (v n)) 
        (Lib.Buffer.as_seq h0 a) (v i);
      let tmp = a.(i) in
      a.(i) <- a.(n -! i -! size 1);
      a.(n -! i -! size 1) <- tmp
    );
  pop_frame()


let test_siggen (vec:siggen_vector) : Stack unit (requires fun _ -> True) (ensures fun _ _ _ -> True) =
  // TODO: remove refinement in msg in signing
  assert_norm (pow2 32 < pow2 61);
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

  // We need to check this at runtime because Low*-ized vectors don't carry any refinements
  if not (d_len = 32ul && qx_len = 32ul && qy_len = 32ul && k_len = 32ul && r_len = 32ul && s_len = 32ul)
  then C.exit (-1l)
  else
    begin
    push_frame();
    let rs = B.alloca (u8 0) 64ul in
    let qxy = B.alloca (u8 0) 64ul in
    B.blit qx 0ul qxy 0ul 32ul;
    B.blit qy 0ul qxy 32ul 32ul;

    // TODO: signing uses wrong byte order; this is a temporary workaround.
    reverse_inplace 32ul d;
    reverse_inplace 32ul k;

    // TODO: the disjointness condition of signing need to be weakened
    assume (let open Lib.Buffer in
      B.all_disjoint [loc #MUT rs; loc #MUT msg; loc #MUT d; loc #MUT k]);
    let h = get() in
    assume (
      let d: Lib.Buffer.lbuffer uint8 32ul = d in
      let k: Lib.Buffer.lbuffer uint8 32ul = k in
      Lib.ByteSequence.nat_from_bytes_le (Lib.Buffer.as_seq h d) <
        Hacl.Spec.ECDSAP256.Definition.prime_p256_order /\
      Lib.ByteSequence.nat_from_bytes_le (Lib.Buffer.as_seq h k) <
        Hacl.Spec.ECDSAP256.Definition.prime_p256_order);
    let flag = ecdsa_p256_sha2_sign rs msg_len msg d k in
    if Lib.RawIntTypes.u64_to_UInt64 flag = 0uL then 
      begin
      // TODO: signing uses wrong byte order; this is a temporary workaround.
      reverse_inplace 32ul (B.sub rs 0ul 32ul);
      reverse_inplace 32ul (B.sub rs 32ul 32ul);
      
      let okr = compare_and_print (B.sub rs 0ul 32ul) r 32ul in
      let oks = compare_and_print (B.sub rs 32ul 32ul) s 32ul in
      if okr && oks then
        begin
        let result = ecdsa_p256_sha2_verify_u8 msg_len msg qxy r s in
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
