module Hacl.Impl.MGF

open FStar.HyperStack.All
open Spec.Lib.IntBuf.Lemmas
open Spec.Lib.IntBuf
open Spec.Lib.IntTypes
open FStar.Mul

open Hacl.Impl.Lib

module Buffer = Spec.Lib.IntBuf

(* SHA 256 *)
inline_for_extraction
let hLen:size_t = size 32

val hash_sha256:
  mHash:lbytes hLen ->
  len:size_t ->
  m:lbytes len -> Stack unit
  (requires (fun h -> live h mHash /\ live h m /\ disjoint m mHash))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 mHash h0 h1))
let hash_sha256 mHash len m = Hacl.SHA256.hash mHash len m
//SHA2_256.hash mHash m clen

(* Mask Generation Function *)
val mgf_sha256_:
  mgfseedLen:size_t -> accLen:size_t ->
  stLen:size_t{v stLen = v mgfseedLen + 4 + v hLen + v accLen} ->
  st:lbytes stLen -> count_max:size_t{v accLen = v count_max * v hLen} -> Stack unit
  (requires (fun h -> live h st))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st h0 h1))
  [@ "substitute"]
let mgf_sha256_ mgfseedLen accLen stLen st count_max =
  iteri_simple #uint8 #(v stLen) count_max
  (fun counter st ->
    let mgfseed_counterLen = add #SIZE mgfseedLen (size 4) in
    let mgfseed_counter = Buffer.sub #uint8 #(v stLen) #(v mgfseed_counterLen) st (size 0) mgfseed_counterLen in
    let mHash = Buffer.sub #uint8 #(v stLen) #(v hLen) st mgfseed_counterLen hLen in
    let acc = Buffer.sub #uint8 #(v stLen) #(v accLen) st (add #SIZE mgfseed_counterLen hLen) accLen in
    let c = Buffer.sub #uint8 #(v mgfseed_counterLen) #4 mgfseed_counter mgfseedLen (size 4) in

    c.(size 0) <- to_u8 #U32 (size_to_uint32 counter >>. u32 24);
    c.(size 1) <- to_u8 #U32 (size_to_uint32 counter >>. u32 16);
    c.(size 2) <- to_u8 #U32 (size_to_uint32 counter >>. u32 8);
    c.(size 3) <- to_u8 #U32 (size_to_uint32 counter);

    hash_sha256 mHash mgfseed_counterLen mgfseed_counter;
    let acc' = Buffer.sub #uint8 #(v accLen) #(v hLen) acc (mul #SIZE hLen counter) hLen in
    copy acc' hLen mHash
  ) st

val mgf_sha256:
  mgfseedLen:size_t{v mgfseedLen + 4 < max_size_t} -> mgfseed:lbytes mgfseedLen ->
  maskLen:size_t{0 < v maskLen /\ v mgfseedLen + 4 + v hLen + v (blocks maskLen hLen) * v hLen < pow2 32} ->
  res:lbytes maskLen -> Stack unit
  (requires (fun h -> live h mgfseed /\ live h res /\ disjoint res mgfseed))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
  [@"c_inline"]
let mgf_sha256 mgfseedLen mgfseed maskLen res =
  let count_max = blocks maskLen hLen in
  let accLen = mul #SIZE count_max hLen in
  let mgfseed_counterLen = add #SIZE mgfseedLen (size 4) in
  //st = [mgfseed_counter; hash(mgfseed_counter); acc]
  let stLen = add #SIZE (add #SIZE mgfseed_counterLen hLen) accLen in

  let h0 = FStar.HyperStack.ST.get () in
  alloc1 #h0 stLen (u8 0) res
  (fun h -> (fun _ r -> True))
  (fun st ->
    let mgfseed_counter = Buffer.sub #uint8 #(v stLen) #(v mgfseed_counterLen) st (size 0) mgfseed_counterLen in
    let mgfseed_st = Buffer.sub #uint8 #(v mgfseed_counterLen) #(v mgfseedLen) mgfseed_counter (size 0) mgfseedLen in
    copy mgfseed_st mgfseedLen mgfseed;
    mgf_sha256_ mgfseedLen accLen stLen st count_max;
    let acc = Buffer.sub #uint8 #(v stLen) #(v accLen) st (add #SIZE mgfseed_counterLen hLen) accLen in
    let acc1 = Buffer.sub #uint8 #(v accLen) #(v maskLen) acc (size 0) maskLen in
    copy res maskLen acc1
  )
