module Hacl.Impl.MGF

open FStar.HyperStack.All
open Spec.Lib.IntBuf.Lemmas
open Spec.Lib.IntBuf
open Spec.Lib.IntTypes
open FStar.Mul

open Hacl.Impl.Lib
open Hacl.Impl.Convert

module Buffer = Spec.Lib.IntBuf

(* SHA 256 *)
inline_for_extraction
let hLen:size_t = size 32

assume val hash_sha256:
  #len:size_nat ->
  mHash:lbytes (v hLen) ->
  clen:size_t{v clen == len} ->
  m:lbytes len -> Stack unit
  (requires (fun h -> live h mHash /\ live h m /\ disjoint m mHash))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 mHash h0 h1))
//let hash_sha256 #len mHash clen m = SHA2_256.hash mHash m clen

(* Mask Generation Function *)
val mgf_sha256_:
  #stLen:size_nat -> mgfseedLen:size_t -> accLen:size_t ->
  sstLen:size_t{v sstLen = stLen /\ stLen = v mgfseedLen + 4 + v hLen + v accLen} ->
  st:lbytes stLen -> count_max:size_t{v accLen = v count_max * v hLen} -> Stack unit
  (requires (fun h -> live h st))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st h0 h1))
  [@ "substitute"]
let mgf_sha256_ #stLen mgfseedLen accLen sstLen st count_max =
  iteri_simple #uint8 #stLen count_max
  (fun counter st ->
    let mgfseed_counterLen = add #SIZE mgfseedLen (size 4) in
    let mgfseed_counter = Buffer.sub #uint8 #stLen #(v mgfseed_counterLen) st (size 0) mgfseed_counterLen in
    let mHash = Buffer.sub #uint8 #stLen #(v hLen) st mgfseed_counterLen hLen in
    let acc = Buffer.sub #uint8 #stLen #(v accLen) st (add #SIZE mgfseed_counterLen hLen) accLen in
    let c = Buffer.sub #uint8 #(v mgfseed_counterLen) #4 mgfseed_counter mgfseedLen (size 4) in

    c.(size 0) <- to_u8 #U32 (size_to_uint32 counter >>. u32 24);
    c.(size 1) <- to_u8 #U32 (size_to_uint32 counter >>. u32 16);
    c.(size 2) <- to_u8 #U32 (size_to_uint32 counter >>. u32 8);
    c.(size 3) <- to_u8 #U32 (size_to_uint32 counter);

    hash_sha256 mHash mgfseed_counterLen mgfseed_counter;
    let acc' = Buffer.sub #uint8 #(v accLen) #(v hLen) acc (mul #SIZE hLen counter) hLen in
    copy hLen mHash acc'
  ) st

val mgf_sha256:
  #mgfseedLen:size_nat{mgfseedLen + 4 < max_size_t} -> #maskLen:size_nat ->
  mmgfseedLen:size_t{v mmgfseedLen = mgfseedLen} -> mgfseed:lbytes mgfseedLen ->
  mmaskLen:size_t{v mmaskLen = maskLen /\ 0 < maskLen /\ mgfseedLen + 4 + v hLen + v (blocks mmaskLen hLen) * v hLen < pow2 32} ->
  res:lbytes maskLen -> Stack unit
  (requires (fun h -> live h mgfseed /\ live h res /\ disjoint res mgfseed))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
  [@"c_inline"]
let mgf_sha256 #mgfseedLen #maskLen mmgfseedLen mgfseed mmaskLen res =
  let count_max = blocks mmaskLen hLen in
  let accLen = mul #SIZE count_max hLen in
  let mgfseed_counterLen = add #SIZE mmgfseedLen (size 4) in
  //st = [mgfseed_counter; hash(mgfseed_counter); acc]
  let stLen = add #SIZE (add #SIZE mgfseed_counterLen hLen) accLen in

  alloc #uint8 #unit #(v stLen) stLen (u8 0) [BufItem mgfseed] [BufItem res]
  (fun h0 _ h1 -> True)
  (fun st ->
    let mgfseed_counter = Buffer.sub #uint8 #(v stLen) #(v mgfseed_counterLen) st (size 0) mgfseed_counterLen in
    let mgfseed_st = Buffer.sub #uint8 #(v mgfseed_counterLen) #mgfseedLen mgfseed_counter (size 0) mmgfseedLen in
    copy mmgfseedLen mgfseed mgfseed_st;
    mgf_sha256_ #(v stLen) mmgfseedLen accLen stLen st count_max;
    let acc = Buffer.sub #uint8 #(v stLen) #(v accLen) st (add #SIZE mgfseed_counterLen hLen) accLen in
    let acc1 = Buffer.sub #uint8 #(v accLen) #maskLen acc (size 0) mmaskLen in
    copy mmaskLen acc1 res
  )
