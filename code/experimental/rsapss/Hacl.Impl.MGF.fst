module Hacl.Impl.MGF

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Lib

module ST = FStar.HyperStack.ST

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

(* SHA 256 *)
inline_for_extraction
let hLen = 32ul

val hash_sha256:
    mHash:lbytes hLen
  -> len:size_t
  -> m:lbytes len
  -> Stack unit
    (requires fun h -> live h mHash /\ live h m /\ disjoint m mHash)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer mHash) h0 h1)
let hash_sha256 mHash len m = Hacl.SHA256.hash mHash len m
//SHA2_256.hash mHash m clen

(* Mask Generation Function *)
inline_for_extraction noextract
val mgf_sha256_:
    mgfseedLen:size_t
  -> accLen:size_t
  -> stLen:size_t{v stLen = v mgfseedLen + 4 + v hLen + v accLen}
  -> st:lbytes stLen
  -> count_max:size_t{v accLen = v count_max * v hLen}
  -> Stack unit
    (requires fun h -> live h st)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer st) h0 h1)
let mgf_sha256_ mgfseedLen accLen stLen st count_max =
  let h0 = ST.get () in
  let inv h1 i = modifies (loc_buffer st) h0 h1 in
  Lib.Loops.for 0ul count_max inv
  (fun counter ->
    let mgfseed_counterLen = mgfseedLen +. 4ul in
    let mgfseed_counter = sub st 0ul mgfseed_counterLen in
    let mHash = sub st mgfseed_counterLen hLen in
    let acc = sub st (mgfseed_counterLen +. hLen) accLen in
    let c = sub #_ #(v mgfseed_counterLen) #4 mgfseed_counter mgfseedLen 4ul in

    c.(0ul) <- to_u8 (counter >>. 24ul);
    c.(1ul) <- to_u8 (counter >>. 16ul);
    c.(2ul) <- to_u8 (counter >>. 8ul);
    c.(3ul) <- to_u8 counter;

    hash_sha256 mHash mgfseed_counterLen mgfseed_counter;
    let acc' = sub #_ #(v accLen) acc (hLen *. counter) hLen in
    copy acc' hLen mHash
  )

val mgf_sha256:
    mgfseedLen:size_t{v mgfseedLen + 4 < max_size_t}
  -> mgfseed:lbytes mgfseedLen
  -> maskLen:size_t{0 < v maskLen /\ v mgfseedLen + 4 + v hLen + v (blocks maskLen hLen) * v hLen < pow2 32}
  -> res:lbytes maskLen
  -> Stack unit
    (requires fun h -> live h mgfseed /\ live h res /\ disjoint res mgfseed)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer res) h0 h1)
[@"c_inline"]
let mgf_sha256 mgfseedLen mgfseed maskLen res =
  push_frame ();
  let count_max = blocks maskLen hLen in
  let accLen = count_max *. hLen in
  let mgfseed_counterLen = mgfseedLen +. 4ul in
  //st = [mgfseed_counter; hash(mgfseed_counter); acc]
  let stLen = mgfseed_counterLen +. hLen +. accLen in
  let st = create stLen (u8 0) in
  let mgfseed_counter = sub st 0ul mgfseed_counterLen in
  let mgfseed_st = sub #_ #(v mgfseed_counterLen) mgfseed_counter 0ul mgfseedLen in
  copy mgfseed_st mgfseedLen mgfseed;
  mgf_sha256_ mgfseedLen accLen stLen st count_max;
  let acc = sub st (mgfseed_counterLen +. hLen) accLen in
  let acc1 = sub #_ #(v accLen) acc 0ul maskLen in
  copy res maskLen acc1;
  pop_frame ()
