module Hacl.Impl.MGF

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Lib

module ST = FStar.HyperStack.ST
module S = Spec.RSAPSS

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

(* SHA 256 *)
inline_for_extraction
let hLen = 32ul

val hash_sha256:
    mHash:lbuffer uint8 hLen
  -> msg_len:size_t{v msg_len < S.max_input}
  -> msg:lbuffer uint8 msg_len ->
  Stack unit
  (requires fun h -> live h mHash /\ live h msg /\ disjoint msg mHash)
  (ensures  fun h0 _ h1 -> modifies (loc mHash) h0 h1 /\
    as_seq h1 mHash == S.sha2_256 (as_seq h0 msg))
let hash_sha256 mHash msg_len msg =
  Hacl.Hash.SHA2.hash_256 msg msg_len mHash


(* Mask Generation Function *)
inline_for_extraction noextract
val mgf_sha256_:
    mgfseedLen:size_t
  -> accLen:size_t
  -> stLen:size_t{v stLen = v mgfseedLen + 4 + v hLen + v accLen}
  -> st:lbuffer uint8 stLen
  -> count_max:size_t{v accLen = v count_max * v hLen}
  -> Stack unit
    (requires fun h -> live h st)
    (ensures  fun h0 _ h1 -> modifies (loc st) h0 h1)
let mgf_sha256_ mgfseedLen accLen stLen st count_max = admit();
  let h0 = ST.get () in
  let inv h1 i = modifies (loc st) h0 h1 in
  Lib.Loops.for 0ul count_max inv
  (fun counter ->
    let mgfseed_counterLen = mgfseedLen +. 4ul in
    let mgfseed_counter = sub st 0ul mgfseed_counterLen in
    let mHash = sub st mgfseed_counterLen hLen in
    let acc = sub st (mgfseed_counterLen +. hLen) accLen in
    let c = sub mgfseed_counter mgfseedLen 4ul in

    c.(0ul) <- to_u8 (counter >>. 24ul);
    c.(1ul) <- to_u8 (counter >>. 16ul);
    c.(2ul) <- to_u8 (counter >>. 8ul);
    c.(3ul) <- to_u8 counter;

    hash_sha256 mHash mgfseed_counterLen mgfseed_counter;
    let acc' = sub acc (hLen *. counter) hLen in
    copy acc' mHash
  )

val mgf_sha256:
    mgfseedLen:size_t{v mgfseedLen + 4 < max_size_t}
  -> mgfseed:lbuffer uint8 mgfseedLen
  -> maskLen:size_t{0 < v maskLen /\ v mgfseedLen + 4 + v hLen + v (blocks maskLen hLen) * v hLen < pow2 32}
  -> res:lbuffer uint8 maskLen
  -> Stack unit
    (requires fun h -> live h mgfseed /\ live h res /\ disjoint res mgfseed)
    (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1)
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
  let mgfseed_st = sub mgfseed_counter 0ul mgfseedLen in
  copy mgfseed_st mgfseed;
  mgf_sha256_ mgfseedLen accLen stLen st count_max;
  let acc = sub st (mgfseed_counterLen +. hLen) accLen in
  let acc1 = sub acc 0ul maskLen in
  copy res acc1;
  pop_frame ()
