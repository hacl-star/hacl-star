module MerkleTree.New.Low.Serialization

open FStar.Integers
open FStar.Mul
open LowStar.Modifies
open LowStar.BufferOps
open LowStar.Vector
open LowStar.RVector
open LowStar.Regional
open LowStar.Regional.Instances

open MerkleTree.New.Low

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

module B = LowStar.Buffer
module V = LowStar.Vector
module RV = LowStar.RVector
module RVI = LowStar.Regional.Instances

module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U8 = FStar.UInt8

let uint8_t = U8.t
let uint16_t = U16.t
let uint32_t = U32.t
let uint64_t = U64.t

let uint8_p = B.buffer uint8_t


#reset-options "--z3rlimit 5 --initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"

private let serialize_bool (ok:bool) (x:bool) (buf:uint8_p) (sz:uint32_t{B.len buf = sz}) (pos:uint32_t) : HST.ST (bool & uint32_t)
  (requires (fun h0 -> B.live h0 buf))
  (ensures (fun h0 _ h1 -> modifies (B.loc_buffer buf) h0 h1))
= if not ok || pos >= sz then (false, 0ul)
  else begin
    B.upd buf pos (if x then 1uy else 0uy);
    (true, pos + 1ul)
  end

private let serialize_uint8_t (ok:bool) (x:uint8_t) (buf:uint8_p) (sz:uint32_t{B.len buf = sz}) (pos:uint32_t) : HST.ST (bool & uint32_t)
  (requires (fun h0 -> B.live h0 buf))
  (ensures (fun h0 _ h1 -> modifies (B.loc_buffer buf) h0 h1))
= if not ok || pos >= sz then (false, 0ul)
  else begin B.upd buf pos x;
    (true, pos + 1ul)
  end

private let serialize_uint16_t (ok:bool) (x:uint16_t) (buf:uint8_p) (sz:uint32_t{B.len buf = sz}) (pos:uint32_t) : HST.ST (bool & uint32_t)
  (requires (fun h0 -> B.live h0 buf))
  (ensures (fun h0 _ h1 -> modifies (B.loc_buffer buf) h0 h1))
= let ok, pos = serialize_uint8_t ok (Int.Cast.uint16_to_uint8 (U16.shift_right x 8ul)) buf sz pos in
  serialize_uint8_t ok (Int.Cast.uint16_to_uint8 x) buf sz pos

private let serialize_uint32_t (ok:bool) (x:uint32_t) (buf:uint8_p) (sz:uint32_t{B.len buf = sz}) (pos:uint32_t) : HST.ST (bool & uint32_t)
  (requires (fun h0 -> B.live h0 buf))
  (ensures (fun h0 _ h1 -> modifies (B.loc_buffer buf) h0 h1))
= let ok, pos = serialize_uint16_t ok (Int.Cast.uint32_to_uint16 (U32.shift_right x 16ul)) buf sz pos in
  serialize_uint16_t ok (Int.Cast.uint32_to_uint16 x) buf sz pos

private let serialize_uint64_t (ok:bool) (x:uint64_t) (buf:uint8_p) (sz:uint32_t{B.len buf = sz}) (pos:uint32_t) : HST.ST (bool & uint32_t)
  (requires (fun h0 -> B.live h0 buf))
  (ensures (fun h0 _ h1 -> modifies (B.loc_buffer buf) h0 h1))
= let ok, pos = serialize_uint32_t ok (Int.Cast.uint64_to_uint32 (U64.shift_right x 32ul)) buf sz pos in
  serialize_uint32_t ok (Int.Cast.uint64_to_uint32 x) buf sz pos

private let serialize_offset_t = serialize_uint64_t
private let serialize_index_t = serialize_uint32_t

private let rec serialize_hash_i (ok:bool) (x:hash) (buf:uint8_p) (sz:uint32_t{B.len buf = sz}) (pos:uint32_t) (i:uint32_t{i < hash_size})
: HST.ST (bool & uint32_t)
    (requires (fun h0 -> B.live h0 buf /\ B.live h0 x /\ B.len x = hash_size))
    (ensures (fun h0 _ h1 -> modifies (B.loc_buffer buf) h0 h1))
= if not ok || pos >= sz then (false, 0ul)
  else let ok, pos = serialize_uint8_t ok (B.index x i) buf sz pos in
       let j = i + 1ul in
       if j < hash_size then serialize_hash_i ok x buf sz pos j
       else (ok, pos)
       
private let serialize_hash (ok:bool) (x:hash) (buf:uint8_p) (sz:uint32_t{B.len buf = sz}) (pos:uint32_t) : HST.ST (bool & uint32_t)
  (requires (fun h0 -> B.live h0 buf /\ B.live h0 x /\ B.len x = hash_size))
  (ensures (fun h0 _ h1 -> modifies (B.loc_buffer buf) h0 h1))
= if not ok || pos >= sz then (false, 0ul)
  else serialize_hash_i ok x buf sz pos 0ul

private 
inline_for_extraction
unfold let hash_vec_bytes (v:hash_vec) = 4UL + U64.mul (u32_64 (V.size_of v)) (u32_64 hash_size)

private let rec serialize_hash_vec_i (ok:bool) (x:hash_vec) (buf:uint8_p) (sz:uint32_t{B.len buf = sz}) (pos:uint32_t) (i:uint32_t{i < V.size_of x})
: HST.ST (bool & uint32_t)
  (requires (fun h0 -> B.live h0 buf /\ RV.rv_inv h0 x /\ loc_disjoint (B.loc_buffer buf) (loc_rvector x)))
  (ensures (fun h0 _ h1 -> RV.rv_inv h1 x /\ modifies (B.loc_buffer buf) h0 h1))
= if not ok || pos >= sz then (false, 0ul)
  else begin
    let vi = V.index x i in
    let ok, pos = serialize_hash ok vi buf sz pos in
    let j = i + 1ul in
    if j < V.size_of x then serialize_hash_vec_i ok x buf sz pos j
    else (ok, pos)
  end
  
private let serialize_hash_vec (ok:bool) (x:hash_vec) (buf:uint8_p) (sz:uint32_t{B.len buf = sz}) (pos:uint32_t) : HST.ST (bool & uint32_t)
  (requires (fun h0 -> B.live h0 buf /\ RV.rv_inv h0 x /\ HS.disjoint (B.frameOf buf) (Rgl?.region_of hvreg x)))
  (ensures (fun h0 _ h1 -> RV.rv_inv h1 x /\ modifies (B.loc_buffer buf) h0 h1))
= if not ok || pos >= sz then (false, 0ul)
  else begin
    let h0 = HST.get() in
    let ok, pos = serialize_uint32_t ok (V.size_of x) buf sz pos in
    let h1 = HST.get() in
    RV.rv_inv_preserved x (B.loc_buffer buf) h0 h1;
    if ok && V.size_of x > 0ul then serialize_hash_vec_i ok x buf sz pos 0ul
    else (ok, pos)
  end

private 
inline_for_extraction
let rec hash_vv_bytes_i (vv:hash_vv) (i:uint32_t): HST.ST uint64_t
    (requires (fun h0 -> V.live h0 vv))
    (ensures (fun h0 _ h1 -> h0 == h1))
  = if i >= V.size_of vv then 4UL
    else begin
      let vvi = V.index vv i in
      let r = hash_vec_bytes vvi in
      let rest = hash_vv_bytes_i vv (i+1ul) in
      if uint64_max - rest < r then uint64_max
      else rest + r
    end
    
private
inline_for_extraction
let rec hash_vv_bytes (vv:hash_vv{V.size_of vv = merkle_tree_size_lg}): HST.ST uint64_t
  (requires (fun h0 -> V.live h0 vv))
  (ensures (fun h0 _ h1 -> h0 == h1))
= hash_vv_bytes_i vv 0ul
                  
private let rec serialize_hash_vv_i (ok:bool) (x:hash_vv) (buf:uint8_p) (sz:uint32_t{B.len buf = sz}) (pos:uint32_t) (i:uint32_t{i < V.size_of x})
: HST.ST (bool & uint32_t)
  (requires (fun h0 -> B.live h0 buf /\ RV.rv_inv h0 x /\ HS.disjoint (B.frameOf buf) (Rgl?.region_of hvvreg x)))
  (ensures (fun h0 _ h1 -> modifies (B.loc_buffer buf) h0 h1))
= if not ok || pos >= sz then (false, 0ul)
  else begin
    let vi = V.index x i in
    let h0 = HST.get() in
    let ok, pos = serialize_hash_vec ok vi buf sz pos in
    let h1 = HST.get() in
    let j = i + 1ul in
    if j < V.size_of x then serialize_hash_vv_i ok x buf sz pos j
    else (ok, pos)
  end
      
private let serialize_hash_vv (ok:bool) (x:hash_vv) (buf:uint8_p) (sz:uint32_t{B.len buf = sz}) (pos:uint32_t): HST.ST (bool & uint32_t)
  (requires (fun h0 -> B.live h0 buf /\ RV.rv_inv h0 x /\ HS.disjoint (B.frameOf buf) (Rgl?.region_of hvvreg x)))
  (ensures (fun h0 _ h1 -> modifies (B.loc_buffer buf) h0 h1))
= if not ok || pos >= sz then (false, 0ul)
  else begin
    let h0 = HST.get() in
    let ok, pos = serialize_uint32_t ok (V.size_of x) buf sz pos in
    let h1 = HST.get() in
    RV.rv_inv_preserved x (B.loc_buffer buf) h0 h1;
    if (V.size_of x > 0ul) then serialize_hash_vv_i ok x buf sz pos 0ul
    else (ok, pos)
  end


private let deserialize_bool (ok:bool) (buf:uint8_p) (sz:uint32_t{B.len buf = sz}) (pos:uint32_t): HST.ST (bool & uint32_t & bool)
  (requires (fun h0 -> B.live h0 buf))
  (ensures  (fun h0 _ h1 -> h0 == h1))
= if not ok || pos >= sz then (false, pos, false)
  else (true, pos + 1ul, (match B.index buf pos with| 0uy -> false | _ -> true))

private let deserialize_uint8_t (ok:bool) (buf:uint8_p) (sz:uint32_t{B.len buf = sz}) (pos:uint32_t): HST.ST (bool & uint32_t & uint8_t)
  (requires (fun h0 -> B.live h0 buf))
  (ensures  (fun h0 _ h1 -> h0 == h1))
= if not ok || pos >= sz then (false, pos, 0uy)
  else (true, pos + 1ul, B.index buf pos)

private let deserialize_uint16_t (ok:bool) (buf:uint8_p) (sz:uint32_t{B.len buf = sz}) (pos:uint32_t): HST.ST (bool & uint32_t & uint16_t)
  (requires (fun h0 -> B.live h0 buf))
  (ensures  (fun h0 _ h1 -> h0 == h1))
= if not ok || pos >= sz then (false, pos, 0us)
  else begin
    let ok, pos, b0 = deserialize_uint8_t ok buf sz pos in
    let ok, pos, b1 = deserialize_uint8_t ok buf sz pos in
    (ok, pos, (U16.shift_left (Int.Cast.uint8_to_uint16 b0) 8ul) + Int.Cast.uint8_to_uint16 b1)
  end

private let deserialize_uint32_t (ok:bool) (buf:uint8_p) (sz:uint32_t{B.len buf = sz}) (pos:uint32_t): HST.ST (bool & uint32_t & uint32_t)
  (requires (fun h0 -> B.live h0 buf))
  (ensures  (fun h0 _ h1 -> h0 == h1))
= if not ok || pos >= sz then (false, pos, 0ul)
  else begin
    let ok, pos, b0 = deserialize_uint16_t ok buf sz pos in
    let ok, pos, b1 = deserialize_uint16_t ok buf sz pos in
    (ok, pos, (U32.shift_left (Int.Cast.uint16_to_uint32 b0) 16ul) + Int.Cast.uint16_to_uint32 b1)
  end

private let deserialize_uint64_t (ok:bool) (buf:uint8_p) (sz:uint32_t{B.len buf = sz}) (pos:uint32_t): HST.ST (bool & uint32_t & uint64_t)
  (requires (fun h0 -> B.live h0 buf))
  (ensures  (fun h0 _ h1 -> h0 == h1))
= if not ok || pos >= sz then (false, pos, 0UL)
  else begin
    let ok, pos, b0 = deserialize_uint32_t ok buf sz pos in
    let ok, pos, b1 = deserialize_uint32_t ok buf sz pos in
    (ok, pos, (U64.shift_left (u32_64 b0) 32ul) + u32_64 b1)
  end

private let deserialize_offset_t = deserialize_uint64_t
private let deserialize_index_t = deserialize_uint32_t

private let deserialize_hash (ok:bool) (buf:uint8_p) (sz:uint32_t{B.len buf = sz}) (r:HST.erid) (pos:uint32_t): HST.ST (bool & uint32_t & hash)
  (requires (fun h0 -> B.live h0 buf))
  (ensures (fun h0 (k, _, h) h1 -> (k ==> Rgl?.r_inv hreg h1 h) /\
                                   loc_disjoint (loc_buffer buf) (loc_buffer h) /\
                                   modifies B.loc_none h0 h1))
= if not ok || pos >= sz then (false, pos, Rgl?.dummy hreg)
  else if sz - pos < hash_size then (false, pos, Rgl?.dummy hreg)
  else begin
    let hash = Rgl?.r_alloc hreg r in
    B.blit buf pos hash 0ul hash_size;
    (true, pos + hash_size, hash)    
  end

private let rec deserialize_hash_vec_i (ok:bool) (buf:uint8_p) (sz:uint32_t{B.len buf = sz}) (r:HST.erid) (pos:uint32_t) (res:hash_vec) (i:uint32_t{i < V.size_of res})
: HST.ST (bool & uint32_t)
  (requires (fun h0 -> B.live h0 buf /\ V.live h0 res))
  (ensures (fun h0 _ h1 -> B.modifies (B.loc_buffer (V.Vec?.vs res)) h0 h1))
= if not ok || pos >= sz then (false, pos)
  else begin
    let ok, pos, h = deserialize_hash ok buf sz r pos in
    if not ok then (false, pos)
    else begin
      V.assign res i h;
      (*
       * AR: 04/01: The call deserialize_hash_vec_i below needs liveness of buf
       *            So we have to frame buf liveness for the V.assign call
       *            V.assign provides a modifies postcondition in terms of
       *              loc_vector_within, which is a recursive predicate and
       *              I guess hard to reason about directly
       *            Whereas to reason about liveness of buf, we only need an
       *              overapproximation that V.assign modifies V.Vec?.vs res
       *            Looking at the Vector library, I found the following lemma
       *              that does the trick
       *)      
      V.loc_vector_within_included res i (i + 1ul);
      let j = i + 1ul in
      if j < V.size_of res then deserialize_hash_vec_i ok buf sz r pos res j
      else (true, pos)
    end
  end

private let deserialize_hash_vec (ok:bool) (buf:uint8_p) (sz:uint32_t{B.len buf = sz}) (r:HST.erid) (pos:uint32_t): HST.ST (bool & uint32_t & hash_vec)
  (requires (fun h0 -> B.live h0 buf))
  (ensures (fun h0 _ h1 -> B.modifies B.loc_none h0 h1))
= if not ok || pos >= sz then (false, pos, Rgl?.dummy hvreg)
  else begin
    let ok, pos, n = deserialize_uint32_t ok buf sz pos in
    if not ok then (false, pos, V.alloc_empty hash)
    else if n = 0ul then (true, pos, V.alloc_empty hash)
    else begin
      let res = V.alloc n (Rgl?.dummy hreg) in
      let ok, pos = deserialize_hash_vec_i ok buf sz r pos res 0ul in
      (ok, pos, res)
    end
  end

private let rec deserialize_hash_vv_i (ok:bool) (buf:uint8_p) (sz:uint32_t{B.len buf = sz}) (r:HST.erid) (pos:uint32_t) (res:hash_vv) (i:uint32_t{i < V.size_of res})
: HST.ST (bool & uint32_t)
  (requires (fun h0 -> B.live h0 buf /\ V.live h0 res /\
                       B.loc_disjoint (B.loc_buffer buf) (V.loc_vector res)))
  (ensures (fun h0 _ h1 -> modifies (B.loc_buffer (V.Vec?.vs res)) h0 h1))
= 
  if not ok || pos >= sz then (false, 0ul)
  else begin
    let ok, pos, hv = deserialize_hash_vec ok buf sz r pos in
    let h0 = HST.get() in
    if not ok then (false, pos) 
    else begin
      V.assign res i hv;
      (*
       * AR: 04/01: The call deserialize_hash_vv_i below needs liveness of buf
       *            So we have to frame buf liveness for the V.assign call
       *            V.assign provides a modifies postcondition in terms of
       *              loc_vector_within, which is a recursive predicate and
       *              I guess hard to reason about directly
       *            Whereas to reason about liveness of buf, we only need an
       *              overapproximation that V.assign modifies V.Vec?.vs res
       *            Looking at the Vector library, I found the following lemma
       *              that does the trick
       *)      
      V.loc_vector_within_included res i (i + 1ul);
      let j = i + 1ul in
      if j = V.size_of res then (true, pos)
      else deserialize_hash_vv_i ok buf sz r pos res j      
    end
  end
  
private let deserialize_hash_vv (ok:bool) (buf:uint8_p) (sz:uint32_t{B.len buf = sz}) (r:HST.erid) (pos:uint32_t): HST.ST (bool & uint32_t & hash_vv)
  (requires (fun h0 -> B.live h0 buf))
  (ensures (fun h0 _ h1 -> modifies B.loc_none h0 h1))
= if not ok || pos >= sz then (false, pos, V.alloc_empty hash_vec)
  else begin
    let ok, pos, n = deserialize_uint32_t ok buf sz pos in
    if not ok then (false, pos, V.alloc_empty hash_vec)
    else if n = 0ul then (true, pos, V.alloc_empty hash_vec)
    else begin
      let res = V.alloc n (Rgl?.dummy hvreg) in
      let ok, pos = deserialize_hash_vv_i ok buf sz r pos res 0ul in
      (ok, pos, res)
    end
  end

#set-options "--z3rlimit 10"
val mt_serialize_size: mt:mt_p -> HST.ST uint64_t
  (requires (fun h0 -> mt_safe h0 mt))
  (ensures (fun _ _ h1 -> mt_safe h1 mt))
let mt_serialize_size mt =
  let mtv = !*mt in
  let hs = MT?.hs mtv in
  let rhs_ok = MT?.rhs_ok mtv in
  let rhs = MT?.rhs mtv in
  let hs_sz = hash_vv_bytes hs in
  if hs_sz < uint32_max then
    1UL +                // format version
    4UL +                // hash_size
    8UL +                // offset
    4UL + 4UL +          // i, j
    hs_sz +              // hs
    1UL +                // rhs_ok
    hash_vec_bytes rhs + // rhs
    u32_64 hash_size     // mroot
  else
    uint64_max
#reset-options

val mt_serialize: mt:mt_p -> output:uint8_p -> sz:uint32_t -> HST.ST uint32_t
  (requires (fun h0 -> mt_safe h0 mt /\ B.live h0 output /\ B.len output = sz /\ 
                       HS.disjoint (B.frameOf output) (B.frameOf mt)))
  (ensures (fun h0 _ h1 -> mt_safe h1 mt /\ modifies (B.loc_buffer output) h0 h1))
let mt_serialize mt output sz =
  let mtv = !*mt in
  let h0 = HST.get() in
  let ok, pos = serialize_uint8_t true 0uy output sz 0ul in // format version = 0uy
  let h1 = HST.get() in mt_safe_preserved mt (B.loc_buffer output) h0 h1;
  let ok, pos = serialize_uint32_t ok hash_size output sz pos in
  let h2 = HST.get() in mt_safe_preserved mt (B.loc_buffer output) h1 h2;
  let ok, pos = serialize_offset_t ok (MT?.offset mtv) output sz pos in
  let h3 = HST.get() in mt_safe_preserved mt (B.loc_buffer output) h2 h3;
  let ok, pos = serialize_uint32_t ok (MT?.i mtv) output sz pos in
  let h4 = HST.get() in mt_safe_preserved mt (B.loc_buffer output) h3 h4;
  let ok, pos = serialize_uint32_t ok (MT?.j mtv) output sz pos in
  let h5 = HST.get() in mt_safe_preserved mt (B.loc_buffer output) h4 h5;
  let ok, pos = serialize_hash_vv ok (MT?.hs mtv) output sz pos in
  let h6 = HST.get() in mt_safe_preserved mt (B.loc_buffer output) h5 h6;
  let ok, pos = serialize_bool ok (MT?.rhs_ok mtv) output sz pos in
  let h7 = HST.get() in mt_safe_preserved mt (B.loc_buffer output) h6 h7;
  let ok, pos = serialize_hash_vec ok (MT?.rhs mtv) output sz pos in
  let h8 = HST.get() in mt_safe_preserved mt (B.loc_buffer output) h7 h8;
  let ok, pos = serialize_hash ok (MT?.mroot mtv) output sz pos in
  let h9 = HST.get() in mt_safe_preserved mt (B.loc_buffer output) h8 h9;
  if ok then pos else 0ul

val mt_deserialize: rid:HST.erid -> input:uint8_p -> sz:uint32_t{B.len input = sz} -> HST.ST (B.pointer_or_null merkle_tree)
  (requires (fun h0 -> B.live h0 input /\ HS.disjoint rid (B.frameOf input)))
  (ensures (fun h0 r h1 -> modifies B.loc_none h0 h1))
let mt_deserialize rid input sz =
  let hrid = HST.new_region rid in
  let hvrid = HST.new_region rid in
  let hvvrid = HST.new_region rid in
  let ok, pos, format_version = deserialize_uint8_t true input sz 0ul in
  let ok, pos, hash_size = deserialize_uint32_t ok input sz pos in
  let ok, pos, offset = deserialize_offset_t ok input sz pos in
  let ok, pos, i = deserialize_index_t ok input sz pos in
  let ok, pos, j = deserialize_index_t ok input sz pos in
  let ok, pos, hs = deserialize_hash_vv ok input sz hvvrid pos in
  let ok, pos, rhs_ok = deserialize_bool ok input sz pos in
  let ok, pos, rhs = deserialize_hash_vec ok input sz hvrid pos in
  let ok, pos, mroot = deserialize_hash ok input sz hrid pos in
  begin
    if not ok || 
       hash_size <> MerkleTree.New.Low.hash_size ||
       not (merkle_tree_conditions offset i j hs rhs_ok rhs mroot)
    then B.null #merkle_tree
    else B.malloc rid (MT offset i j hs rhs_ok rhs mroot) 1ul
  end
