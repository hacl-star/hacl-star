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

private let serialize_bool (x:bool) (buf:uint8_p) (sz:uint32_t{B.len buf = sz}) (pos:uint32_t) : HST.ST (bool & uint32_t)
  (requires (fun h0 -> B.live h0 buf))
  (ensures (fun h0 _ h1 -> B.live h1 buf /\ modifies (B.loc_buffer buf) h0 h1))
= if pos >= sz then (false, 0ul)
  else begin
    B.upd buf pos (if x then 1uy else 0uy);
    (true, pos + 1ul)
  end

private let serialize_uint8_t (x:uint8_t) (buf:uint8_p) (sz:uint32_t{B.len buf = sz}) (pos:uint32_t) : HST.ST (bool & uint32_t)
  (requires (fun h0 -> B.live h0 buf))
  (ensures (fun h0 _ h1 -> B.live h1 buf /\ modifies (B.loc_buffer buf) h0 h1))
= if pos >= sz then (false, 0ul)
  else begin B.upd buf pos x;
    (true, pos + 1ul)
  end

private let serialize_uint16_t (x:uint16_t) (buf:uint8_p) (sz:uint32_t{B.len buf = sz}) (pos:uint32_t) : HST.ST (bool & uint32_t)
  (requires (fun h0 -> B.live h0 buf))
  (ensures (fun h0 _ h1 -> B.live h1 buf /\ modifies (B.loc_buffer buf) h0 h1))
= let _, pos = serialize_uint8_t (Int.Cast.uint16_to_uint8 (U16.shift_right x 8ul)) buf sz pos in
  serialize_uint8_t (Int.Cast.uint16_to_uint8 x) buf sz pos

private let serialize_uint32_t (x:uint32_t) (buf:uint8_p) (sz:uint32_t{B.len buf = sz}) (pos:uint32_t) : HST.ST (bool & uint32_t)
  (requires (fun h0 -> B.live h0 buf))
  (ensures (fun h0 _ h1 -> B.live h1 buf /\ modifies (B.loc_buffer buf) h0 h1))
= let _, pos = serialize_uint16_t (Int.Cast.uint32_to_uint16 (U32.shift_right x 16ul)) buf sz pos in
  serialize_uint16_t (Int.Cast.uint32_to_uint16 x) buf sz pos

private let serialize_uint64_t (x:uint64_t) (buf:uint8_p) (sz:uint32_t{B.len buf = sz}) (pos:uint32_t) : HST.ST (bool & uint32_t)
  (requires (fun h0 -> B.live h0 buf))
  (ensures (fun h0 _ h1 -> B.live h1 buf /\ modifies (B.loc_buffer buf) h0 h1))
= let _, pos = serialize_uint32_t (Int.Cast.uint64_to_uint32 (U64.shift_right x 32ul)) buf sz pos in
  serialize_uint32_t (Int.Cast.uint64_to_uint32 x) buf sz pos

private let serialize_offset_t = serialize_uint64_t
private let serialize_index_t = serialize_uint32_t

private let serialize_hash (x:hash) (buf:uint8_p) (sz:uint32_t{B.len buf = sz}) (pos:uint32_t) : HST.ST (bool & uint32_t)
  (requires (fun h0 -> B.live h0 buf /\ B.live h0 x /\ B.len x = hash_size))
  (ensures (fun h0 _ h1 -> B.live h1 buf /\ B.live h1 x /\ modifies (B.loc_buffer buf) h0 h1))
= if pos >= sz then (false, 0ul)
  else begin
    let rec serialize_hash_i pos (i:uint32_t): HST.ST (bool & uint32_t)
        (requires (fun h0 -> B.live h0 buf /\ B.live h0 x /\ B.len x = hash_size))
        (ensures (fun h0 _ h1 -> B.live h1 buf /\ B.live h1 x /\ modifies (B.loc_buffer buf) h0 h1))
    = if pos >= sz then (false, 0ul)
      else if i >= hash_size then (true, pos)
      else begin
        let _, pos = serialize_uint8_t (B.index x i) buf sz pos in
        serialize_hash_i pos (i+1ul)
      end in
    serialize_hash_i pos 0ul
  end

private unfold let hash_vec_bytes (v:hash_vec) = 4UL + U64.mul (u32_64 (V.size_of v)) (u32_64 hash_size)

private let serialize_hash_vec (x:hash_vec) (buf:uint8_p) (sz:uint32_t{B.len buf = sz}) (pos:uint32_t) : HST.ST (bool & uint32_t)
  (requires (fun h0 -> B.live h0 buf /\ RV.rv_inv h0 x /\ HS.disjoint (B.frameOf buf) (Rgl?.region_of hvreg x)))
  (ensures (fun h0 _ h1 -> B.live h1 buf /\ RV.rv_inv h1 x /\ modifies (B.loc_buffer buf) h0 h1))
= if pos >= sz then (false, 0ul)
  else begin
    let rec serialize_hash_vec_i pos (i:uint32_t): HST.ST (bool & uint32_t)
      (requires (fun h0 -> B.live h0 buf /\ RV.rv_inv h0 x))
      (ensures (fun h0 _ h1 -> B.live h1 buf /\ RV.rv_inv h1 x /\ modifies (B.loc_buffer buf) h0 h1))
    = if pos >= sz then (false, 0ul)
      else if i >= V.size_of x then (true, pos)
      else begin
        let vi = V.index x i in
        let h0 = HST.get() in
        let _, pos = serialize_hash vi buf sz pos in
        let h1 = HST.get() in
        RV.rv_inv_preserved x (B.loc_buffer buf) h0 h1;
        serialize_hash_vec_i pos (i+1ul)
      end in
    let h0 = HST.get() in
    let _, pos = serialize_uint32_t (V.size_of x) buf sz pos in
    let h1 = HST.get() in
    RV.rv_inv_preserved x (B.loc_buffer buf) h0 h1;
    serialize_hash_vec_i pos 0ul
  end

private let rec hash_vv_bytes (vv:hash_vv{V.size_of vv = merkle_tree_size_lg}): HST.ST uint64_t
  (requires (fun h0 -> V.live h0 vv))
  (ensures (fun h0 _ h1 -> h0 == h1 /\ V.live h1 vv))
= let rec hash_vv_bytes_i (vv:hash_vv) (i:uint32_t): HST.ST uint64_t
    (requires (fun h0 -> V.live h0 vv))
    (ensures (fun h0 _ h1 -> h0 == h1 /\ V.live h1 vv))
  = if i >= V.size_of vv then 4UL
    else begin
      let vvi = V.index vv i in
      let r = hash_vec_bytes vvi in
      let rest = hash_vv_bytes_i vv (i+1ul) in
      if uint64_max - rest < r then uint64_max
      else rest + r
    end in
  hash_vv_bytes_i vv 0ul

private let serialize_hash_vv (x:hash_vv) (buf:uint8_p) (sz:uint32_t{B.len buf = sz}) (pos:uint32_t): HST.ST (bool & uint32_t)
  (requires (fun h0 -> B.live h0 buf /\ RV.rv_inv h0 x /\ HS.disjoint (B.frameOf buf) (Rgl?.region_of hvvreg x)))
  (ensures (fun h0 _ h1 -> B.live h1 buf /\ RV.rv_inv h1 x /\ modifies (B.loc_buffer buf) h0 h1))
= if pos >= sz then (false, 0ul)
  else begin
    let rec serialize_hash_vv_i pos (i:uint32_t): HST.ST (bool & uint32_t)
      (requires (fun h0 -> B.live h0 buf /\ RV.rv_inv h0 x /\ HS.disjoint (B.frameOf buf) (Rgl?.region_of hvvreg x)))
      (ensures (fun h0 _ h1 -> B.live h1 buf /\ RV.rv_inv h1 x /\ modifies (B.loc_buffer buf) h0 h1))
    = if pos >= sz then (false, 0ul)
      else if i >= V.size_of x then (true, pos)
      else begin
        let vi = V.index x i in
        let h0 = HST.get() in
        let _, pos = serialize_hash_vec vi buf sz pos in
        let h1 = HST.get() in
        RV.rv_inv_preserved x (B.loc_buffer buf) h0 h1;
        serialize_hash_vv_i pos (i+1ul)
      end in
    let h0 = HST.get() in
    let _, pos = serialize_uint32_t (V.size_of x) buf sz pos in
    let h1 = HST.get() in
    RV.rv_inv_preserved x (B.loc_buffer buf) h0 h1;
    serialize_hash_vv_i pos 0ul
  end

private let deserialize_bool (buf:uint8_p) (sz:uint32_t{B.len buf = sz}) (pos:uint32_t): HST.ST (bool & uint32_t & bool)
  (requires (fun h0 -> B.live h0 buf))
  (ensures (fun _ _ h1 -> B.live h1 buf))
= if pos >= sz then (false, pos, false)
  else (true, pos + 1ul, (match B.index buf pos with| 0uy -> false | _ -> true))

private let deserialize_uint8_t (buf:uint8_p) (sz:uint32_t{B.len buf = sz}) (pos:uint32_t): HST.ST (bool & uint32_t & uint8_t)
  (requires (fun h0 -> B.live h0 buf))
  (ensures (fun _ _ h1 -> B.live h1 buf))
= if pos >= sz then (false, pos, 0uy)
  else (true, pos + 1ul, B.index buf pos)

private let deserialize_uint16_t (buf:uint8_p) (sz:uint32_t{B.len buf = sz}) (pos:uint32_t): HST.ST (bool & uint32_t & uint16_t)
  (requires (fun h0 -> B.live h0 buf))
  (ensures (fun _ _ h1 -> B.live h1 buf))
= if pos >= sz then (false, pos, 0us)
  else begin
    let _, pos, b0 = deserialize_uint8_t buf sz pos in
    let k, pos, b1 = deserialize_uint8_t buf sz pos in
    (k, pos, (U16.shift_left (Int.Cast.uint8_to_uint16 b0) 8ul) + Int.Cast.uint8_to_uint16 b1)
  end

private let deserialize_uint32_t (buf:uint8_p) (sz:uint32_t{B.len buf = sz}) (pos:uint32_t): HST.ST (bool & uint32_t & uint32_t)
  (requires (fun h0 -> B.live h0 buf))
  (ensures (fun _ _ h1 -> B.live h1 buf))
= if pos >= sz then (false, pos, 0ul)
  else begin
    let _, pos, b0 = deserialize_uint16_t buf sz pos in
    let k, pos, b1 = deserialize_uint16_t buf sz pos in
    (k, pos, (U32.shift_left (Int.Cast.uint16_to_uint32 b0) 16ul) + Int.Cast.uint16_to_uint32 b1)
  end

private let deserialize_uint64_t (buf:uint8_p) (sz:uint32_t{B.len buf = sz}) (pos:uint32_t): HST.ST (bool & uint32_t & uint64_t)
  (requires (fun h0 -> B.live h0 buf))
  (ensures (fun _ _ h1 -> B.live h1 buf))
= if pos >= sz then (false, pos, 0UL)
  else begin
    let _, pos, b0 = deserialize_uint32_t buf sz pos in
    let k, pos, b1 = deserialize_uint32_t buf sz pos in
    (k, pos, (U64.shift_left (u32_64 b0) 32ul) + u32_64 b1)
  end

private let deserialize_offset_t = deserialize_uint64_t
private let deserialize_index_t = deserialize_uint32_t

private let deserialize_hash (buf:uint8_p) (sz:uint32_t{B.len buf = sz}) (r:HST.erid) (pos:uint32_t): HST.ST (bool & uint32_t & hash)
  (requires (fun h0 -> B.live h0 buf /\ HS.disjoint (B.frameOf buf) r))
  (ensures (fun h0 _ h1 -> B.live h1 buf))
= if pos >= sz then (false, pos, Rgl?.dummy hreg)
  else if sz - pos < hash_size then (false, pos, Rgl?.dummy hreg)
  else begin
    let h0 = HST.get() in
    let hash = Rgl?.r_alloc hreg r in
    B.blit buf pos hash 0ul hash_size;
    (true, pos, hash)
  end

// joonwonc: there is a quite hard disjointness problem here; need to talk about it.
private let deserialize_hash_vec (buf:uint8_p) (sz:uint32_t{B.len buf = sz}) (r:HST.erid) (pos:uint32_t): HST.ST (bool & uint32_t & hash_vec)
  (requires (fun h0 -> B.live h0 buf /\ HS.disjoint (B.frameOf buf) r))
  (ensures (fun h0 _ h1 -> B.live h1 buf))
= if pos >= sz then (false, pos, Rgl?.dummy hvreg)
  else begin
    let _, pos, n = deserialize_uint32_t buf sz pos in
    if n = 0ul then (false, pos, V.alloc_empty hash)
    else begin
      let res = V.alloc n (Rgl?.dummy hreg) in
      let rec deserialize_hash_vec_i pos (i:uint32_t): HST.ST (bool & uint32_t)
        (requires (fun h0 -> B.live h0 buf))
        (ensures (fun h0 _ h1 -> B.live h1 buf))
      = if i >= V.size_of res then (true, pos)
        else begin
          let _, pos, h = deserialize_hash buf sz r pos in
          let h0 = HST.get() in
          assume (V.live h0 res);
          V.assign res i h;
          let h1 = HST.get() in
          assume (B.live h1 buf);
          deserialize_hash_vec_i pos (i+1ul)
        end
      in
      let k, pos = deserialize_hash_vec_i pos 0ul in
      (k, pos, res)
    end
  end

private let deserialize_hash_vv (buf:uint8_p) (sz:uint32_t{B.len buf = sz}) (r:HST.erid) (pos:uint32_t): HST.ST (bool & uint32_t & hash_vv)
  (requires (fun h0 -> B.live h0 buf /\ HS.disjoint (B.frameOf buf) r))
  (ensures (fun h0 _ h1 -> B.live h1 buf))
= if pos >= sz then (false, pos, Rgl?.dummy hvvreg)
  else begin
    let _, pos, n = deserialize_uint32_t buf sz pos in
    if n = 0ul then (false, pos, V.alloc_empty hash_vec)
    else begin
      let res = V.alloc n (Rgl?.dummy hvreg) in
      let rec deserialize_hash_vv_i pos (i:uint32_t): HST.ST (bool & uint32_t)
        (requires (fun h0 -> B.live h0 buf))
        (ensures (fun h0 _ h1 -> B.live h1 buf))
      = if i >= V.size_of res then (true, pos)
        else begin
          let _, pos, hv = deserialize_hash_vec buf sz r pos in
          let h0 = HST.get() in
          assume (V.live h0 res);
          V.assign res i hv;
          let h1 = HST.get() in
          assume (B.live h1 buf);
          deserialize_hash_vv_i pos (i+1ul)
      end in
    let k, pos = deserialize_hash_vv_i pos 0ul in
    (k, pos, res)
    end
  end

val mt_serialize_size: mt:mt_p -> HST.ST uint64_t
  (requires (fun h0 -> mt_safe h0 mt))
  (ensures (fun _ _ h1 -> True))
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

#set-options "--z3rlimit 10"
val mt_serialize: mt:mt_p -> output:uint8_p -> sz:uint32_t -> HST.ST uint32_t
  (requires (fun h0 -> mt_safe h0 mt /\ B.live h0 output /\ B.len output = sz /\ 
                       HS.disjoint (B.frameOf output) (B.frameOf mt)))
  (ensures (fun h0 _ h1 -> mt_safe h1 mt /\ B.live h1 output))
let mt_serialize mt output sz =
  let mtv = !*mt in
  let h0 = HST.get() in
  let _, pos = serialize_uint8_t 0uy output sz 0ul in // format version = 0uy
  let h1 = HST.get() in mt_safe_preserved mt (B.loc_buffer output) h0 h1;
  let _, pos = serialize_uint32_t hash_size output sz pos in
  let h2 = HST.get() in mt_safe_preserved mt (B.loc_buffer output) h1 h2;
  let _, pos = serialize_offset_t (MT?.offset mtv) output sz pos in
  let h3 = HST.get() in mt_safe_preserved mt (B.loc_buffer output) h2 h3;
  let _, pos = serialize_uint32_t (MT?.i mtv) output sz pos in
  let h4 = HST.get() in mt_safe_preserved mt (B.loc_buffer output) h3 h4;
  let _, pos = serialize_uint32_t (MT?.j mtv) output sz pos in
  let h5 = HST.get() in mt_safe_preserved mt (B.loc_buffer output) h4 h5;
  let _, pos = serialize_hash_vv (MT?.hs mtv) output sz pos in
  let h6 = HST.get() in mt_safe_preserved mt (B.loc_buffer output) h5 h6;
  let _, pos = serialize_bool (MT?.rhs_ok mtv) output sz pos in
  let h7 = HST.get() in mt_safe_preserved mt (B.loc_buffer output) h6 h7;
  let _, pos = serialize_hash_vec (MT?.rhs mtv) output sz pos in
  let h8 = HST.get() in mt_safe_preserved mt (B.loc_buffer output) h7 h8;
  let k, pos = serialize_hash (MT?.mroot mtv) output sz pos in
  let h9 = HST.get() in mt_safe_preserved mt (B.loc_buffer output) h8 h9;
  if k then pos else 0ul

val mt_deserialize: rid:HST.erid -> input:uint8_p -> sz:uint32_t{B.len input = sz} -> HST.ST (B.pointer_or_null merkle_tree)
  (requires (fun h0 -> B.live h0 input /\ HS.disjoint (B.frameOf input) rid))
  (ensures (fun _ _ h1 -> B.live h1 input))
let mt_deserialize rid input sz =
  let _, pos, format_version = deserialize_uint8_t input sz 0ul in
  let _, pos, hash_size = deserialize_uint32_t input sz pos in
  let _, pos, offset = deserialize_offset_t input sz pos in
  let _, pos, i = deserialize_index_t input sz pos in
  let _, pos, j = deserialize_index_t input sz pos in
  let _, ops, hs = deserialize_hash_vv input sz rid pos in
  let _, pos, rhs_ok = deserialize_bool input sz pos in
  let _, pos, rhs = deserialize_hash_vec input sz rid pos in
  let k, pos, mroot = deserialize_hash input sz rid pos in
  begin
    if not k || not (merkle_tree_conditions offset i j hs rhs_ok rhs mroot)
    then B.null #merkle_tree
    else B.malloc rid (MT offset i j hs rhs_ok rhs mroot) 1ul
  end

