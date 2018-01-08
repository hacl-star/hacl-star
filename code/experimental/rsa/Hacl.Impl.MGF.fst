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
val mgf_:
    #accLen:size_nat -> #stLen:size_nat ->
    count_max:size_t ->
    mgfseed:lbytes (v hLen) ->
    aaccLen:size_t{v aaccLen == accLen /\  accLen = v hLen * v count_max} ->
    sstLen:size_t{v sstLen == stLen /\ stLen = v hLen + 4 + 4 + v hLen + accLen} -> st:lbytes stLen ->
    counter:size_t{v counter <= v count_max} -> Stack unit
    (requires (fun h -> live h mgfseed /\ live h st /\ disjoint st mgfseed))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st h0 h1))

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let rec mgf_ #accLen #stLen count_max mgfseed aaccLen sstLen st counter =
  if (counter <. count_max) then begin
     let mgfseed_counter = Buffer.sub #uint8 #stLen #(v hLen + 4) st (size 0) (add #SIZE hLen (size 4)) in
     let c = Buffer.sub #uint8 #stLen #4 st (add #SIZE hLen (size 4)) (size 4) in
     let mHash = Buffer.sub #uint8 #stLen #(v hLen) st (add #SIZE hLen (size 8)) hLen in
     let acc = Buffer.sub #uint8 #stLen #accLen st (add #SIZE (add #SIZE hLen (size 8)) hLen) aaccLen in
     c.(size 0) <- to_u8 #U32 (size_to_uint32 counter >>. u32 24);
     c.(size 1) <- to_u8 #U32 (size_to_uint32 counter >>. u32 16);
     c.(size 2) <- to_u8 #U32 (size_to_uint32 counter >>. u32 8);
     c.(size 3) <- to_u8 #U32 (size_to_uint32 counter);

     let mgfseed_counter_ = Buffer.sub #uint8 #(v hLen + 4) #4 mgfseed_counter hLen (size 4) in
     copy (size 4) c mgfseed_counter_;
     hash_sha256 mHash (add #SIZE hLen (size 4)) mgfseed_counter;
     let acc_ = Buffer.sub #uint8 #accLen #(v hLen) acc (mul #SIZE hLen counter) hLen in
     copy hLen mHash acc_;
     mgf_ #accLen #stLen count_max mgfseed aaccLen sstLen st (size_incr counter)
  end

val mgf_sha256:
    #len:size_nat ->
    mgfseed:lbytes (v hLen) ->
    clen:size_t{v clen == len /\ 0 < len /\ 8 + 2 * v hLen + v hLen * v (blocks clen hLen) < max_size_t} ->
    res:lbytes len -> Stack unit
    (requires (fun h -> live h mgfseed /\ live h res /\ disjoint res mgfseed))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
	
let mgf_sha256 #len mgfseed clen res =
    let count_max = blocks clen hLen in
    let accLen = mul #SIZE hLen count_max in
    let stLen = add #SIZE (add #SIZE (add #SIZE hLen (size 8)) hLen) accLen in
    
    alloc #uint8 #unit #(v stLen) stLen (u8 0) [BufItem mgfseed] [BufItem res]
    (fun h0 _ h1 -> True)
    (fun st ->
       let mgfseed_counter = Buffer.sub #uint8 #(v stLen) #(v hLen + 4) st (size 0) (add #SIZE hLen (size 4)) in
       let acc = Buffer.sub #uint8 #(v stLen) #(v accLen) st (add #SIZE (add #SIZE hLen (size 8)) hLen) accLen in
       let mgfseed_counter_ = Buffer.sub #uint8 #(v hLen + 4) #(v hLen) mgfseed_counter (size 0) hLen in
       copy hLen mgfseed mgfseed_counter_;
       mgf_ #(v accLen) #(v stLen) count_max mgfseed accLen stLen st (size 0);
       let acc_ = Buffer.sub #uint8 #(v accLen) #len acc (size 0) clen in
       copy clen acc_ res
    )
