module Hacl.Impl.RSA

open FStar.HyperStack.All
open FStar.Mul
open Spec.Lib.Loops
open Spec.Lib.IntBuf.Lemmas
open Spec.Lib.IntBuf
open Spec.Lib.IntTypes

open Hacl.Impl.Lib
open Hacl.Impl.MGF
open Hacl.Impl.Comparison
open Hacl.Impl.Convert
open Hacl.Impl.Exponentiation

module Buffer = Spec.Lib.IntBuf

inline_for_extraction let hLen:size_t = size 32

val xor_bytes:
    #len:size_nat ->
    clen:size_t{v clen == len} ->
    b1:lbytes len ->
    b2:lbytes len -> Stack unit
    (requires (fun h -> live h b1 /\ live h b2))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 b1 h0 h1))
let xor_bytes #len clen b1 b2 = map2 #uint8 #uint8 #len clen (fun x y -> logxor #U8 x y) b1 b2

val pss_encode_in:
    #sLen:size_nat -> #msgLen:size_nat -> #emLen:size_nat -> #stLen:size_nat ->
    ssLen:size_t{v ssLen == sLen /\ sLen + v hLen + 8 < max_size_t} -> salt:lbytes sLen ->
    mmsgLen:size_t{v mmsgLen == msgLen} -> msg:lbytes msgLen ->
    eemLen:size_t{v eemLen == emLen /\ emLen - sLen - v hLen - 2 >= 0} ->
    m1_size:size_t{v m1_size = 8 + v hLen + sLen} -> 
    db_size:size_t{v db_size = emLen - v hLen - 1} ->
    sstLen:size_t{v sstLen == stLen /\ stLen = v hLen + v m1_size + v hLen + v db_size + v db_size} -> st:lbytes stLen -> Stack unit
    (requires (fun h -> live h salt /\ live h msg /\ live h st /\ disjoint st msg /\ disjoint st salt /\ disjoint msg salt))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st h0 h1))

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"
[@ "substitute"]
let pss_encode_in #sLen #msgLen #emLen #stLen ssLen salt mmsgLen msg eemLen m1_size db_size sstLen st =
    let mHash = Buffer.sub #uint8 #stLen #(v hLen) st (size 0) hLen in
    disjoint_sub_lemma1 st msg (size 0) hLen;
    hash_sha256 mHash mmsgLen msg;
    
    let m1 = Buffer.sub #uint8 #stLen #(v m1_size) st hLen m1_size in
    let m1_ = Buffer.sub #uint8 #(v m1_size) #(v hLen) m1 (size 8) hLen in
    copy hLen mHash m1_;
    let m1_ = Buffer.sub #uint8 #(v m1_size) #sLen m1 (add #SIZE (size 8) hLen) ssLen in
    copy ssLen salt m1_;
    
    let m1Hash = Buffer.sub #uint8 #stLen #(v hLen) st (add #SIZE hLen m1_size) hLen in
    hash_sha256 m1Hash m1_size m1;
    
    let db = Buffer.sub #uint8 #stLen #(v db_size) st (add #SIZE (add #SIZE hLen m1_size) hLen) db_size in
    let last_before_salt = sub #SIZE (sub #SIZE db_size ssLen) (size 1) in
    db.(last_before_salt) <- u8 1;
    let db_ = Buffer.sub #uint8 #(v db_size) #sLen db (size_incr last_before_salt) ssLen in
    copy ssLen salt db_;
    
    let dbMask = Buffer.sub #uint8 #stLen #(v db_size) st (add #SIZE (add #SIZE (add #SIZE hLen m1_size) hLen) db_size) db_size in
    assume (8 + 2 * v hLen + v hLen * v (blocks db_size hLen) < max_size_t);
    mgf_sha256 m1Hash db_size dbMask;
    xor_bytes db_size db dbMask

  
val pss_encode_:
    #sLen:size_nat -> #msgLen:size_nat -> #emLen:size_nat ->
    ssLen:size_t{v ssLen == sLen /\ sLen + v hLen + 8 < max_size_t} ->
    salt:lbytes sLen ->
    mmsgLen:size_t{v mmsgLen == msgLen} -> msg:lbytes msgLen ->
    eemLen:size_t{v eemLen == emLen /\  emLen - sLen - v hLen - 2 >= 0} ->
    em:lbytes emLen -> Stack unit
    (requires (fun h -> live h salt /\ live h msg /\ live h em /\ disjoint msg salt /\ disjoint em msg /\ disjoint em salt))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 em h0 h1))

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let pss_encode_ #sLen #msgLen #emLen ssLen salt mmsgLen msg eemLen em =
    let m1_size = add #SIZE (add #SIZE (size 8) hLen) ssLen in
    let db_size = sub #SIZE (sub #SIZE eemLen hLen) (size 1) in
    assume (v hLen + v m1_size + v hLen + v db_size + v db_size < max_size_t);
    let stLen = add #SIZE (add #SIZE (add #SIZE (add #SIZE hLen m1_size) hLen) db_size) db_size in

    alloc #uint8 #unit #(v stLen) stLen (u8 0) [BufItem salt; BufItem msg] [BufItem em]
    (fun h0 _ h1 -> True)
    (fun st ->
       pss_encode_in #sLen #msgLen #emLen #(v stLen) ssLen salt mmsgLen msg eemLen m1_size db_size stLen st;
       let db = Buffer.sub #uint8 #(v stLen) #(v db_size) st (add #SIZE (add #SIZE hLen m1_size) hLen) db_size in
       let em_ = Buffer.sub #uint8 #emLen #(v db_size) em (size 0) db_size in
       copy db_size db em_;
       let em_ = Buffer.sub #uint8 #emLen #(v hLen) em db_size hLen in
       let m1Hash = Buffer.sub #uint8 #(v stLen) #(v hLen) st (add #SIZE hLen m1_size) hLen in
       copy hLen m1Hash em_;
       em.(size_decr eemLen) <- u8 0xbc
    )
		
val pss_encode:
    #sLen:size_nat -> #msgLen:size_nat -> #emLen:size_nat ->
    msBits:size_t{v msBits < 8} ->
    ssLen:size_t{v ssLen == sLen /\ sLen + v hLen + 8 < max_size_t} -> salt:lbytes sLen ->
    mmsgLen:size_t{v mmsgLen == msgLen /\ msgLen < pow2 61} -> msg:lbytes msgLen ->
    eemLen:size_t{v eemLen == emLen /\ emLen - sLen - v hLen - 3 >= 0} ->
    em:lbytes emLen -> Stack unit
    (requires (fun h -> live h salt /\ live h msg /\ live h em /\ disjoint msg salt /\ disjoint em msg /\ disjoint em salt))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 em h0 h1))

#reset-options "--z3rlimit 50 --max_fuel 0"

let pss_encode #sLen #msgLen #emLen msBits ssLen salt mmsgLen msg eemLen em =
    if (msBits =. size 0)
    then begin
	let em' = Buffer.sub #uint8 #emLen #(emLen - 1) em (size 1) (size_decr eemLen) in
	disjoint_sub_lemma1 em msg (size 1) (size_decr eemLen);
	disjoint_sub_lemma1 em salt (size 1) (size_decr eemLen);
	pss_encode_ ssLen salt mmsgLen msg (size_decr eemLen) em' end
    else begin
	pss_encode_ ssLen salt mmsgLen msg eemLen em;
	let shift_ = sub #SIZE (size 8) msBits in
	em.(size 0) <- em.(size 0) &. (shift_right #U8 (u8 0xff) (size_to_uint32 shift_))
    end


val pss_verify_in:
    #sLen:size_nat -> #msgLen:size_nat -> #emLen:size_nat -> #stLen:size_nat ->
    ssLen:size_t{v ssLen == sLen /\ sLen + v hLen + 8 < max_size_t} ->
    msBits:size_t{v msBits < 8} ->
    eemLen:size_t{v eemLen == emLen /\ emLen - sLen - v hLen - 2 >= 0} -> em:lbytes emLen ->
    mmsgLen:size_t{v mmsgLen == msgLen} -> msg:lbytes msgLen ->
    pad_size:size_t{v pad_size = emLen - sLen - v hLen - 1} ->
    db_size:size_t{v db_size = emLen - v hLen - 1} ->
    m1_size:size_t{v m1_size = 8 + v hLen + sLen} ->
    sstLen:size_t{v sstLen == stLen /\ stLen = v hLen + v pad_size + v db_size + v m1_size + v hLen} ->
    st:lbytes stLen -> Stack bool
    (requires (fun h -> live h em /\ live h msg /\ live h st /\ disjoint em st /\ disjoint st em /\ disjoint st msg))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st h0 h1))

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"
[@ "substitute"]
let pss_verify_in #sLen #msgLen #emLen #stLen ssLen msBits eemLen em mmsgLen msg pad_size db_size m1_size sstLen st =
    assume (8 + 2 * v hLen + v hLen * v (blocks db_size hLen) < max_size_t);
    
    let mHash = Buffer.sub #uint8 #stLen #(v hLen) st (size 0) hLen in
    disjoint_sub_lemma1 st msg (size 0) hLen;
    hash_sha256 mHash mmsgLen msg;
    
    let pad2 = Buffer.sub #uint8 #stLen #(v pad_size) st hLen pad_size in
    pad2.(size_decr pad_size) <- u8 0x01;

    let maskedDB = Buffer.sub #uint8 #emLen #(v db_size) em (size 0) db_size in
    let m1Hash = Buffer.sub #uint8 #emLen #(v hLen) em db_size hLen in
    let dbMask = Buffer.sub #uint8 #stLen #(v db_size) st (add #SIZE hLen pad_size) db_size in
    mgf_sha256 m1Hash db_size dbMask;
    xor_bytes db_size dbMask maskedDB;
    
    (if (msBits >. size 0) then begin
      let shift_ = sub #SIZE (size 8) msBits in
      dbMask.(size 0) <- dbMask.(size 0) &. (shift_right #U8 (u8 0xff) (size_to_uint32 shift_)) end);

    //let pad = Buffer.sub #uint8 #(v db_size) #(v pad_size) dbMask (size 0) pad_size in
    let pad = Buffer.sub #uint8 #stLen #(v pad_size) st (add #SIZE hLen pad_size) pad_size in
    let salt = Buffer.sub #uint8 #(v db_size) #sLen dbMask pad_size ssLen in

    let m1 = Buffer.sub #uint8 #stLen #(v m1_size) st (add #SIZE (add #SIZE hLen pad_size) db_size) m1_size in
    let m1Hash' = Buffer.sub #uint8 #stLen #(v hLen) st (add #SIZE (add #SIZE (add #SIZE hLen pad_size) db_size) m1_size) hLen in

    disjoint_sub_lemma2 st (add #SIZE hLen pad_size) pad_size hLen pad_size;
    let res = 
	if not (eq_b pad_size pad pad2) then false 
	else begin	
	     let m1_ = Buffer.sub #uint8 #(v m1_size) #(v hLen) m1 (size 8) hLen in
	     copy hLen mHash m1_;
	     let m1_ = Buffer.sub #uint8 #(v m1_size) #sLen m1 (add #SIZE (size 8) hLen) ssLen in
	     copy ssLen salt m1_;
	     hash_sha256 m1Hash' m1_size m1;
	     disjoint_sub_lemma3 em st db_size hLen (add #SIZE (add #SIZE (add #SIZE hLen pad_size) db_size) m1_size) hLen;
	     eq_b hLen m1Hash m1Hash'
	end in
    res


val pss_verify_:
    #sLen:size_nat -> #msgLen:size_nat -> #emLen:size_nat ->
    ssLen:size_t{v ssLen == sLen /\ sLen + v hLen + 8 < max_size_t} ->
    msBits:size_t{v msBits < 8} ->
    eemLen:size_t{v eemLen == emLen /\ emLen - sLen - v hLen - 2 >= 0} ->
    em:lbytes emLen ->
    mmsgLen:size_t{v mmsgLen == msgLen} ->
    msg:lbytes msgLen -> Stack bool
    (requires (fun h -> live h em /\ live h msg /\ disjoint em msg))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies0 h0 h1))

let pss_verify_ #sLen #msgLen #emLen ssLen msBits eemLen em mmsgLen msg =
    let pad_size = sub #SIZE (sub #SIZE (sub #SIZE eemLen ssLen) hLen) (size 1) in
    let db_size = sub #SIZE (sub #SIZE eemLen hLen) (size 1) in
    let m1_size = add #SIZE (add #SIZE (size 8) hLen) ssLen in
    
    assume (v hLen + v pad_size + v db_size + v m1_size + v hLen < max_size_t);
    let stLen = add #SIZE (add #SIZE (add #SIZE (add #SIZE hLen pad_size) db_size) m1_size) hLen in
    
    alloc #uint8 #bool #(v stLen) stLen (u8 0) [BufItem em; BufItem msg] []
    (fun h0 _ h1 -> True)
    (fun st ->
	  pss_verify_in #sLen #msgLen #emLen #(v stLen) ssLen msBits eemLen em mmsgLen msg pad_size db_size m1_size stLen st
    )


val pss_verify:
    #sLen:size_nat -> #msgLen:size_nat -> #emLen:size_nat ->
    ssLen:size_t{v ssLen == sLen /\ sLen + v hLen + 8 < max_size_t} ->
    msBits:size_t{v msBits < 8} ->
    eemLen:size_t{v eemLen == emLen /\ emLen - sLen - v hLen - 2 >= 0} ->
    em:lbytes emLen ->
    mmsgLen:size_t{v mmsgLen == msgLen} -> msg:lbytes msgLen -> Stack bool
    (requires (fun h -> live h em /\ live h msg /\ disjoint em msg))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies0 h0 h1))

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let pss_verify #sLen #msgLen #emLen ssLen msBits eemLen em mmsgLen msg =
    let h0 = FStar.HyperStack.ST.get() in
    let em_0 = em.(size 0) &. (shift_left #U8 (u8 0xff) (size_to_uint32 msBits)) in
    let em_last = em.(size_decr eemLen) in

    let res = 
      if not ((eq_u8 em_0 (u8 0)) && (eq_u8 em_last (u8 0xbc)))
      then false
      else begin
	 let eemLen1 = if msBits =. size 0 then size_decr eemLen else eemLen in
	 let em1:lbytes (v eemLen1) =
	     if msBits =. size 0 then begin
	       let em' = Buffer.sub em (size 1) eemLen1 in
	       disjoint_sub_lemma1 em msg (size 1) eemLen1;
	       em' end
	     else em in
	 if (eemLen1 <. add #SIZE (add #SIZE ssLen hLen) (size 2)) then false
	 else pss_verify_ #sLen #msgLen #(v eemLen1) ssLen msBits eemLen1 em1 mmsgLen msg
      end in
    let h1 = FStar.HyperStack.ST.get() in
    assume (modifies0 h0 h1);
    res

val rsa_sign:
    #sLen:size_nat -> #msgLen:size_nat ->
    pow2_i:size_t -> iLen:size_t ->
    modBits:size_t{0 < v modBits /\ v modBits + 3 < max_size_t} ->
    eBits:size_t{0 < v eBits /\ v eBits <= v modBits} ->
    dBits:size_t{0 < v dBits /\ v dBits <= v modBits /\
		 v (bits_to_bn modBits) + v (bits_to_bn eBits) + v (bits_to_bn dBits) < max_size_t} ->
    skey:lbignum (v (bits_to_bn modBits) + v (bits_to_bn eBits) + v (bits_to_bn dBits)) ->
    ssLen:size_t{v ssLen == sLen /\ sLen + v hLen + 8 < max_size_t /\ v (blocks modBits (size 8)) - sLen - v hLen - 3 >= 0 } ->
    salt:lbytes sLen ->
    mmsgLen:size_t{v mmsgLen == msgLen /\ msgLen < pow2 61} -> msg:lbytes msgLen ->
    sgnt:lbytes (v (blocks modBits (size 8))) -> Stack unit
    (requires (fun h -> live h salt /\ live h msg /\ live h sgnt /\ live h skey /\
	              disjoint msg salt /\ disjoint msg sgnt /\ disjoint sgnt salt))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 sgnt h0 h1))

#reset-options "--z3rlimit 300 --max_fuel 0 --max_ifuel 0"

let rsa_sign #sLen #msgLen pow2_i iLen modBits eBits dBits skey ssLen salt mmsgLen msg sgnt =
    let nLen = bits_to_bn modBits in
    let eLen = bits_to_bn eBits in
    let dLen = bits_to_bn dBits in
    let skeyLen = add #SIZE (add #SIZE nLen eLen) dLen in
    let k = blocks modBits (size 8) in
    let msBits = (size_decr modBits) %. size 8 in
    
    assume (v nLen + v nLen < max_size_t);
    assume (8 * v (get_size_nat k) < max_size_t);
    assume (v nLen == v k);
 
    let n2Len:size_t = add #SIZE nLen nLen in
    
    alloc #uint8 #unit #(v k) k (u8 0) [BufItem skey; BufItem msg; BufItem salt] [BufItem sgnt]
    (fun h0 _ h1 -> True)
    (fun em -> 
       pss_encode msBits ssLen salt mmsgLen msg k em;
      	
       alloc #uint64 #unit #(v n2Len) n2Len (u64 0) [BufItem skey; BufItem em] [BufItem sgnt]
	(fun h0 _ h1 -> True)
	(fun tmp ->
	   let n = Buffer.sub #uint64 #(v skeyLen) #(v nLen) skey (size 0) nLen in
	   let e = Buffer.sub #uint64 #(v skeyLen) #(v eLen) skey nLen eLen in
	   let d = Buffer.sub #uint64 #(v skeyLen) #(v dLen) skey (add #SIZE nLen eLen) dLen in

	   let m = Buffer.sub #uint64 #(v n2Len) #(v nLen) tmp (size 0) nLen in
	   let s = Buffer.sub #uint64 #(v n2Len) #(v nLen) tmp nLen nLen in
	   
	   (**) disjoint_sub_lemma1 tmp em (size 0) nLen;
	   text_to_nat k em m;
	   mod_exp pow2_i iLen modBits nLen n m dBits d s;
	   (**) disjoint_sub_lemma1 tmp sgnt nLen nLen; 
	   nat_to_text k s sgnt
	)
    )

val rsa_verify:
    #sLen:size_nat -> #msgLen:size_nat ->
    pow2_i:size_t -> iLen:size_t ->
    modBits:size_t{0 < v modBits /\ v modBits + 3 < max_size_t} ->
    eBits:size_t{0 < v eBits /\ v eBits <= v modBits /\
		 v (bits_to_bn modBits) + v (bits_to_bn eBits) < max_size_t} ->
    pkey:lbignum (v (bits_to_bn modBits) + v (bits_to_bn eBits)) ->
    ssLen:size_t{v ssLen == sLen /\ sLen + v hLen + 8 < max_size_t} ->
    sgnt:lbytes (v (blocks modBits (size 8))) ->
    mmsgLen:size_t{v mmsgLen == msgLen /\ msgLen < pow2 61} -> msg:lbytes msgLen -> Stack bool
    (requires (fun h -> live h msg /\ live h sgnt /\ live h pkey /\ disjoint msg sgnt))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies0 h0 h1))

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let rsa_verify #sLen #msgLen pow2_i iLen modBits eBits pkey ssLen sgnt mmsgLen msg =
    let nLen = bits_to_bn modBits in
    let eLen = bits_to_bn eBits in
    let pkeyLen = add #SIZE nLen eLen in
    let k = blocks modBits (size 8) in
    let msBits = (size_decr modBits) %. size 8 in
    
    assume (8 * v (get_size_nat k) < max_size_t);
    assume (v nLen + v nLen < max_size_t);
    assume (v k - sLen - v hLen - 2 >= 0);
    assume (v nLen = v k);
    let n2Len:size_t = add #SIZE nLen nLen in

    alloc #uint64 #bool #(v n2Len) n2Len (u64 0) [BufItem pkey; BufItem msg; BufItem sgnt] []
    (fun h0 _ h1 -> True)
    (fun tmp ->
	let s = Buffer.sub #uint64 #(v n2Len) #(v nLen) tmp nLen nLen in
	(**) disjoint_sub_lemma1 tmp sgnt nLen nLen;
	text_to_nat k sgnt s;

	alloc #uint8 #bool #(v k) k (u8 0) [BufItem pkey; BufItem msg] [BufItem tmp]
	(fun h0 _ h1 -> True)
	(fun em ->
            let m = Buffer.sub #uint64 #(v n2Len) #(v nLen) tmp (size 0) nLen in
	    let s = Buffer.sub #uint64 #(v n2Len) #(v nLen) tmp nLen nLen in
	
	    let n = Buffer.sub #uint64 #(v pkeyLen) #(v nLen) pkey (size 0) nLen in
	    let e = Buffer.sub #uint64 #(v pkeyLen) #(v eLen) pkey nLen eLen in

	    assume (disjoint s n);
	    let res = 
	      if (bn_is_less nLen s n) then begin
	         mod_exp pow2_i iLen modBits nLen n s eBits e m;
		 disjoint_sub_lemma1 tmp em (size 0) nLen;
		 nat_to_text k m em;
		 pss_verify #sLen #msgLen #(v k) ssLen msBits k em mmsgLen msg end
	      else false in
	    res 
       )
    )
