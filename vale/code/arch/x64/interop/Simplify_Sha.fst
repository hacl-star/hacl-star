module Simplify_Sha

friend SHA_helpers

#set-options "--z3rlimit_factor 4"

open Words_s

#set-options "--z3rlimit 20"

let reveal_get128 (s:Seq.lseq UInt8.t 16) (v0 v1 v2 v3:UInt32.t) : Lemma
  (requires 
    Views.get32 (Seq.slice s 0 4) == v0 /\
    Views.get32 (Seq.slice s 4 8) == v1 /\
    Views.get32 (Seq.slice s 8 12) == v2 /\
    Views.get32 (Seq.slice s 12 16) == v3)    
  (ensures Views.get128 s == Mkfour (UInt32.v v0) (UInt32.v v1) (UInt32.v v2) (UInt32.v v3)) = 
  Opaque_s.reveal_opaque Views.get128_def;
  Opaque_s.reveal_opaque le_bytes_to_quad32_def;
  Opaque_s.reveal_opaque Views.get32_def

let reveal_get32_128 (s:Seq.lseq UInt32.t 4) : Lemma
  (Views.get32_128 s == Mkfour 
    (UInt32.v (Seq.index s 0))
    (UInt32.v (Seq.index s 1))
    (UInt32.v (Seq.index s 2))
    (UInt32.v (Seq.index s 3))    
  ) = Opaque_s.reveal_opaque Views.get32_128_def

let reveal_low_buffer_read (b8:buf_t TUInt128) (h:HS.mem) (i:nat{i < B.length b8 / 4}) : Lemma
  (requires B.live h b8 /\ B.length b8 % 4 = 0)
  (ensures low_buffer_read TUInt32 h b8 i == Views.get32 (Seq.slice (B.as_seq h b8) (i*4) (i*4+4)))
  = let view = Views.view32 in
    let b_v = BV.mk_buffer_view b8 view in
    BV.as_buffer_mk_buffer_view b8 view;
    BV.get_view_mk_buffer_view b8 view;
    BV.length_eq b_v; 
    BV.as_seq_sel h b_v i;
    BV.get_sel h b_v i

let reveal_imm_low_buffer_read (b8:ibuf_t TUInt128) (h:HS.mem) (i:nat{i < B.length b8 / 4}) : Lemma
  (requires B.live h b8 /\ B.length b8 % 4 = 0)
  (ensures imm_low_buffer_read TUInt32 h b8 i == Views.get32 (Seq.slice (B.as_seq h b8) (i*4) (i*4+4)))
  = let view = Views.view32 in
    let b_v = BV.mk_buffer_view b8 view in
    BV.as_buffer_mk_buffer_view b8 view;
    BV.get_view_mk_buffer_view b8 view;
    BV.length_eq b_v; 
    BV.as_seq_sel h b_v i;
    BV.get_sel h b_v i

let math_aux1 (b:B.buffer UInt32.t) (bv:BV.buffer quad32) (n:nat) : Lemma
  (requires B.length b == n /\ BV.length bv == B.length b / 4)
  (ensures BV.length bv = n/4) = ()

let math_aux2 (b:B.buffer UInt8.t) (bv:BV.buffer quad32) (n:nat) : Lemma
  (requires B.length b == n * 4 /\ BV.length bv == B.length b / 16)
  (ensures BV.length bv = n/4) = ()

let lemma_same_length_32_128
  (b8:buf_t TUInt128)
  (b:B.buffer UInt32.t)
  (h:HS.mem) : Lemma
  (requires B.live h b /\ B.live h b8 /\ 
    B.length b8 == B.length b * 4 /\ B.length b % 4 == 0)
  (ensures Seq.length (BV.as_seq h (BV.mk_buffer_view b8 Views.view128)) =
           Seq.length (BV.as_seq h (BV.mk_buffer_view b Views.view32_128)))
  = 
    let b128 = BV.mk_buffer_view b8 Views.view128 in
    let b32 = BV.mk_buffer_view b Views.view32_128 in
    BV.as_buffer_mk_buffer_view b8 Views.view128;
    BV.get_view_mk_buffer_view b8 Views.view128;
    BV.length_eq b128;
    
    BV.as_buffer_mk_buffer_view b Views.view32_128;
    BV.get_view_mk_buffer_view b Views.view32_128;
    BV.length_eq b32;
    math_aux1 b b32 (B.length b);
    math_aux2 b8 b128 (B.length b)

let math_aux3 (k_b:IB.ibuffer UInt8.t) (h:HS.mem) : Lemma
  (requires B.length k_b == 256 /\ B.length k_b % 16 == 0)
  (ensures Seq.length (BV.as_seq h (BV.mk_buffer_view k_b Views.view128)) == 16) =
  BV.as_buffer_mk_buffer_view k_b Views.view128;
  BV.get_view_mk_buffer_view k_b Views.view128;
  BV.length_eq (BV.mk_buffer_view k_b Views.view128)  


let simplify_hash_32_128
  (b8:buf_t TUInt128)
  (b:B.buffer UInt32.t)
  (h:HS.mem) : Lemma
  (requires B.live h b /\ B.live h b8 /\ B.length b8 == B.length b * 4 /\
    B.length b % 4 == 0 /\ B.length b8 % 4 == 0 /\
    (forall (i:nat{i < B.length b}). Seq.index (B.as_seq h b) i == low_buffer_read TUInt32 h b8 i))
  (ensures Seq.equal
    (BV.as_seq h (BV.mk_buffer_view b8 Views.view128))
    (BV.as_seq h (BV.mk_buffer_view b Views.view32_128))) =
  let b128 = BV.mk_buffer_view b8 Views.view128 in
  let b32 = BV.mk_buffer_view b Views.view32_128 in
  let s128 = BV.as_seq h b128 in
  let s32 = BV.as_seq h b32 in
  lemma_same_length_32_128 b8 b h;
  let aux2 (i:nat{i < Seq.length s32}) : Lemma (Seq.index s32 i == Seq.index s128 i) =
    BV.as_seq_sel h b128 i;
    BV.get_sel h b128 i;
    BV.as_seq_sel h b32 i;
    BV.get_sel h b32 i;
    BV.as_buffer_mk_buffer_view b8 Views.view128;
    BV.get_view_mk_buffer_view b8 Views.view128;
    BV.length_eq b128;      
    BV.as_buffer_mk_buffer_view b Views.view32_128;
    BV.get_view_mk_buffer_view b Views.view32_128;
    BV.length_eq b32;    

    let s = Seq.slice (B.as_seq h b) (i*4) (i*4+4) in
    let big_s = Seq.slice (B.as_seq h b8) (i*16) (i*16+16) in
    reveal_low_buffer_read b8 h (i*4);
    reveal_low_buffer_read b8 h (i*4+1);
    reveal_low_buffer_read b8 h (i*4+2);
    reveal_low_buffer_read b8 h (i*4+3); 
    assert (Seq.equal
      (Seq.slice (B.as_seq h b8) (i*16) (i*16+4))
      (Seq.slice big_s 0 4));
    assert (Seq.equal
      (Seq.slice (B.as_seq h b8) (i*16+4) (i*16+8))
      (Seq.slice big_s 4 8));
    assert (Seq.equal
      (Seq.slice (B.as_seq h b8) (i*16+8) (i*16+12))
      (Seq.slice big_s 8 12));
    assert (Seq.equal
      (Seq.slice (B.as_seq h b8) (i*16+12) (i*16+16))
      (Seq.slice big_s 12 16));      
    reveal_get32_128 s;
    reveal_get128 big_s
      (Seq.index s 0)
      (Seq.index s 1)
      (Seq.index s 2)
      (Seq.index s 3)
  in Classical.forall_intro aux2

let imm_math_aux1 (b:IB.ibuffer UInt32.t) (bv:BV.buffer quad32) (n:nat) : Lemma
  (requires B.length b == n /\ BV.length bv == B.length b / 4)
  (ensures BV.length bv = n/4) = ()

let imm_math_aux2 (b:IB.ibuffer UInt8.t) (bv:BV.buffer quad32) (n:nat) : Lemma
  (requires B.length b == n * 4 /\ BV.length bv == B.length b / 16)
  (ensures BV.length bv = n/4) = ()

let lemma_imm_same_length_32_128
  (b8:ibuf_t TUInt128)
  (b:IB.ibuffer UInt32.t)
  (h:HS.mem) : Lemma
  (requires B.live h b /\ B.live h b8 /\ 
    B.length b8 == B.length b * 4 /\ B.length b % 4 == 0)
  (ensures Seq.length (BV.as_seq h (BV.mk_buffer_view b8 Views.view128)) =
           Seq.length (BV.as_seq h (BV.mk_buffer_view b Views.view32_128)))
  = 
    let b128 = BV.mk_buffer_view b8 Views.view128 in
    let b32 = BV.mk_buffer_view b Views.view32_128 in
    BV.as_buffer_mk_buffer_view b8 Views.view128;
    BV.get_view_mk_buffer_view b8 Views.view128;
    BV.length_eq b128;
    
    BV.as_buffer_mk_buffer_view b Views.view32_128;
    BV.get_view_mk_buffer_view b Views.view32_128;
    BV.length_eq b32;
    imm_math_aux1 b b32 (B.length b);
    imm_math_aux2 b8 b128 (B.length b)

let imm_simplify_hash_32_128
  (b8:ibuf_t TUInt128)
  (b:IB.ibuffer UInt32.t)
  (h:HS.mem) : Lemma
  (requires B.live h b /\ B.live h b8 /\ B.length b8 == B.length b * 4 /\
    B.length b % 4 == 0 /\ B.length b8 % 4 == 0 /\
    (forall (i:nat{i < B.length b}). Seq.index (B.as_seq h b) i == imm_low_buffer_read TUInt32 h b8 i))
  (ensures Seq.equal
    (BV.as_seq h (BV.mk_buffer_view b8 Views.view128))
    (BV.as_seq h (BV.mk_buffer_view b Views.view32_128))) =
  let b128 = BV.mk_buffer_view b8 Views.view128 in
  let b32 = BV.mk_buffer_view b Views.view32_128 in
  let s128 = BV.as_seq h b128 in
  let s32 = BV.as_seq h b32 in
  lemma_imm_same_length_32_128 b8 b h;
  let aux2 (i:nat{i < Seq.length s32}) : Lemma (Seq.index s32 i == Seq.index s128 i) =
    BV.as_seq_sel h b128 i;
    BV.get_sel h b128 i;
    BV.as_seq_sel h b32 i;
    BV.get_sel h b32 i;
    BV.as_buffer_mk_buffer_view b8 Views.view128;
    BV.get_view_mk_buffer_view b8 Views.view128;
    BV.length_eq b128;      
    BV.as_buffer_mk_buffer_view b Views.view32_128;
    BV.get_view_mk_buffer_view b Views.view32_128;
    BV.length_eq b32;    

    let s = Seq.slice (B.as_seq h b) (i*4) (i*4+4) in
    let big_s = Seq.slice (B.as_seq h b8) (i*16) (i*16+16) in
    reveal_imm_low_buffer_read b8 h (i*4);
    reveal_imm_low_buffer_read b8 h (i*4+1);
    reveal_imm_low_buffer_read b8 h (i*4+2);
    reveal_imm_low_buffer_read b8 h (i*4+3); 
    assert (Seq.equal
      (Seq.slice (B.as_seq h b8) (i*16) (i*16+4))
      (Seq.slice big_s 0 4));
    assert (Seq.equal
      (Seq.slice (B.as_seq h b8) (i*16+4) (i*16+8))
      (Seq.slice big_s 4 8));
    assert (Seq.equal
      (Seq.slice (B.as_seq h b8) (i*16+8) (i*16+12))
      (Seq.slice big_s 8 12));
    assert (Seq.equal
      (Seq.slice (B.as_seq h b8) (i*16+12) (i*16+16))
      (Seq.slice big_s 12 16));      
    reveal_get32_128 s;
    reveal_get128 big_s
      (Seq.index s 0)
      (Seq.index s 1)
      (Seq.index s 2)
      (Seq.index s 3)
  in Classical.forall_intro aux2

#set-options "--z3rlimit 40"

let lemma_k_reqs_equiv k_b k_b8 h =
  let k_seq = BV.as_seq h (BV.mk_buffer_view k_b8 Views.view128) in
  math_aux3 k_b8 h;
  assert (Seq.equal
    (B.as_seq h k_b)
    k);
  imm_simplify_hash_32_128 k_b8 k_b h;
  let aux (i:nat{i < size_k_w_256/4}) : Lemma
    ((k_seq.[i]).lo0 == word_to_nat32 (k.[4 `op_Multiply` i]) /\
    (k_seq.[i]).lo1 == word_to_nat32 (k.[4 `op_Multiply` i + 1]) /\
    (k_seq.[i]).hi2 == word_to_nat32 (k.[4 `op_Multiply` i + 2]) /\
    (k_seq.[i]).hi3 == word_to_nat32 (k.[4 `op_Multiply` i + 3]))
    = Opaque_s.reveal_opaque Views.get32_128_def;
      let s = B.as_seq h k_b in
      let b32 = BV.mk_buffer_view k_b Views.view32_128 in
      BV.as_buffer_mk_buffer_view k_b Views.view32_128;
      BV.get_view_mk_buffer_view k_b Views.view32_128;
      BV.length_eq b32;
      BV.as_seq_sel h b32 i;
      BV.get_sel h b32 i;       
      assert (Seq.index s (4*i) == Seq.index k (4*i));
      assert (Seq.index s (4*i+1) == Seq.index k (4*i+1));
      assert (Seq.index s (4*i+2) == Seq.index k (4*i+2));
      assert (Seq.index s (4*i+3) == Seq.index k (4*i+3))// ;     
  in Classical.forall_intro aux

let simplify_quad_aux (b:B.buffer UInt8.t) (h:HS.mem) : Lemma
  (requires B.live h b /\ B.length b % 16 == 0)
  (ensures (BV.length (BV.mk_buffer_view b Views.view128) == B.length b / 16))
  =
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq (BV.mk_buffer_view b Views.view128)

open Words.Four_s
open Collections.Seqs_s

#reset-options "--z3rlimit 60 --max_fuel 0 --max_ifuel 2 --initial_ifuel 2"
let lemma_seq_nat8_le_seq_quad32_to_bytes_uint32 b h =
  let s_init = B.as_seq h b in
  //view of b as buffer of UInt128
  let b128 = BV.mk_buffer_view b Views.view128 in
  //length s == length s_init / 16
  let s = BV.as_seq h b128 in
  //s' sequence of nat8 with length that of s_init (== length s * 16)
  let s' = le_seq_quad32_to_bytes s in
  Opaque_s.reveal_opaque le_seq_quad32_to_bytes_def;
  //definition given by reveal_opaque
  assert (s' == seq_four_to_seq_LE (seq_map (nat_to_four 8) (seq_four_to_seq_LE s)));
  let s_f = seq_nat8_to_seq_uint8 s' in
  simplify_quad_aux b h;
  let aux (i:nat{i < Seq.length s_f}) : Lemma (Seq.index s_init i == Seq.index s_f i) = 
    let i' = i/16 in
    BV.as_seq_sel h b128 i';
    BV.get_sel h b128 i'; 
    assert (Seq.index s i' == Views.get128 (Seq.slice s_init (i' `op_Multiply` 16) (i' `op_Multiply` 16 + 16)));
    Opaque_s.reveal_opaque Views.get128_def;
    let s_slice = seq_uint8_to_seq_nat8 (Seq.slice s_init (i' `op_Multiply` 16) (i' `op_Multiply` 16 +16)) in
    Opaque_s.reveal_opaque le_bytes_to_quad32_def;
    assert (seq_to_four_LE (seq_map (four_to_nat 8) (seq_to_seq_four_LE s_slice)) ==
            Seq.index s i')
  in Classical.forall_intro aux;
  assert (Seq.equal s_f s_init)


let simplify_bytes_hash_aux (b:B.buffer UInt32.t) (h:HS.mem) : Lemma
  (requires B.live h b /\ B.length b % 4 == 0)
  (ensures (BV.length (BV.mk_buffer_view b Views.view32_128) == B.length b / 4))
  =
  BV.as_buffer_mk_buffer_view b Views.view32_128;
  BV.get_view_mk_buffer_view b Views.view32_128;
  BV.length_eq (BV.mk_buffer_view b Views.view32_128)

let simplify_bytes_hash_aux2 (b:B.buffer UInt32.t) (h:HS.mem) (i:nat{i < B.length b}) : Lemma
  (requires B.live h b /\ B.length b % 4 == 0)
  (ensures (let b128 = BV.mk_buffer_view b Views.view32_128 in
    let s = BV.as_seq h b128 in
    simplify_bytes_hash_aux b h;
    UInt32.uint_to_t (four_select (Seq.index s (i/4)) (i%4)) == Seq.index (B.as_seq h b) i)) =
  let b128 = BV.mk_buffer_view b Views.view32_128 in
  let s = BV.as_seq h b128 in
  simplify_bytes_hash_aux b h;
  let i' = i/4 in
  BV.as_seq_sel h b128 i';
  BV.get_sel h b128 i';
  assert (Seq.index s i' == 
     Views.get32_128 (Seq.slice (B.as_seq h b) (i' `op_Multiply` 4) (i' `op_Multiply` 4 + 4)));
  Opaque_s.reveal_opaque Views.get32_128_def

let simplify_bytes_hash (b:B.buffer UInt32.t) (h:HS.mem) : Lemma
  (requires B.live h b /\ B.length b == 8 /\ B.length b % 4 == 0)
  (ensures (
    let b128 = BV.mk_buffer_view b Views.view32_128 in
    le_bytes_to_hash (le_seq_quad32_to_bytes (BV.as_seq h b128)) == B.as_seq h b
  )) =
  let s_init = B.as_seq h b in
  let b128 = BV.mk_buffer_view b Views.view32_128 in
  let s = BV.as_seq h b128 in
  let s' = le_seq_quad32_to_bytes s in
  let s_f = le_bytes_to_hash s' in
  simplify_bytes_hash_aux b h;
  Opaque_s.reveal_opaque le_seq_quad32_to_bytes_def;
  let s_map = seq_map UInt32.uint_to_t (seq_four_to_seq_LE s) in
  assert (Seq.equal s_f s_map);
  let aux (i:nat{i < Seq.length s_map}) : Lemma (Seq.index s_map i == Seq.index s_init i) = 
    assert (Seq.index s_map i = UInt32.uint_to_t (four_select (Seq.index s (i / 4)) (i % 4)));
    simplify_bytes_hash_aux2 b h i
  in Classical.forall_intro aux;
  assert (Seq.equal s_map s_init)

let simplify_le_bytes_to_hash_uint32 b8 b h =
  simplify_hash_32_128 b8 b h;
  simplify_bytes_hash b h
