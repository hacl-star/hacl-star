module Spec.Argon2i

#reset-options "--z3rlimit 100 --max_fuel 0"

let ( *$ ) = FStar.Mul.(( * ))
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.RawIntTypes
open Lib.LoopCombinators

let version_number : uint8 = assert_norm (0x13 < maxint (U8));u8 0x13
let argon_type = 1
let block_size = 1024
let line_size = 128

(** Wrapper for Blake2b hash function called without a secret key *)
val h : a_len:size_nat{0 < a_len /\ a_len <=max_size_t - 2 *$line_size}
  -> a:lbytes a_len
  -> nn:size_nat{1 <= nn /\ nn <= 64}
  -> Tot (lbytes nn)
let h a_len a nn =
  let null_list = [] in
  let null_key : lbytes 0 = assert_norm (List.Tot.length null_list = 0); of_list #uint8 null_list in
  Spec.Blake2.blake2b a 0 null_key nn

(** Concats the parameters for Argon2i and hashes them to provide the initial buffer *)
val concat_and_hash :
  p_len:size_nat -> p : lbytes p_len ->
  s_len:size_nat -> s: lbytes s_len ->
  lanes:size_nat -> t_len:size_nat ->
  m:size_nat ->
  iterations:size_nat ->
  x_len:size_nat -> x:lbytes x_len ->
  k_len:size_nat{k_len + p_len + s_len + x_len + 11*$4 <= max_size_t - 2*$line_size} -> k:lbytes k_len ->
  Tot (lbytes 64)

let concat_and_hash p_len p s_len s lanes t_len m iterations x_len x k_len k =
  (* This is basically a big concatenation *)
  let lanes_as_word = uint_to_bytes_le #U32 (u32 lanes) in
  let t_len_as_word = uint_to_bytes_le #U32 (u32 t_len) in
  let m_as_word = uint_to_bytes_le #U32 (u32 m) in
  let iterations_as_word = uint_to_bytes_le #U32 (u32 iterations) in
  let v_as_word = uint_to_bytes_le #U32 (to_u32 #U8 version_number) in
  let argon_type_as_word = uint_to_bytes_le #U32 (u32 argon_type) in
  let p_len_as_word = uint_to_bytes_le #U32 (u32 p_len) in
  let s_len_as_word = uint_to_bytes_le #U32 (u32 s_len) in
  let k_len_as_word = uint_to_bytes_le #U32 (u32 k_len) in
  let x_len_as_word = uint_to_bytes_le #U32 (u32 x_len) in
  let blake2_argument_size : size_nat = 10*$4 + p_len + k_len + s_len + x_len in
  let blake2_argument = create blake2_argument_size (u8 0) in
  let blake2_argument = update_slice blake2_argument 0 4 lanes_as_word in
  let blake2_argument = update_slice blake2_argument 4 8 t_len_as_word in
  let blake2_argument = update_slice blake2_argument 8 12 m_as_word in
  let blake2_argument = update_slice blake2_argument 12 16 iterations_as_word in
  let blake2_argument = update_slice blake2_argument 16 20 v_as_word in
  let blake2_argument = update_slice blake2_argument 20 24 argon_type_as_word in
  let blake2_argument = update_slice blake2_argument 24 28 p_len_as_word in
  let blake2_argument = update_slice blake2_argument 28 (28 + p_len) p in
  let offset = 28 + p_len in
  let blake2_argument = update_slice blake2_argument offset (offset + 4) s_len_as_word in
  let blake2_argument = update_slice blake2_argument (offset + 4) (offset + 4 + s_len) s in
  let offset = offset + 4 + s_len in
  let blake2_argument = update_slice blake2_argument offset (offset + 4) k_len_as_word in
  let blake2_argument = update_slice blake2_argument (offset + 4) (offset + 4 + k_len) k in
  let offset = offset + 4 + k_len in
  let blake2_argument = update_slice blake2_argument offset (offset + 4) x_len_as_word in
  let blake2_argument = update_slice blake2_argument (offset + 4) (offset + 4 + x_len) x in
  h blake2_argument_size blake2_argument 64

let ceil_32 (x:size_nat) : Tot size_nat = if x % 32 = 0 then x / 32 else x / 32  + 1

(** Formula to get the output size of the variable-length hash function depending on the desired tag length *)
let compute_variable_length_output_size (t_len:size_nat{t_len + 64 <= max_size_t}) : Tot (result:size_nat{result <= max_size_t}) =
  if t_len <= 64 then t_len else
    (* For long tags we ceil to the next multiple of 64*)
    let r = (ceil_32 t_len) - 2 in
    32*$r + 64


(**
Variable-length hash function used to shuffle the blocks in memory
See section 3.2 of the Argon2 spec
*)
val h' : t_len:size_nat{1 <= t_len /\ t_len + 64 <= max_size_t}
  -> x_len:size_nat{x_len + 4 <= max_size_t - 2*$line_size}
  -> x:lbytes x_len
  -> Tot (lbytes (compute_variable_length_output_size t_len))

let h' t_len x_len x =
  let t_with_x_len : size_nat = x_len + 4 in
  let t_with_x = create t_with_x_len (u8 0) in
  let t_with_x = update_slice t_with_x 0 4 (uint_to_bytes_le #U32 (u32 t_len)) in
  let t_with_x = update_slice t_with_x 4 t_with_x_len x in
  if t_len <= 64 then
    h t_with_x_len t_with_x t_len
  else
    let r = (ceil_32 t_len) - 2 in
    let output = create (compute_variable_length_output_size t_len) (u8 0) in
    let v1 = h t_with_x_len t_with_x 64 in
    let output = update_slice output 0 32 (sub v1 0 32)  in
    let (output,vlast) = repeati r (fun i (output,vprevious) ->
      let i = i + 1 in (* we did the first iteration outside the loop *)
      let v = h 64 vprevious 64 in
      (update_slice output (i*$32) ((i+1)*$32) (sub v 0 32),v)
    ) (output,v1)
    in
    update_slice output (r*$32) ((r*$32)+64) vlast

let low_bits (x:uint64) : uint64 = to_u64 (to_u32 x)

type idx = idx:size_nat{idx <= 15}

(**
Low-level compression function inspired by Blake2b
See annex A of the Argon2 spec
*)
let g (a:uint64) (b:uint64) (c:uint64) (d:uint64) : (uint64 & uint64 & uint64 & uint64) =
  let a = a +. b +. (u64 2) *. (low_bits a) *. (low_bits b) in
  let d = (d ^. a) >>>. (size 32) in
  let c = c +. d +. (u64 2) *. (low_bits c) *. (low_bits d) in
  let b = (b ^. c) >>>. (size 24) in
  let a = a +. b +. (u64 2) *. (low_bits a) *. (low_bits b) in
  let d = (d ^. a) >>>. (size 16) in
  let c = c +. d +. (u64 2) *. (low_bits c) *. (low_bits d) in
  let b = (b ^. c) >>>. (size 63) in
  (a,b,c,d)

(** Wrapper around g *)
let apply_g (v:lseq uint64 16) (i1:idx) (i2:idx) (i3:idx) (i4:idx) : Tot (lseq uint64 16) =
  let a : uint64 = index v i1 in
  let b : uint64 = index v i2 in
  let c : uint64 = index v i3 in
  let d : uint64 = index v i4 in
  let (a,b,c,d) = g a b c d in
  let v = upd v i1 a in
  let v = upd v i2 b in
  let v = upd v i3 c in
  let v = upd v i4 d in
  v

(**
Permuation function P that shuffles a 128-bytes line
See annex A of the Argon2 spec
*)
val argon_permute : input: lbytes line_size -> Tot (lbytes line_size)
let argon_permute input =
  let v : lseq uint64 16 = create 16 (u64 0) in
  let v = repeati 8 (fun i v ->
     let tmp1 : uint64 = uint_from_bytes_le #U64 (sub input (i*$16) 8) in
     let tmp2 : uint64 = uint_from_bytes_le #U64 (sub input (i*$16 + 8) 8) in
     let v = upd v (2*$i) tmp1 in
     upd v (2*$i + 1) tmp2
  ) v in
  let v = apply_g v 0 4 8 12 in
  let v = apply_g v 1 5 9  13 in
  let v = apply_g v 2 6 10 14 in
  let v = apply_g v 3 7 11 15 in
  let v = apply_g v 0 5 10 15 in
  let v = apply_g v 1 6 11 12 in
  let v = apply_g v 2 7 8  13 in
  let v = apply_g v 3 4 9  14 in
  uints_to_bytes_le #U64 v

(** Performs a XOR on two 1024-bytes blocks *)
let xor_matrices (x:lbytes block_size) (y:lbytes block_size) : Tot (lbytes block_size) =
  let r = create block_size (u8 0) in
  repeati (block_size / 8) (fun i r ->
    update_slice r (8*$i) (8*$(i+1)) (uint_to_bytes_be (
      (uint_from_bytes_be #U64 #SEC (sub x (8*$i) 8)) ^. (uint_from_bytes_be #U64 (sub y (8*$i) 8))
    ))
  ) r

(** Extracts a columns of 64-bits words in a matrix as a 128-bytes line *)
let extract_column_from_matrix (r: lbytes block_size) (j:size_nat{j < 8}) : Tot (lbytes line_size) =
  let output : lbytes line_size = create line_size (u8 0) in
  let output = repeati 8 (fun i output ->
    let r_offset : size_nat = i*$line_size + j*$16 in
    update_slice output (i*$16) ((i+1)*$16) (sub r r_offset 16)
  ) output
  in
  output

(** Updates a column of 64-bitts words according to the contents of a 128-bytes line*)
let update_column_to_matrix (col:lbytes line_size) (r:lbytes block_size) (j:size_nat{j < 8})
  : Tot (lbytes block_size) =
  repeati 8 (fun i (r:lbytes block_size) ->
    let r_offset = i*$line_size + j*$16 in
     update_slice r r_offset (r_offset + 16) (sub col (i*$16) 16)
  ) r

(**
Argon2i compression function G used to merge two blocks of data
See section 3.4 of the Argon2 spec
*)
let argon_compress (x:lbytes block_size) (y:lbytes block_size) : Tot (lbytes block_size) =
  let r : lbytes block_size = create block_size (u8 0) in
  let r = xor_matrices x y in
  (* permute rows *)
  let q = repeati 8 (fun i r ->
    assert_norm (0 <= i /\ i < 8);
    let row : lbytes line_size = sub r (line_size*$i) line_size in
    let row = argon_permute row in
    update_slice r (line_size*$i) (line_size*$(i+1)) row
  ) r in
  (* permute columns *)
  let z = repeati 8 (fun j q ->
    let col = extract_column_from_matrix q j in
    let col = argon_permute col in
    update_column_to_matrix col q j
  ) q in
  xor_matrices z r


(** Pad a buffer with zeroes to a 1024-bytes length *)
let fill_block (d_len: size_nat{d_len <= block_size}) (d: lbytes d_len) : Tot (lbytes block_size) =
  let output = create block_size (u8 0) in
  update_slice output 0 d_len d

#reset-options "--z3rlimit 50 --max_fuel 1"

(** Given a position in the matrix, resolve the offset in the buffer *)
let block_offset
  (lanes:size_nat{lanes <> 0}) (columns:size_nat{columns <> 0 /\ columns*$lanes*$block_size <= max_size_t})
  (i:size_nat{i<lanes}) (j:size_nat{j<columns})
  : Tot (result:size_nat{result <= (lanes*$columns - 1)*$block_size}) =
   assert (columns*$i <= columns*$(lanes - 1));
   assert (columns*$i + j <= columns*$(lanes - 1) + (columns - 1));
   assert (columns*$i + j <= columns*$lanes - 1);
   block_size*$(columns*$i + j)

(** XORs all the buffer in the last column of the memory matrix to get a 128-bytes line *)
val xor_last_column : lanes:size_nat{lanes >= 1 /\ lanes <= pow2 24 - 1}
  -> columns:size_nat{4 <= columns /\ lanes*$columns*$block_size <= max_size_t}
  ->  mem:lbytes (lanes*$columns*$block_size)
  -> Tot (lbytes block_size)

let xor_last_column lanes columns mem =
  let block = sub mem (block_offset lanes columns 0 (columns - 1)) block_size in
  repeati (lanes-1) (fun i block ->
    let i = i + 1 in
    xor_matrices block (sub mem (block_offset lanes columns i (columns - 1)) block_size)
  ) block

(** Crafts a buffer by concatenating loop parameters *)
let concat_pseudo_rand_arg_block
  (t:size_nat) (i:size_nat) (segment:size_nat) (m':size_nat) (iterations:size_nat) (ctr:size_nat)
  : Tot (lbytes block_size) =
  let g_arg = create block_size (u8 0) in
  let g_arg = update_slice g_arg 0 8 (uint_to_bytes_le #U64 (u64 t)) in
  let g_arg = update_slice g_arg 8 16 (uint_to_bytes_le #U64 (u64 i)) in
  let g_arg = update_slice g_arg 16 24 (uint_to_bytes_le #U64 (u64 segment)) in
  let g_arg = update_slice g_arg 24 32 (uint_to_bytes_le #U64 (u64 m')) in
  let g_arg = update_slice g_arg 32 40 (uint_to_bytes_le #U64 (u64 iterations)) in
  let g_arg = update_slice g_arg 40 48 (uint_to_bytes_le #U64 (u64 argon_type)) in
  update_slice g_arg 48 56 (uint_to_bytes_le #U64 (u64 ctr))

(** Crafts the initialisation buffers for the first iteration of Argon2i *)
let concat_h0_j_i (h0:lbytes 64) (j:size_nat) (i:size_nat) : Tot (lbytes 72) =
   let output = create 72 (u8 0) in
   let output = update_slice output 0 64 h0 in
   let output = update_slice output 64 68 (uint_to_bytes_le (u32 j)) in
   update_slice output 68 72 (uint_to_bytes_le (u32 i))

(** Overwrite a block in memory with its new value *)
let update_block
  (lanes:size_nat{lanes >= 1 /\ lanes <= pow2 24 - 1}) (columns:size_nat{4 <= columns /\ lanes*$columns*$block_size <= max_size_t})
  (i:size_nat{i<lanes}) (j:size_nat{j<columns}) (memory:lbytes (lanes*$columns*$block_size)) (block:lbytes block_size)
  : Tot(lbytes(lanes*$columns*$block_size)) =
  let offset : size_nat = block_offset lanes columns i j in
  update_slice memory offset (offset + block_size) block

#reset-options "--z3rlimit 200 --max_fuel 4"

(*
    What follows is a sequence of lemmas somehow necessary for F* to prove the following result :
      a : size_nat -> a * a <= max_size_t * max_size_t
*)

let square_lemma (a:size_nat) (b:size_nat{a <= b}) : Lemma
   (ensures (a *$ a <= b *$ b))
   = ()

let square_lemma_helper (a:size_nat{a <= (pow2 32) - 1}) : Lemma
  (ensures (a *$ a <= ((pow2 32) - 1)*$((pow2 32) - 1)))
  = square_lemma a ((pow2 32) - 1)

let square_max_lemma (a:size_nat) : Lemma
  (ensures (a *$ a <= max_size_t *$ max_size_t))
  = square_lemma_helper a

(**
Given a seed j1, chooses a number in the interval [0,r_size[
See section 3.3 of the Argon2 spec
*)
let pseudo_random_generation (j1:size_nat) (r_size:size_nat{r_size <> 0}) : Tot (n:size_nat{n<r_size}) =
  let _ = square_max_lemma j1 in
  assert (j1 *$ j1 <= max_size_t*$max_size_t);
  assert (max_size_t*$max_size_t = (pow2 64) - (pow2 33) + 1);
  let tmp : n:nat{n <= (pow2 64) - (pow2 33) + 1} = j1 *$ j1 in
  let tmp : n:size_nat{n < max_size_t} = tmp / (pow2 32) in
  assert (tmp*$r_size < max_size_t*$r_size);
  let tmp : n:nat{n < max_size_t*$r_size} = tmp *$ r_size in
  let tmp : n:size_nat{n < r_size} = tmp / (pow2 32) in
  r_size - 1 - tmp

let seeds_length
  (lanes:size_nat{lanes >= 1 /\ lanes <= pow2 24 - 1})
  (columns:size_nat{4 <= columns /\ lanes*$columns*$block_size <= max_size_t})
  : size_nat =
  let segment_length = columns / 4 in
  let tmp :size_nat = segment_length / line_size + 1 in
  tmp *$ line_size *$ 2

val generate_seeds :
  lanes:size_nat{lanes >= 1 /\ lanes <= pow2 24 - 1}
  -> columns:size_nat{4 <= columns /\ lanes*$columns*$block_size <= max_size_t}
  -> i:size_nat{i < lanes}
  -> iterations:size_nat
  -> t:size_nat{t < iterations}
  -> segment:size_nat{segment < 4}
  -> lseq uint32 (seeds_length lanes columns)

let generate_seeds lanes columns i iterations t segment =
  let segment_length = columns / 4 in
  let pseudo_rands_rounds: size_nat = segment_length / line_size + 1 in
  let pseudo_rands_size : size_nat = pseudo_rands_rounds *$ line_size *$ 2 in
  repeati pseudo_rands_rounds
    (fun ctr (pseudo_rands :  lseq uint32 pseudo_rands_size)  ->
      let zero_block = create block_size (u8 0) in
      let arg_block = argon_compress
	zero_block
	(concat_pseudo_rand_arg_block t i segment (lanes*$columns) iterations (ctr+1))
      in
      let address_block = argon_compress zero_block arg_block in
      let addresses_list : lseq uint32 (2*$line_size) = uints_from_bytes_le #U32 address_block in
      update_slice pseudo_rands (ctr*$line_size*$2) ((ctr+1)*$2*$line_size) addresses_list
    ) (create pseudo_rands_size (u32 0))

val map_indexes :
  t:size_nat
  -> segment:size_nat{segment < 4}
  -> lanes:size_nat{lanes >= 1 /\ lanes <= pow2 24 - 1}
  -> columns:size_nat{4 <= columns /\ lanes*$columns*$block_size <= max_size_t}
  -> idx:size_nat{idx < columns / 4}
  -> i:size_nat{i < lanes}
  -> j:size_nat{j < columns /\ (t=0 ==> j >= 2) /\  j = segment *$ (columns / 4) + idx}
  -> j1:uint32 -> j2:uint32
  -> (i':size_nat{i' < lanes} * j':size_nat{j' < columns})

let map_indexes t segment lanes columns idx i j j1 j2 =
  let segment_length:(n:size_nat{1 <= n}) = columns / 4 in
  let i':(n:size_nat{n < lanes}) =
    if t = 0 && segment = 0 then i else ((uint_to_nat #U32 j2) % lanes)
  in
  let j':(n:size_nat{n < columns}) = (
    (* r_size is the number of computed blocks that can be reference from (i,j) *)
  //admit ();
  let r_size:(n:size_nat{n <> 0}) =
    if t = 0 then begin
      if segment = 0 || i = i' then
	j  - 1
      else if idx = 0 then
	segment*$segment_length - 1
      else
	segment*$segment_length
    end else if i = i' then
      columns - segment_length + idx - 1
    else if idx = 0 then
      columns - segment_length - 1
    else
      columns - segment_length
  in
  let r_start:size_nat = if t <> 0 && segment <> 3 then (segment + 1)*$segment_length else 0 in
  let j':size_nat = pseudo_random_generation (uint_to_nat #U32 j1) r_size in
    (r_start + j') % columns
  )
  in
  (i',j')

(**
Updates all the blocks in a segment of the memory matrix
See section 3.2 of the Argon2 spec
*)
val fill_segment : h0:lbytes 64
  -> iterations:size_nat
  -> segment:size_nat{segment < 4}
  -> t_len:size_nat{1 <= t_len /\ t_len <= max_size_t - 64}
  -> lanes:size_nat{lanes >= 1 /\ lanes <= pow2 24 - 1}
  -> columns:size_nat{4 <= columns /\ lanes*$columns*$block_size <= max_size_t}
  -> t:size_nat{t < iterations}
  -> i:size_nat{i < lanes}
  -> memory: lbytes (lanes*$columns*$block_size)
  -> Tot (lbytes (lanes*$columns*$block_size))

#reset-options "--z3rlimit 100 --max_fuel 2"

let fill_segment h0 iterations segment t_len lanes columns t i memory =
  let segment_length :size_nat = columns / 4 in
  let counter = 0 in
  let pseudo_rands_size = seeds_length lanes columns in
  let pseudo_rands = generate_seeds lanes columns i iterations t segment
  in
  (*
    Now pseudo_rands holds a large number of couples (j1,j2) which we will use to determine indexing

  *)
  repeati segment_length (fun idx (memory : lbytes (lanes*$columns*$block_size))  ->
    let j = segment *$ segment_length + idx in
    if t = 0 && j < 2 then (
       let new_block = h' block_size 72 (concat_h0_j_i h0 j i) in
       update_block lanes columns i j memory new_block
    ) else (
      let j1 = index pseudo_rands (2*$idx)  in
      let j2 = index pseudo_rands (2*$idx+1)  in
      let (i',j') = map_indexes t segment lanes columns idx i j j1 j2 in
      let arg1 : lbytes block_size =
	sub memory (block_offset lanes columns i ((j-1)%columns)) block_size
      in
      let arg2 : lbytes block_size = sub memory (block_offset lanes columns i' j') block_size in
      let new_block : lbytes block_size = argon_compress arg1 arg2 in
      if t <> 0 then
	let old_block : lbytes block_size =
	  sub memory (block_offset lanes columns i j) block_size
	in
	update_block lanes columns i j memory (xor_matrices new_block old_block)
      else
	update_block lanes columns i j memory new_block
    )
  ) memory

(**
Argon2i password-hashing function
This is the main entrypoint of the module
*)
val argon2i : p_len:size_nat -> p : lbytes p_len
  -> s_len:size_nat{s_len >= 8} -> s: lbytes s_len
  -> lanes:size_nat{lanes >= 1 /\ lanes <= pow2 24 - 1}
  -> t_len:size_nat{t_len >= 4 /\ t_len <= max_size_t - 64}
  -> m:size_nat{m >= (8*$lanes) /\ (m + 4*$lanes)*$1024 <= max_size_t}
  -> iterations:size_nat{iterations >= 1}
  -> x_len:size_nat{x_len + 4 <= max_size_t - 2*$line_size} -> x:lbytes x_len
  -> k_len:size_nat{k_len + p_len + s_len + x_len + 11*$4 <= max_size_t - 2 *$line_size} -> k:lbytes k_len
  -> Tot (lbytes (compute_variable_length_output_size t_len))

let argon2i p_len p s_len s lanes t_len m iterations x_len x k_len k =
  let h0 = concat_and_hash p_len p s_len s lanes t_len m iterations x_len x k_len k in
  let four_lanes = 4*$lanes in
  let columns = 4*$(m / four_lanes) in
  let number_of_blocks = lanes*$columns in
  let memory_size : size_nat = block_size*$number_of_blocks in
  let memory = create memory_size (u8 0) in
  assert (memory_size = columns*$lanes*$block_size);
  let memory:lbytes memory_size  = repeati iterations (fun t (memory:lbytes memory_size) ->
    repeati 4 (fun segment (memory:lbytes memory_size) ->
      repeati lanes (fun i (memory:lbytes memory_size) ->
	fill_segment h0 iterations segment t_len lanes columns t i memory
      ) memory
    ) memory
  ) memory in
  let final_block = xor_last_column lanes columns memory in
  h' t_len block_size final_block

