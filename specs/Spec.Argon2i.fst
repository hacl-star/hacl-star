module Spec.Argon2i

#reset-options "--z3rlimit 100 --max_fuel 0"

let ( *$ ) = FStar.Mul.(( * ))
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.RawIntTypes

let version_number : uint8 = assert_norm (0x13 < maxint (U8));u8 0x13
let argon_type = 1
let block_size = 1024
let line_size = 128

val h : a_len:size_nat{0 < a_len /\ a_len <=max_size_t - 2 *$line_size} -> a:lbytes a_len -> nn:size_nat{1 <= nn /\ nn <= 64} -> Tot (lbytes nn)
let h a_len a nn =
  let null_list = [] in
  let null_key : lbytes 0 = assert_norm (List.Tot.length null_list = 0); createL #uint8 null_list in
  Spec.Blake2b.blake2b a_len a 0 null_key nn

val step1 :
  p_len:size_nat -> p : lbytes p_len ->
  s_len:size_nat -> s: lbytes s_len ->
  lanes:size_nat -> t_len:size_nat ->
  m:size_nat ->
  iterations:size_nat ->
  x_len:size_nat -> x:lbytes x_len ->
  k_len:size_nat{k_len + p_len + s_len + x_len + 11*$4 <= max_size_t - 2*$line_size} -> k:lbytes k_len ->
  Tot (lbytes 64)
let step1 p_len p s_len s lanes t_len m iterations x_len x k_len k =
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
  let blake2_argument_size : size_nat = 11*$4 + p_len + k_len + s_len + x_len in
  let blake2_argument = create blake2_argument_size (u8 0) in
  let blake2_argument = update_slice blake2_argument 0 4 lanes_as_word in
  let blake2_argument = update_slice blake2_argument 4 8 t_len_as_word in
  let blake2_argument = update_slice blake2_argument 8 12 m_as_word in
  let blake2_argument = update_slice blake2_argument 12 16 iterations_as_word in
  let blake2_argument = update_slice blake2_argument 16 20 v_as_word in
  let blake2_argument = update_slice blake2_argument 20 24 t_len_as_word in
  let blake2_argument = update_slice blake2_argument 24 28 argon_type_as_word in
  let blake2_argument = update_slice blake2_argument 28 32 p_len_as_word in
  let blake2_argument = update_slice blake2_argument 32 (32 + p_len) p in
  let offset = 32 + p_len in
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

let compute_variable_length_output_size (t_len:size_nat{t_len + 64 <= block_size}) : Tot (result:size_nat{result <= block_size}) =
  if t_len <= 64 then t_len else
    let r = (ceil_32 t_len) - 2 in
    32*$r + 64

val h' : t_len:size_nat{1 <= t_len /\ t_len + 64 <= block_size} -> x_len:size_nat{x_len + 4 <= max_size_t - 2*$line_size} -> x:lbytes x_len -> Tot (lbytes ( compute_variable_length_output_size t_len))

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
    let (output,vlast) = repeati (r-1) (fun i (output,vprevious) ->
      let i = i + 1 in (* we did the first iteration outside the loop *)
      let v = h 64 vprevious 64 in
      (update_slice output (i*$32) ((i+1)*$32) (sub v 0 32),v)
    ) (output,v1)
    in
    update_slice output (r*$32) ((r*$32)+64) vlast

let low_bits x = to_u64 #U32 (to_u32 #U64 x)

type idx = idx:size_nat{idx <= 15}

let g (a:uint64) (b:uint64) (c:uint64) (d:uint64) =
  let a = a +. b +. (u64 2) *. (low_bits a) *. (low_bits b) in
  let d = (d ^. a) >>>. (u32 32) in
  let c = c +. d +. (u64 2) *. (low_bits c) *. (low_bits d) in
  let b = (b ^. c) >>>. (u32 24) in
  let a = a +. b +. (u64 2) *. (low_bits a) *. (low_bits b) in
  let d = (d ^. a) >>>. (u32 16) in
  let c = c +. d +. (u64 2) *. (low_bits c) *. (low_bits d) in
  let b = (b ^. c) >>>. (u32 63) in
  (a,b,c,d)

let permutation_matrix_index_to_offset (i:idx) : Tot size_nat =
   if i % 2 = 0 then
     8*$((i/2)+1)
   else
     8*$(i/2)

let apply_g (v:lbytes 128) (i1:idx) (i2:idx) (i3:idx) (i4:idx) : Tot (lbytes line_size) =
  let o1 = permutation_matrix_index_to_offset i1 in
  let o2 = permutation_matrix_index_to_offset i2 in
  let o3 = permutation_matrix_index_to_offset i3 in
  let o4 = permutation_matrix_index_to_offset i4 in
  let a = uint_from_bytes_be #U64 (sub v o1 8) in
  let b = uint_from_bytes_be #U64 (sub v o2 8) in
  let c = uint_from_bytes_be #U64 (sub v o3 8) in
  let d = uint_from_bytes_be #U64 (sub v o4 8) in
  let (a,b,c,d) = g a b c d in
  let v = update_slice v o1 (o1 + 8) (uint_to_bytes_be a) in
  let v = update_slice v o2 (o2 + 8) (uint_to_bytes_be b) in
  let v = update_slice v o3 (o3 + 8) (uint_to_bytes_be c) in
  let v = update_slice v o4 (o4 + 8) (uint_to_bytes_be d) in
  v

val argon_permute : input: lbytes line_size -> Tot (lbytes line_size)
let argon_permute input =
  let v : lbytes 128 = apply_g input 0 4 8 12 in
  let v : lbytes 128 = apply_g v 1 5 9  13 in
  let v : lbytes 128 = apply_g v 2 6 10 14 in
  let v : lbytes 128 = apply_g v 3 7 11 15 in
  let v : lbytes 128 = apply_g v 0 5 10 15 in
  let v : lbytes 128 = apply_g v 1 6 11 12 in
  let v : lbytes 128 = apply_g v 2 7 8  13 in
  let v : lbytes 128 = apply_g v 3 4 9  14 in
  v


let xor_matrices (x:lbytes block_size) (y:lbytes block_size) : Tot (lbytes block_size) =
  let r = create block_size (u8 0) in
  repeati (block_size / 8) (fun i r ->
    update_slice r (8*$i) (8*$(i+1)) (uint_to_bytes_be (
      (uint_from_bytes_be #U64 (sub x (8*$i) 8)) ^. (uint_from_bytes_be #U64 (sub y (8*$i) 8))
    ))
  ) r

let extract_column_from_matrix (r: lbytes block_size) (j:size_nat{j < 8}) : Tot (lbytes line_size) =
  let output : lbytes line_size = create line_size (u8 0) in
  let output = repeati 8 (fun i output ->
    let r_offset : size_nat = i*$line_size + j*$16 in
    update_slice output (i*$16) ((i+1)*$16) (sub r r_offset 16)
  ) output
  in
  output

let update_column_to_matrix (col:lbytes line_size) (r:lbytes block_size) (j:size_nat{j < 8}) : Tot (lbytes block_size) =
  repeati 8 (fun i (r:lbytes block_size) ->
    let r_offset = i*$line_size + j*$16 in
     update_slice r r_offset (r_offset + 16) (sub col (i*$16) 16)
  ) r

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



let fill_block (d_len: size_nat{d_len <= block_size}) (d: lbytes d_len) : Tot (lbytes block_size) =
  let output = create block_size (u8 0) in
  update_slice output 0 d_len d

#reset-options "--z3rlimit 50 --max_fuel 1"

let block_offset (lanes:size_nat{lanes <> 0}) (columns:size_nat{columns <> 0 /\ columns*$lanes*$block_size <= max_size_t}) (i:size_nat{i<lanes}) (j:size_nat{j<columns}) : Tot (result:size_nat{result <= (lanes*$columns - 1)*$block_size}) =
   assert (columns*$i <= columns*$(lanes - 1));
   assert (columns*$i + j <= columns*$(lanes - 1) + (columns - 1));
   assert (columns*$i + j <= columns*$lanes - 1);
   block_size*$(columns*$i + j)

val step3 : t_len:size_nat{1 <= t_len /\ t_len <= block_size - 64} -> lanes:size_nat{lanes >= 1 /\ lanes <= pow2 24 - 1} -> columns:size_nat{1 <= columns /\ lanes*$columns*$block_size <= max_size_t} -> mem: lbytes (lanes*$columns*$block_size) -> h0:lbytes 64 -> Tot (lbytes (lanes*$columns*$block_size))

let step3 t_len lanes columns mem h0 =
  repeati lanes (fun i mem ->
    let offset: size_nat = block_offset lanes columns i 0 in
    let argument_length : size_nat = 64 + 4 + 4 in
    let argument = create argument_length (u8 0) in
    let argument = update_slice argument 0 64 h0 in
    let argument = update_slice argument (64 + 4) argument_length (uint_to_bytes_le #U32 (u32 i)) in
    let slice =
      fill_block (compute_variable_length_output_size t_len) (h' t_len argument_length argument)
    in
    update_slice mem offset (offset + block_size) slice
  ) mem


val step4 : t_len:size_nat{1 <= t_len /\ t_len <= block_size - 64} -> lanes:size_nat{lanes >= 1 /\ lanes <= pow2 24 - 1} -> columns:size_nat{4 <= columns /\ lanes*$columns*$block_size <= max_size_t} -> mem: lbytes (lanes*$columns*$block_size) -> h0:lbytes 64 -> Tot (lbytes (lanes*$columns*$block_size))

let step4 t_len lanes columns mem h0 =
  repeati lanes (fun i mem ->
    let offset: size_nat = block_offset lanes columns i 1 in
    let argument_length : size_nat = 64 + 4 + 4 in
    let argument = create argument_length (u8 0) in
    let argument = update_slice argument 0 64 h0 in
    let argument = update_slice argument 64 68 (uint_to_bytes_le #U32 (u32 1)) in
    let argument = update_slice argument (64 + 4) argument_length (uint_to_bytes_le #U32 (u32 i)) in
    let slice =
      fill_block (compute_variable_length_output_size t_len) (h' t_len argument_length argument)
    in
    update_slice mem offset (offset + block_size) slice
  ) mem

val map_indexes : iterations:size_nat -> r:size_nat -> lanes:size_nat -> columns:size_nat -> i:size_nat{i < lanes} -> j:size_nat{j < columns} -> Tot ((size_nat*size_nat))

let map_indexes iterations r lanes columns i j =
  let slice = j/4 in
  let segment_length = columns/4 in
  let g_arg_zero : lbytes block_size = create block_size (u8 0) in
  let g_arg : lbytes block_size = update_slice g_arg_zero 0 8 (uint_to_bytes_le #U64 (u64 r)) in
  let g_arg : lbytes block_size = update_slice g_arg 8 16 (uint_to_bytes_le #U64 (u64 i)) in
  let g_arg : lbytes block_size = update_slice g_arg 16 24 (uint_to_bytes_le #U64 (u64 slice)) in
  let g_arg : lbytes block_size = update_slice g_arg 24 32 (uint_to_bytes_le #U64 (u64 (lanes*$columns))) in
  let g_arg : lbytes block_size = update_slice g_arg 32 40 (uint_to_bytes_le #U64 (u64 iterations)) in
  let g_arg : lbytes block_size = update_slice g_arg 40 48 (uint_to_bytes_le #U64 (u64 argon_type)) in
  let g_arg : lbytes block_size = update_slice g_arg 48 56 (uint_to_bytes_le #U64 (u64 ((j%4) + 1))) in
  let result_block : lbytes block_size = argon_compress g_arg_zero g_arg in
  let j1 = uint_to_nat (uint_from_bytes_le #U32 (sub result_block 0 4)) in
  let j2 = uint_to_nat (uint_from_bytes_le #U32 (sub result_block 4 4)) in
  let i' = if (r = 0 && j/4 = 0) then i else j2 % lanes in
  let x = j1*$j1 / (pow2 32) in
  let (first_available_block,available_blocks) =
    (* All the blocks of the previous computed slices in selected lane, minus one if ours is first block of slice*)
    if i' = j then
      (* We select blocks in the same lane that we are computing *)
      (0, slice*$segment_length - (if j%4 = 0 then 1 else 0))
    else
      (* We select blocks from a lane that we have already computed *)
      (segment_length*$((slice+1) % 4), 3*$segment_length - (if j%4 = 0 then 1 else 0))
  in
  let y = (available_blocks*$x)/(pow2 32) in
  let z = available_blocks - 1 - y in
  let j' = (first_available_block + z) % columns in
  (i',j')

val step5 : iterations:size_nat -> t_len:size_nat{1 <= t_len /\ t_len <= block_size - 64} -> lanes:size_nat{lanes >= 1 /\ lanes <= pow2 24 - 1} -> columns:size_nat{4 <= columns /\ lanes*$columns*$block_size <= max_size_t} -> mem: lbytes (lanes*$columns*$block_size) -> Tot (lbytes (lanes*$columns*$block_size))

let step5 iterations t_len lanes columns mem =
  repeati lanes (fun i (mem: lbytes (lanes*$columns*$block_size)) ->
    repeati (columns-1) (fun j (mem:lbytes (lanes*$columns*$block_size)) ->
      let j = j + 1 in
      let offset = block_offset lanes columns i j in
      let first_block = sub mem (block_offset lanes columns i (j-1)) block_size in
      let i',j' = map_indexes iterations 1 lanes columns i j in
      let second_block = sub mem (block_offset lanes columns i' j') block_size in
      let slice = argon_compress first_block second_block  in
      update_slice mem offset (offset+ block_size) slice
    ) mem
  ) mem

val step6 : iterations:size_nat -> t_len:size_nat{1 <= t_len /\ t_len <= block_size - 64} -> lanes:size_nat{lanes >= 1 /\ lanes <= pow2 24 - 1} -> columns:size_nat{4 <= columns /\ lanes*$columns*$block_size <= max_size_t} -> mem: lbytes (lanes*$columns*$block_size) -> Tot (lbytes (lanes*$columns*$block_size))

#reset-options "--z3rlimit 500 --max_fuel 1"

let step6 iterations t_len lanes columns mem =
  if iterations <= 1 then mem else
    repeati (iterations - 1) (fun r mem ->
      let r = r + 1 in
      repeati lanes (fun i (mem: lbytes (lanes*$columns*$block_size)) ->
	repeati (columns-1) (fun j (mem:lbytes (lanes*$columns*$block_size)) ->
	  let col_idx = if j = 0 then columns - 1 else j - 1 in
	  let i',j' = map_indexes iterations r lanes columns i j in
	  let arg1 : lbytes block_size = sub mem (block_offset lanes columns i j) block_size in
	  let arg2 : lbytes block_size = argon_compress
	     (sub mem (block_offset lanes columns i col_idx) block_size)
	     (sub mem (block_offset lanes columns i' j') block_size)
	  in
	  let offset = block_offset lanes columns i j in
	  update_slice mem offset (offset + block_size) (xor_matrices arg1 arg2)
	) mem
      ) mem
    ) mem

val step7 : lanes:size_nat{lanes >= 1 /\ lanes <= pow2 24 - 1} -> columns:size_nat{4 <= columns /\ lanes*$columns*$block_size <= max_size_t} ->  mem:lbytes (lanes*$columns*$block_size) -> Tot (lbytes block_size)

let step7 lanes columns mem =
  let block = sub mem (block_offset lanes columns 0 (columns - 1)) block_size in
  repeati (lanes-1) (fun i block ->
    let i = i + 1 in
    xor_matrices block (sub mem (block_offset lanes columns i (columns - 1)) block_size)
  ) block

val argon2i :
  p_len:size_nat -> p : lbytes p_len ->
  s_len:size_nat{s_len >= 8} -> s: lbytes s_len ->
  lanes:size_nat{lanes >= 1 /\ lanes <= pow2 24 - 1} -> t_len:size_nat{t_len >= 4 /\ t_len <= block_size - 64} ->
  m:size_nat{m >= (8*$lanes) /\ (m + 4*$lanes)*$1024 <= max_size_t} ->
  iterations:size_nat{iterations >= 1}  ->
  x_len:size_nat{x_len + 4 <= max_size_t - 2*$line_size} -> x:lbytes x_len ->
  k_len:size_nat{k_len + p_len + s_len + x_len + 11*$4 <= max_size_t - 2 *$line_size} -> k:lbytes k_len ->
  Tot (lbytes (compute_variable_length_output_size t_len))

let argon2i p_len p s_len s lanes t_len m iterations x_len x k_len k =
  let h0 = step1 p_len p s_len s lanes t_len m iterations x_len x k_len k in
  let four_lanes = 4*$lanes in
  let columns = 4*$(m / four_lanes) in
  let number_of_blocks = lanes*$columns in
  let memory_size : size_nat = block_size*$number_of_blocks in
  let memory = create memory_size (u8 0) in
  assert (memory_size = columns*$lanes*$block_size);
  let memory = step3 t_len lanes columns memory h0 in
  let memory = step4 t_len lanes columns memory h0 in
  let memory = step5 iterations t_len lanes columns memory in
  let memory = step6 iterations t_len lanes columns memory in
  let final_block = step7 lanes columns memory in
  h' t_len block_size final_block
