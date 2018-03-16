module Spec.Argon2i

#reset-options "--z3rlimit 100 --max_fuel 0"

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.RawIntTypes

let version_number : uint8 = u8 0x13
let argon_type : nat = 1
let size_of_block = 1024

val h : a_len:size_nat{0 < a_len /\ a_len <=max_size_t - 2 * Spec.Blake2b.bytes_in_block} -> a:lbytes a_len -> nn:size_nat{1 <= nn /\ nn <= 64} -> Tot (lbytes nn)

let h a_len a nn =
  let null_list = [] in
  let null_key : lbytes 0 = assert_norm (List.Tot.length null_list = 0); createL #uint8 null_list in
  Spec.Blake2b.blake2b a_len a 0 null_key nn

val step1 :
  p_len:size_nat -> p : lbytes p_len ->
  s_len:size_nat{s_len >= 8} -> s: lbytes s_len ->
  lanes:nat{lanes >= 1 /\ lanes <= pow2 24 - 1} -> t_len:size_nat{t_len >= 4} ->
  m:size_nat{m >= (8 * lanes)} ->
  iterations:size_nat{iterations >= 1}  ->
  x_len:size_nat -> x:lbytes x_len ->
  k_len:size_nat{k_len + p_len + s_len + x_len + 11*4 <= max_size_t - 2 * Spec.Blake2b.bytes_in_block} -> k:lbytes k_len ->
  Tot (lbytes 64)

let step1 p_len p s_len s lanes t_len m iterations x_len x k_len k =
  let lanes_as_word = uint_to_bytes_le (u32 lanes) in
  let t_len_as_word = uint_to_bytes_le (u32 t_len) in
  let m_as_word = uint_to_bytes_le (u32 m) in
  let iterations_as_word = uint_to_bytes_le (u32 iterations) in
  let v_as_word = uint_to_bytes_le (to_u32 version_number) in
  let argon_type_as_word = uint_to_bytes_le (u32 argon_type) in
  let p_len_as_word = uint_to_bytes_le (u32 p_len) in
  let s_len_as_word = uint_to_bytes_le (u32 s_len) in
  let k_len_as_word = uint_to_bytes_le (u32 k_len) in
  let x_len_as_word = uint_to_bytes_le (u32 x_len) in
  let blake2_argument_size : size_nat = 11 * 4 + p_len + k_len + s_len + x_len in
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

let compute_variable_length_output_size (t_len:size_nat{t_len + 64 <= size_of_block}) : Tot (result:size_nat{result <= size_of_block}) =
  if t_len <= 64 then t_len else
    let r = (ceil_32 t_len) - 2 in
    32 * r + 64

val h' : t_len:size_nat{t_len >= 4 /\ t_len <= size_of_block - 64} -> x_len:size_nat{x_len + 4 <= max_size_t - 2 * Spec.Blake2b.bytes_in_block} -> x:lbytes x_len -> Tot (lbytes ( compute_variable_length_output_size t_len))


let h' t_len x_len x =
  let t_with_x_len : size_nat = x_len + 4 in
  let t_with_x = create t_with_x_len (u8 0) in
  let t_with_x = update_slice t_with_x 0 4 (uint_to_bytes_le (u32 t_len)) in
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
      (update_slice output (i * 32) ((i+1)*32) (sub v 0 32),v)
    ) (output,v1)
    in
    update_slice output (r * 32) ((r*32)+64) vlast


let fill_block (d_len: size_nat{d_len <= size_of_block}) (d: lbytes d_len) : Tot (lbytes size_of_block) =
  let output = create size_of_block (u8 0) in
  update_slice output 0 d_len d


val step3 : t_len:size_nat{t_len >= 4 /\ t_len <= size_of_block - 64} -> lanes:size_nat{lanes >= 1 /\ lanes <= pow2 24 - 1} -> number_of_blocks:size_nat{number_of_blocks * size_of_block <= max_size_t} -> mem_size:size_nat{mem_size= (number_of_blocks + 1) * size_of_block} -> mem: lbytes mem_size -> h0:lbytes 64 -> Tot (lbytes mem_size)

let step3 t_len lanes number_of_blocks mem_size mem h0 =
  repeati lanes (fun i mem ->
    let offset: size_nat = (number_of_blocks / lanes) * size_of_block * i in
    let argument = create (64 + 4 + 4) (u8 0) in
    let argument = update_slice argument 0 64 h0 in
    let argument = update_slice argument (64 + 4) (64 + 4 + 4) (uint_to_bytes_le (u32 i)) in
    let slice =  fill_block (compute_variable_length_output_size t_len) (h' t_len (64 + 4 + 4) argument) in
    update_slice mem offset (offset + size_of_block) slice
  ) mem

val argon2i :
  p_len:size_nat -> p : lbytes p_len ->
  s_len:size_nat{s_len >= 8} -> s: lbytes s_len ->
  lanes:size_nat{lanes >= 1 /\ lanes <= pow2 24 - 1} -> t_len:size_nat{t_len >= 4 /\ t_len <= max_size_t - 64} ->
  m:size_nat{m >= (8 * lanes) /\ (m + 4 * lanes)  * 1024 <= max_size_t} ->
  iterations:size_nat{iterations >= 1}  ->
  x_len:size_nat{x_len + 4 <= max_size_t - 2 * Spec.Blake2b.bytes_in_block} -> x:lbytes x_len ->
  k_len:size_nat{k_len + p_len + s_len + x_len + 11*4 <= max_size_t - 2 * Spec.Blake2b.bytes_in_block} -> k:lbytes k_len ->
  Tot (lbytes t_len)

let argon2i p_len p s_len s lanes t_len m iterations x_len x k_len k =
  let h0 = step1 p_len p s_len s lanes t_len m iterations x_len x k_len k in
  let four_lanes = 4 * lanes in
  let number_of_blocks = four_lanes * (m / four_lanes) in
  let memory_size : size_nat = size_of_block * number_of_blocks in
  let memory = create memory_size (u8 0) in

  create t_len (u8 0)
