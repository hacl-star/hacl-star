module GCM

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HST
open Hacl.UInt8
open Hacl.Cast
open Hacl.SBuffer
open Symmetric.AES

module U32 = FStar.UInt32

#set-options "--lax"

(* Length of each cipher block *)
let nb = 16ul

(* Define a type for all 16-byte block cipher algorithm *)
type cipher_alg (k: pos) = key:u8s ->
    input:u8s{length input = U32.v nb} ->
    out:u8s{length out = U32.v nb} ->
    Stl unit

private val gf128_add_loop: a:u8s{length a = U32.v nb} ->
    b:u8s{length b = U32.v nb} ->
    dep:u32{U32.v dep <= U32.v nb} ->
    Stl unit
let rec gf128_add_loop a b dep =
  if U32.eq dep 0ul then () else begin
    let i = U32.sub dep 1ul in
    let ai = index a i in
    let bi = index b i in
    let x = logxor ai bi in
    upd a i x;
    gf128_add_loop a b i
  end

val gf128_add: a:u8s{length a = U32.v nb} ->
    b:u8s{length b = U32.v nb} ->
    Stl unit
let gf128_add a b = gf128_add_loop a b nb

private val gf128_shift_right_loop: a:u8s{length a = U32.v nb} ->
    dep:u32{U32.v dep <= U32.v nb} ->
    Stl unit
let rec gf128_shift_right_loop a dep =
  if U32.eq dep 0ul then begin
    let ai = index a 0ul in
    let x = shift_right ai 1ul in
    upd a 0ul x
  end else begin
    let i = U32.sub dep 1ul in
    let hd = index a i in
    let tl = index a dep in
    let x = add (shift_left hd 7ul) (shift_right tl 1ul) in
    upd a dep x;
    gf128_shift_right_loop a i
  end

private val gf128_shift_right: a:u8s{length a = U32.v nb} -> Stl unit
let gf128_shift_right a = gf128_shift_right_loop a (U32.sub nb 1ul)

private val r_mul: s8
let r_mul = uint8_to_sint8 225uy

private val apply_mask_loop: a:u8s{length a = U32.v nb} ->
    m:u8s{length m = U32.v nb} ->
    msk:s8 -> dep:u32{U32.v dep <= U32.v nb} -> Stl unit
let rec apply_mask_loop a m msk dep =
  if U32.eq dep 0ul then () else begin
    let i = U32.sub dep 1ul in
    let ai = index a i in
    let x = logand ai msk in
    upd a i x;
    apply_mask_loop a m msk i
  end

private val apply_mask: a:u8s{length a = U32.v nb} ->
    m:u8s{length m = U32.v nb} ->
    msk:s8 -> Stl unit
let apply_mask a m msk = apply_mask_loop a m msk nb

private val gf128_mul_loop: a:u8s{length a = U32.v nb} ->
    b:u8s{length b = U32.v nb} ->
    r:u8s{length r = U32.v nb} ->
    m:u8s{length m = U32.v nb} ->
    dep:u32{U32.v dep <= 8 * U32.v nb} ->
    Stl unit
let rec gf128_mul_loop a b r m dep =
  if U32.eq dep (U32.mul nb 8ul) then () else begin
    let s8_1 = uint8_to_sint8 1uy in
    let i = U32.sub dep 1ul in
    let iblk = U32.div dep 8ul in
    let ibit = U32.rem dep 8ul in
    let num = index b iblk in
    let msk = eq_mask num (shift_left s8_1 (U32.sub 7ul ibit)) in
    apply_mask a m msk;
    gf128_add r m;
    let num = index a 7ul in
    let msk = eq_mask num s8_1 in
    gf128_shift_right a;
    let num = index a 0ul in
    upd a 7ul (logxor num (logand msk r_mul));
    gf128_mul_loop a b r m i
  end

val gf128_mul: a:u8s{length a = U32.v nb} ->
    b:u8s{length b = U32.v nb} ->
    Stl unit
let gf128_mul a b =
  push_frame();
  let r = create (uint8_to_sint8 0uy) nb in
  let m = create (uint8_to_sint8 0uy) nb in
  gf128_mul_loop a b r m (U32.mul nb 8ul);
  blit r 0ul a 0ul nb;
  pop_frame()

private val pre_auth_loop: tag:u8s{length tag = U32.v nb} ->
    auth_key:u8s{length auth_key = U32.v nb} ->
    ad:u8s -> adlen:u32{length ad = U32.v adlen} ->
    dep:u32 -> Stl unit
let rec pre_auth_loop tag auth_key ad adlen dep =
  if U32.gte (U32.add dep nb) adlen then begin
    push_frame();
    let last = create (uint8_to_sint8 0uy) nb in
    blit ad dep last 0ul (U32.sub adlen dep);
    gf128_add tag last;
    gf128_mul tag auth_key;
    pop_frame()
  end else begin
    let next = U32.add dep nb in
    let adi = sub ad dep nb in
    gf128_add tag adi;
    gf128_mul tag auth_key;
    pre_auth_loop tag auth_key ad adlen next
  end

(* Maybe shouldn't change input parameters *)
private val update_counter: counter:u8s{length counter = U32.v nb} ->
    num:u32 -> Stl unit
let update_counter counter num =
  upd counter 15ul (uint32_to_sint8 num);
  let num = U32.shift_right num 8ul in
  upd counter 14ul (uint32_to_sint8 num);
  let num = U32.shift_right num 8ul in
  upd counter 13ul (uint32_to_sint8 num);
  let num = U32.shift_right num 8ul in
  upd counter 12ul (uint32_to_sint8 num)

private val encrypt_loop: #k:pos -> alg:cipher_alg k ->
    ciphertext:u8s -> tag:u8s{length tag = U32.v nb} ->
    key:u8s{length key = k} -> auth_key:u8s{length auth_key = U32.v nb} ->
    counter:u8s{length counter = U32.v nb} ->
    plaintext:u8s{length plaintext = length ciphertext} ->
    len:u32{length ciphertext = U32.v len} -> dep:u32 -> Stl unit
let rec encrypt_loop #k alg ciphertext tag key auth_key counter plaintext len dep = 
  if U32.gte (U32.add dep nb) len then begin
    push_frame();
    let last = create (uint8_to_sint8 0uy) nb in
    blit plaintext dep last 0ul (U32.sub len dep);
    let cnt = U32.add (U32.div dep nb) 1ul in
    update_counter counter cnt;
    let ci = create (uint8_to_sint8 0uy) nb in
    alg key counter ci;
    gf128_add ci last;
    blit ci 0ul ciphertext dep nb;
    gf128_add tag ci;
    gf128_mul tag auth_key;
    pop_frame()
  end else begin
    let next = U32.add dep nb in
    let pi = sub plaintext dep nb in
    let cnt = U32.add (U32.div dep nb) 1ul in
    update_counter counter cnt;
    push_frame();
    let ci = create (uint8_to_sint8 0uy) nb in
    alg key counter ci;
    gf128_add ci pi;
    blit ci 0ul ciphertext dep nb;
    gf128_add tag ci;
    gf128_mul tag auth_key;
    pop_frame();
    encrypt_loop #k alg ciphertext tag key auth_key counter plaintext len next
  end

private val mk_len_info: len_info:u8s{length len_info = U32.v nb} ->
    adlen:u32 -> len:u32 -> Stl unit
let mk_len_info len_info adlen len =
  upd len_info 7ul (uint32_to_sint8 adlen);
  let adlen = U32.shift_right adlen 8ul in
  upd len_info 6ul (uint32_to_sint8 adlen);
  let adlen = U32.shift_right adlen 8ul in
  upd len_info 5ul (uint32_to_sint8 adlen);
  let adlen = U32.shift_right adlen 8ul in
  upd len_info 4ul (uint32_to_sint8 adlen);
  upd len_info 15ul (uint32_to_sint8 len);
  let len = U32.shift_right len 8ul in
  upd len_info 14ul (uint32_to_sint8 len);
  let len = U32.shift_right len 8ul in
  upd len_info 13ul (uint32_to_sint8 len);
  let len = U32.shift_right len 8ul in
  upd len_info 12ul (uint32_to_sint8 len)

val encrypt: #k:pos -> alg:cipher_alg k ->
    ciphertext:u8s -> tag:u8s{length tag = U32.v nb} ->
    key:u8s{length key = k} -> iv:u8s{length iv = 12} ->
    ad:u8s -> adlen:u32{length ad = U32.v adlen} ->
    plaintext:u8s{length plaintext = length ciphertext} ->
    len:u32{length ciphertext = U32.v len} -> Stl unit
let encrypt #k alg ciphertext tag key iv ad adlen plaintext len =
  push_frame();
  let cur_tag = create (uint8_to_sint8 0uy) nb in
  let auth_key = create (uint8_to_sint8 0uy) nb in
  alg key cur_tag auth_key;
  pre_auth_loop cur_tag auth_key ad adlen 0ul;
  let counter = create (uint8_to_sint8 0uy) nb in
  blit iv 0ul counter 0ul 12ul;
  encrypt_loop #k alg ciphertext cur_tag key auth_key counter plaintext len 0ul;
  let len_info = create (uint8_to_sint8 0uy) nb in
  mk_len_info len_info adlen len;
  gf128_add cur_tag len_info;
  gf128_mul cur_tag auth_key;
  let cnt = 0ul in
  update_counter counter cnt;
  let c0 = create (uint8_to_sint8 0uy) nb in
  alg key counter c0;
  gf128_add cur_tag c0;
  blit cur_tag 0ul tag 0ul nb;
  pop_frame()
