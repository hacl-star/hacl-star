module Hacl.Bignum.Crecip

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Limb
open Hacl.Bignum.Fsquare
open Hacl.Bignum.Fmul
open Hacl.Spec.Bignum.Crecip
open Hacl.Spec.EC.AddAndDouble


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

private let lemma_53_is_5413 (s:seqelem{red_53 s}) : Lemma (red_5413 s) = ()
private let lemma_513_is_53 (s:seqelem{red_513 s}) : Lemma (red_53 s) = ()
private let lemma_513_is_55 (s:seqelem{red_513 s}) : Lemma (red_55 s) = ()
private let lemma_513_is_5413 (s:seqelem{red_513 s}) : Lemma (red_5413 s) = ()
private let lemma_513_is_52 (s:seqelem{red_513 s}) : Lemma (red_52 s) = ()
private let lemma_5413_is_55 (s:seqelem{red_5413 s}) : Lemma (Hacl.Spec.EC.AddAndDouble.red_55 s) = ()

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

[@"substitute"]
private val fmul:
  output:felem ->
  a:felem ->
  b:felem ->
  Stack unit
    (requires (fun h -> live h output /\ live h a /\ live h b
      /\ red_513 (as_seq h a) /\ red_513 (as_seq h b)))
    (ensures (fun h0 _ h1 -> live h0 output /\ live h0 a /\ live h0 b
      /\ red_513 (as_seq h0 a) /\ red_513 (as_seq h0 b)
      /\ modifies_1 output h0 h1 /\ live h1 output
      /\ red_513 (as_seq h1 output)
      /\ Hacl.Spec.Bignum.Fmul.fmul_pre (as_seq h0 a) (as_seq h0 b)
      /\ eval h1 output % prime = (eval h0 a * eval h0 b) % prime
      /\ as_seq h1 output == Hacl.Spec.Bignum.fmul_tot (as_seq h0 a) (as_seq h0 b)
      ))
[@"substitute"]
private let fmul output a b =
  let h = ST.get() in
  lemma_513_is_53 (as_seq h a);
  lemma_513_is_55 (as_seq h b);
  fmul_53_55_is_fine (as_seq h a) (as_seq h b);
  fmul output a b


#reset-options "--max_fuel 0 --z3rlimit 50"

[@"substitute"]
private val fsquare_times:
  output:felem ->
  input:felem{disjoint output input} ->
  count:FStar.UInt32.t{FStar.UInt32.v count > 0} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input
      /\ red_513 (as_seq h input)))
    (ensures (fun h0 _ h1 -> live h0 output /\ live h1 output /\ live h0 input /\ modifies_1 output h0 h1
      /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h0 input)
      /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h1 output)
      /\ (as_seq h1 output) == Hacl.Spec.Bignum.Fsquare.fsquare_times_tot (as_seq h0 input) (FStar.UInt32.v count)))
[@"substitute"]
private let fsquare_times output input count =
  let h = ST.get() in
  lemma_513_is_5413 (as_seq h input);
  fsquare_times output input count


[@"substitute"]
private val fsquare_times_inplace:
  output:felem ->
  count:FStar.UInt32.t{FStar.UInt32.v count > 0} ->
  Stack unit
    (requires (fun h -> live h output /\ red_513 (as_seq h output)))
    (ensures (fun h0 _ h1 -> live h0 output /\ live h1 output /\ modifies_1 output h0 h1
      /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h0 output)
      /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h1 output)
      /\ (as_seq h1 output) == Hacl.Spec.Bignum.Fsquare.fsquare_times_tot (as_seq h0 output) (FStar.UInt32.v count)))
[@"substitute"]
private let fsquare_times_inplace output count =
  let h = ST.get() in
  lemma_513_is_5413 (as_seq h output);
  fsquare_times_inplace output count


private val lemma_crecip_1_modifies': h0:mem -> h1:mem -> b:buffer limb -> Lemma (requires (equal_domains h0 h1 /\ live h0 b /\ modifies_1 b h0 h1))
  (ensures (live h1 b))
private let lemma_crecip_1_modifies' h0 h1 b = lemma_reveal_modifies_1  b h0 h1
 

private val lemma_crecip_1_modifies'': h0:mem -> h1:mem -> h2:mem -> h3:mem -> h4:mem -> h5:mem -> h6:mem -> h7:mem -> buf:buffer limb{length buf = 20} ->
  Lemma (requires (
    let a  = Buffer.sub buf 0ul  5ul in
    let t0 = Buffer.sub buf 5ul  5ul in
    let b  = Buffer.sub buf 10ul 5ul in
    let c  = Buffer.sub buf 15ul 5ul in
    live h0 buf /\ modifies_1 a h0 h1 /\ modifies_1 t0 h1 h2 /\ modifies_1 b h2 h3 /\ modifies_1 a h3 h4
    /\ modifies_1 t0 h4 h5 /\ modifies_1 b h5 h6 /\ modifies_1 t0 h6 h7 /\ equal_domains h0 h7))
        (ensures (modifies_1 buf h0 h7))
private let lemma_crecip_1_modifies'' h0 h1 h2 h3 h4 h5 h6 h7 buf = ()

private val lemma_crecip_1_modifies: h0:mem -> h1:mem -> h2:mem -> h3:mem -> h4:mem -> h5:mem -> h6:mem -> h7:mem -> buf:buffer limb{length buf = 20} ->
  Lemma (requires (
    let a  = Buffer.sub buf 0ul  5ul in
    let t0 = Buffer.sub buf 5ul  5ul in
    let b  = Buffer.sub buf 10ul 5ul in
    let c  = Buffer.sub buf 15ul 5ul in
    live h0 buf /\ modifies_1 a h0 h1 /\ modifies_1 t0 h1 h2 /\ modifies_1 b h2 h3 /\ modifies_1 a h3 h4
    /\ modifies_1 t0 h4 h5 /\ modifies_1 b h5 h6 /\ modifies_1 t0 h6 h7 /\ equal_domains h0 h7))
        (ensures (modifies_1 buf h0 h7 /\ live h7 buf))
private let lemma_crecip_1_modifies h0 h1 h2 h3 h4 h5 h6 h7 buf =
  lemma_crecip_1_modifies'' h0 h1 h2 h3 h4 h5 h6 h7 buf;
  lemma_crecip_1_modifies' h0 h7 buf


[@"substitute"]
private val crecip_1:
  buf:buffer limb{length buf = 20} ->
  z:felem{disjoint buf z} ->
  Stack unit
  (requires (fun h -> live h buf /\ live h z /\ crecip_pre (as_seq h z)))
  (ensures (fun h0 _ h1 -> live h1 z /\ live h1 buf /\ modifies_1 buf h0 h1 /\ live h0 buf /\ live h0 z
    /\ crecip_pre (as_seq h0 z)
    /\ (let a  = Buffer.sub buf 0ul  5ul in
       let t0 = Buffer.sub buf 5ul  5ul in
       let b  = Buffer.sub buf 10ul 5ul in
       let c  = Buffer.sub buf 15ul 5ul in
       crecip_pre (as_seq h1 t0)
       /\ crecip_pre (as_seq h1 b)
       /\ crecip_pre (as_seq h1 a)
       /\ ( (as_seq h1 t0, as_seq h1 b, as_seq h1 a)  == crecip_tot_1 (as_seq h0 z)))
  ))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"
[@"substitute"]
private let crecip_1 buf z =
  let a  = Buffer.sub buf 0ul  5ul in
  let t0 = Buffer.sub buf 5ul  5ul in
  let b  = Buffer.sub buf 10ul 5ul in
  let c  = Buffer.sub buf 15ul 5ul in
  (**) lemma_disjoint_sub buf a z;
  (**) lemma_disjoint_sub buf t0 z;
  (**) lemma_disjoint_sub buf b z;
  (**) lemma_disjoint_sub buf c z;
  let h0 = ST.get() in
  fsquare_times a z 1ul;
  let h1 = ST.get() in
  (**) modifies_subbuffer_1 h0 h1 a buf;
  no_upd_lemma_1 h0 h1 a z;
  fsquare_times t0 a 2ul;
  let h2 = ST.get() in
  (**) modifies_subbuffer_1 h1 h2 t0 buf;
  no_upd_lemma_1 h1 h2 t0 z;
  no_upd_lemma_1 h1 h2 t0 a;
  fmul b t0 z;
  let h3 = ST.get() in
  (**) modifies_subbuffer_1 h2 h3 b buf;
  no_upd_lemma_1 h2 h3 b a;
  fmul a b a;
  let h4 = ST.get() in
  (**) modifies_subbuffer_1 h3 h4 a buf;
  fsquare_times t0 a 1ul;
  let h5 = ST.get() in
  (**) modifies_subbuffer_1 h4 h5 t0 buf;
  no_upd_lemma_1 h3 h4 a b;
  no_upd_lemma_1 h4 h5 t0 b;
  fmul b t0 b;
  let h6 = ST.get() in
  (**) modifies_subbuffer_1 h5 h6 b buf;
  fsquare_times t0 b 5ul;
  let h7 = ST.get() in
  (**) modifies_subbuffer_1 h6 h7 t0 buf;
  no_upd_lemma_1 h6 h7 t0 b;
  no_upd_lemma_1 h4 h5 t0 a;
  no_upd_lemma_1 h5 h6 b  a;
  no_upd_lemma_1 h6 h7 t0 a;
  lemma_crecip_1_modifies h0 h1 h2 h3 h4 h5 h6 h7 buf


private val lemma_crecip_2_modifies: h0:mem -> h1:mem -> h2:mem -> h3:mem -> h4:mem -> h5:mem -> h6:mem -> h7:mem -> h8:mem -> buf:buffer limb{length buf = 20} ->
  Lemma (requires (
    let a  = Buffer.sub buf 0ul  5ul in
    let t0 = Buffer.sub buf 5ul  5ul in
    let b  = Buffer.sub buf 10ul 5ul in
    let c  = Buffer.sub buf 15ul 5ul in
    live h0 buf /\ modifies_1 b h0 h1 /\ modifies_1 t0 h1 h2 /\ modifies_1 c h2 h3 /\ modifies_1 t0 h3 h4
    /\ modifies_1 t0 h4 h5 /\ modifies_1 t0 h5 h6 /\ modifies_1 b h6 h7 /\ modifies_1 t0 h7 h8 /\ equal_domains h0 h8))
        (ensures (modifies_1 buf h0 h8 /\ live h8 buf))
private let lemma_crecip_2_modifies h0 h1 h2 h3 h4 h5 h6 h7 h8 buf =
  cut (modifies_1 buf h0 h8);
  lemma_crecip_1_modifies' h0 h8 buf


[@"substitute"]
private val crecip_2:
  buf:buffer limb{length buf = 20} ->
  Stack unit
  (requires (fun h -> live h buf
    /\ (let a  = Buffer.sub buf 0ul  5ul in
       let t0 = Buffer.sub buf 5ul  5ul in
       let b  = Buffer.sub buf 10ul 5ul in
       let c  = Buffer.sub buf 15ul 5ul in
       red_513 (as_seq h t0)
       /\ red_513 (as_seq h b)
       /\ red_513 (as_seq h a))
      ))
  (ensures (fun h0 _ h1 -> live h1 buf /\ modifies_1 buf h0 h1 /\ live h0 buf
    /\ (let a  = Buffer.sub buf 0ul  5ul in
       let t0 = Buffer.sub buf 5ul  5ul in
       let b  = Buffer.sub buf 10ul 5ul in
       let c  = Buffer.sub buf 15ul 5ul in
       red_513 (as_seq h0 t0)
       /\ red_513 (as_seq h0 b)
       /\ red_513 (as_seq h0 a)
       /\ crecip_pre (as_seq h1 t0)
       /\ crecip_pre (as_seq h1 b)
       /\ crecip_pre (as_seq h1 a)
       /\ ( (as_seq h1 t0, as_seq h1 b, as_seq h1 a)  == crecip_tot_2 (as_seq h0 t0) (as_seq h0 b) (as_seq h0 a)))
  ))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 200"
[@"substitute"]
private let crecip_2 buf =
  assert_norm(pow2 32 = 0x100000000);
  let a  = Buffer.sub buf 0ul  5ul in
  let t0 = Buffer.sub buf 5ul  5ul in
  let b  = Buffer.sub buf 10ul 5ul in
  let c  = Buffer.sub buf 15ul 5ul in
  let h0 = ST.get() in
  fmul b t0 b;
  let h1 = ST.get() in
  no_upd_lemma_1 h0 h1 b a;
  (* no_upd_lemma_1 h0 h1 b t0; *)
  fsquare_times t0 b 10ul;
  let h2 = ST.get() in
  (* no_upd_lemma_1 h1 h2 b t0; *)
  no_upd_lemma_1 h1 h2 t0 a;
  fmul c t0 b;
  let h3 = ST.get() in
  no_upd_lemma_1 h2 h3 c b;
  no_upd_lemma_1 h2 h3 c a;
  (* no_upd_lemma_1 h2 h3 c t0; *)
  fsquare_times t0 c 20ul;
  let h4 = ST.get() in
  no_upd_lemma_1 h3 h4 t0 b;
  no_upd_lemma_1 h3 h4 t0 a;
  fmul t0 t0 c;
  let h5 = ST.get() in
  no_upd_lemma_1 h4 h5 t0 b;
  no_upd_lemma_1 h4 h5 t0 a;
  fsquare_times_inplace t0 10ul;
  let h6 = ST.get() in
  no_upd_lemma_1 h5 h6 t0 b;
  no_upd_lemma_1 h5 h6 t0 a;
  fmul b t0 b;
  let h7 = ST.get() in
  no_upd_lemma_1 h6 h7 b a;
  no_upd_lemma_1 h6 h7 b t0;
  fsquare_times t0 b 50ul;
  let h8 = ST.get() in
  no_upd_lemma_1 h7 h8 t0 a;
  no_upd_lemma_1 h7 h8 t0 b;
  cut (red_513 (as_seq h8 b));
  cut (red_513 (as_seq h8 a));
  cut (red_513 (as_seq h8 t0));
  lemma_crecip_2_modifies h0 h1 h2 h3 h4 h5 h6 h7 h8 buf


private val lemma_crecip_3_modifies: h0:mem -> h1:mem -> h2:mem -> h3:mem -> h4:mem -> h5:mem -> h6:mem -> h7:mem -> buf:buffer limb{length buf = 20} -> out:felem{disjoint buf out} ->
  Lemma (requires (
    let a  = Buffer.sub buf 0ul  5ul in
    let t0 = Buffer.sub buf 5ul  5ul in
    let b  = Buffer.sub buf 10ul 5ul in
    let c  = Buffer.sub buf 15ul 5ul in
    live h0 buf /\ live h0 out
    /\ modifies_1 c h0 h1 /\ modifies_1 t0 h1 h2 /\ modifies_1 t0 h2 h3 /\ modifies_1 t0 h3 h4
    /\ modifies_1 t0 h4 h5 /\ modifies_1 t0 h5 h6 /\ modifies_1 out h6 h7 /\ equal_domains h0 h7))
        (ensures (modifies_2 out buf h0 h7 /\ live h7 out))
private let lemma_crecip_3_modifies h0 h1 h2 h3 h4 h5 h6 h7 buf out =
  let a  = Buffer.sub buf 0ul  5ul in
  let t0 = Buffer.sub buf 5ul  5ul in
  let b  = Buffer.sub buf 10ul 5ul in
  let c  = Buffer.sub buf 15ul 5ul in
  lemma_reveal_modifies_1 c h0 h1;
  lemma_reveal_modifies_1 t0 h1 h2;
  lemma_reveal_modifies_1 t0 h2 h3;
  lemma_reveal_modifies_1 t0 h3 h4;
  lemma_reveal_modifies_1 t0 h4 h5;
  lemma_reveal_modifies_1 t0 h5 h6;
  lemma_reveal_modifies_1 out h6 h7


[@"substitute"]
private val crecip_3:
  out:felem ->
  buf:buffer limb{length buf = 20 /\ disjoint out buf} ->
  Stack unit
  (requires (fun h -> live h buf /\ live h out
    /\ (let a  = Buffer.sub buf 0ul  5ul in
       let t0 = Buffer.sub buf 5ul  5ul in
       let b  = Buffer.sub buf 10ul 5ul in
       let c  = Buffer.sub buf 15ul 5ul in
       red_513 (as_seq h t0)
       /\ red_513 (as_seq h b)
       /\ red_513 (as_seq h a))
      ))
  (ensures (fun h0 _ h1 -> live h1 out /\ modifies_2 out buf h0 h1 /\ live h0 buf
     /\ crecip_pre (as_seq h1 out)
     /\ (let a  = Buffer.sub buf 0ul  5ul in
       let t0 = Buffer.sub buf 5ul  5ul in
       let b  = Buffer.sub buf 10ul 5ul in
       let c  = Buffer.sub buf 15ul 5ul in 
       red_513 (as_seq h0 t0)
       /\ red_513 (as_seq h0 b)
       /\ red_513 (as_seq h0 a)
       /\ as_seq h1 out  == crecip_tot_3 (as_seq h0 t0) (as_seq h0 b) (as_seq h0 a))
  ))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"
[@"substitute"]
private let crecip_3 out buf =
  assert_norm(pow2 32 = 0x100000000);
  let a  = Buffer.sub buf 0ul  5ul in
  let t0 = Buffer.sub buf 5ul  5ul in
  let b  = Buffer.sub buf 10ul 5ul in
  let c  = Buffer.sub buf 15ul 5ul in
  let h0 = ST.get() in
  fmul c t0 b;
  let h1 = ST.get() in
  no_upd_lemma_1 h0 h1 c b;
  no_upd_lemma_1 h0 h1 c t0;
  no_upd_lemma_1 h0 h1 c a;
  fsquare_times t0 c 100ul;
  let h2 = ST.get() in
  no_upd_lemma_1 h1 h2 t0 b;
  no_upd_lemma_1 h1 h2 t0 a;
  fmul t0 t0 c;
  let h3 = ST.get() in
  no_upd_lemma_1 h2 h3 t0 b;
  no_upd_lemma_1 h2 h3 t0 a;
  fsquare_times_inplace t0 50ul;
  let h4 = ST.get() in
  no_upd_lemma_1 h3 h4 t0 b;
  no_upd_lemma_1 h3 h4 t0 a;
  fmul t0 t0 b;
  let h5 = ST.get() in
  no_upd_lemma_1 h4 h5 t0 a;
  fsquare_times_inplace t0 5ul;
  let h6 = ST.get() in
  no_upd_lemma_1 h5 h6 t0 a;
  fmul out t0 a;
  let h7 = ST.get() in
  lemma_crecip_3_modifies h0 h1 h2 h3 h4 h5 h6 h7 buf out


[@"substitute"]
private val crecip_3':
  out:felem ->
  buf:buffer limb{length buf = 20 /\ disjoint out buf} ->
  Stack unit
  (requires (fun h -> live h buf /\ live h out
    /\ (let a  = Buffer.sub buf 0ul  5ul in
       let t0 = Buffer.sub buf 5ul  5ul in
       let b  = Buffer.sub buf 10ul 5ul in
       let c  = Buffer.sub buf 15ul 5ul in
       red_513 (as_seq h t0)
       /\ red_513 (as_seq h b)
       /\ red_513 (as_seq h a))
      ))
  (ensures (fun h0 _ h1 -> live h1 out /\ modifies_2 out buf h0 h1 /\ live h0 buf
     /\ crecip_pre (as_seq h1 out)
     /\ (let a  = Buffer.sub buf 0ul  5ul in
       let t0 = Buffer.sub buf 5ul  5ul in
       let b  = Buffer.sub buf 10ul 5ul in
       let c  = Buffer.sub buf 15ul 5ul in 
       red_513 (as_seq h0 t0)
       /\ red_513 (as_seq h0 b)
       /\ red_513 (as_seq h0 a)
       /\ as_seq h1 out  == crecip_tot_3' (as_seq h0 t0) (as_seq h0 b) (as_seq h0 a))
  ))
#reset-options "--max_fuel 0 --z3rlimit 100"
[@"substitute"]
private let crecip_3' out buf =
  assert_norm(pow2 32 = 0x100000000);
  let a  = Buffer.sub buf 0ul  5ul in
  let t0 = Buffer.sub buf 5ul  5ul in
  let b  = Buffer.sub buf 10ul 5ul in
  let c  = Buffer.sub buf 15ul 5ul in
  let h0 = ST.get() in
  fmul c t0 b;
  let h1 = ST.get() in
  no_upd_lemma_1 h0 h1 c b;
  no_upd_lemma_1 h0 h1 c t0;
  no_upd_lemma_1 h0 h1 c a;
  fsquare_times t0 c 100ul;
  let h2 = ST.get() in
  no_upd_lemma_1 h1 h2 t0 b;
  no_upd_lemma_1 h1 h2 t0 a;
  fmul t0 t0 c;
  let h3 = ST.get() in
  no_upd_lemma_1 h2 h3 t0 b;
  no_upd_lemma_1 h2 h3 t0 a;
  fsquare_times_inplace t0 50ul;
  let h4 = ST.get() in
  no_upd_lemma_1 h3 h4 t0 b;
  no_upd_lemma_1 h3 h4 t0 a;
  fmul t0 t0 b;
  let h5 = ST.get() in
  no_upd_lemma_1 h4 h5 t0 a;
  fsquare_times_inplace t0 2ul;
  let h6 = ST.get() in
  no_upd_lemma_1 h5 h6 t0 a;
  fmul out t0 a;
  let h7 = ST.get() in
  lemma_crecip_3_modifies h0 h1 h2 h3 h4 h5 h6 h7 buf out


[@"c_inline"]
val crecip:
  out:felem ->
  z:felem{disjoint out z} ->
  Stack unit
  (requires (fun h -> live h out /\ live h z /\ crecip_pre (as_seq h z)))
  (ensures (fun h0 _ h1 -> live h1 out /\ modifies_1 out h0 h1 /\ live h0 z
    /\ crecip_pre (as_seq h0 z)
    /\ as_seq h1 out == crecip_tot (as_seq h0 z)
    /\ crecip_pre (as_seq h1 out)))
[@"c_inline"]
let crecip out z =
  (**) let hinit = ST.get() in
  push_frame();
  (**) let h0 = ST.get() in
  let buf = create limb_zero 20ul in
  (**) let h1 = ST.get() in
  (**) no_upd_lemma_0 h0 h1 out;
  crecip_1 buf z;
  (**) let h2 = ST.get() in
  (**) no_upd_lemma_1 h1 h2 buf out;
  crecip_2 buf;
  (**) let h3 = ST.get() in
  (**) no_upd_lemma_1 h2 h3 buf out;
  (**) lemma_modifies_1_trans buf h1 h2 h3;
  crecip_3 out buf;
  (**) let h4 = ST.get() in
  (**) lemma_modifies_1_2''' buf out h1 h3 h4;
  (**) lemma_modifies_0_2 out buf h0 h1 h4;
  pop_frame();
  (**) let hfin = ST.get() in
  (**) modifies_popped_1 out hinit h0 h4 hfin


[@"c_inline"]
val crecip':
  out:felem ->
  z:felem{disjoint out z} ->
  Stack unit
  (requires (fun h -> live h out /\ live h z /\ crecip_pre (as_seq h z)))
  (ensures (fun h0 _ h1 -> live h1 out /\ modifies_1 out h0 h1 /\ live h0 z
    /\ crecip_pre (as_seq h0 z)
    /\ as_seq h1 out == crecip_tot' (as_seq h0 z)
    /\ crecip_pre (as_seq h1 out)))

#reset-options "--max_fuel 0 --z3rlimit 100"

[@"c_inline"]
let crecip' out z =
  (**) let hinit = ST.get() in
  push_frame();
  (**) let h0 = ST.get() in
  let buf = create limb_zero 20ul in
  (**) let h1 = ST.get() in
  let h  = ST.get() in
  crecip_1 buf z;
  (**) let h2 = ST.get() in
  crecip_2 buf;
  (**) let h3 = ST.get() in
  (**) lemma_modifies_1_trans buf h1 h2 h3;
  let h' = ST.get() in
  no_upd_lemma_1 h h' buf z;
  let a  = Buffer.sub buf 0ul  5ul in
  let t0 = Buffer.sub buf 5ul  5ul in
  let b  = Buffer.sub buf 10ul 5ul in
  let c  = Buffer.sub buf 15ul 5ul in
  let h  = ST.get() in
  fsquare_times a z 1ul;
  (**) let h4 = ST.get() in
  (**) modifies_subbuffer_1 h3 h4 a buf;
  (**) lemma_modifies_1_trans buf h1 h3 h4;
  let h' = ST.get() in
  no_upd_lemma_1 h h' a t0;
  no_upd_lemma_1 h h' a b;
  no_upd_lemma_1 h h' a c;
  no_upd_lemma_1 h h' a z;
  crecip_3' out buf;
  (**) let h5 = ST.get() in
  (**) lemma_modifies_1_2''' buf out h1 h4 h5;
  (**) lemma_modifies_0_2 out buf h0 h1 h5;
  pop_frame();
  (**) let hfin = ST.get() in
  (**) modifies_popped_1 out hinit h0 h5 hfin
