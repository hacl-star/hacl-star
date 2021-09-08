module Hacl.Impl.EC.Precomputed

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.Loops

open FStar.Mul

open Spec.ECC.Curves



#set-options "--fuel 0 --ifuel 0 --z3rlimit 200"

inline_for_extraction
let points_radix_16_list_p256: x:list uint64 {List.Tot.length x == 128} =
  let open FStar.Mul in 
  [@inline_let]
  let x = [ 
    u64 0x0; u64 0x0; u64 0x0; u64 0x0; 
    u64 0x0; u64 0x0; u64 0x0; u64 0x0; 

    u64 0x1fb38ab1388ad777; u64 0x1dfee06615fa309d; u64 0xfcac986c3afea4a7; u64 0xdf65c2da29fb821a; 
    u64 0xeff44e23f63f8f6d; u64 0xaa02cd3ed4b681a4; u64 0xdd5fda3363818af8; u64 0xfc53bc2629fbf0b3; 

    u64 0x12631d721b91beea; u64 0x5f73f2d3a11a09f8; u64 0xac41f54484d5fcd8; u64 0x86578e5c56025df4; 
    u64 0x577c956b15ed6b5a; u64 0xb59c5f77982d848; u64 0xb7c5e2c190fcdcc2; u64 0x7d64d13ef1c91ffd; 

    u64 0xd40c2d6273f9d9f1; u64 0x4dc6f628063ef17c; u64 0x498e81df7ab17aa5; u64 0xabb2a5026f17173c; 
    u64 0x4a3d7527f6739ef3; u64 0xd941003268184c91; u64 0xd2d458b8d401508b; u64 0xb7437ab810ac5451; 

    u64 0x5256d9bdab491252; u64 0x972d326eb1084c12; u64 0xc3e96455e2ec3bfa; u64 0xb75c723b549a10ff; 
    u64 0x9d9185f9f8a18961; u64 0x2200a07b8589ba82; u64 0x637b9d96fd4e9f5e; u64 0xce75bfb2575e6cfa; 

    u64 0x7dd4477db8b77c7d; u64 0x80818a776e5503b0; u64 0x6fc7d58fb59581d; u64 0xd899fb87efe43022; 
    u64 0x23b9912111694135; u64 0x7e5de7bac33fa1c8; u64 0xb3b83722a70e7d43; u64 0xf06cfecbfb9bb38f; 

    u64 0xaa39277dfa93656; u64 0x3dabb6cce67c5201; u64 0x473ffb8bf1f94677; u64 0xb9f0b93637453e56; 
    u64 0x8fce12ec20958fb2; u64 0xcc16d74ff7786061; u64 0x3678438a8235d096; u64 0xe39ea044f06b43f6; 

    u64 0xbb40bdb5775c9950; u64 0xd244a74cdc703cdd; u64 0x83dc1b8a6105dd53; u64 0x38d9d50d49ef0437; 
    u64 0x58be44eba6096472; u64 0x960afaec386fa5c5; u64 0x1440032e000134b9; u64 0x601e721454d6ba96; 

    u64 0x79ec42228671b9b6; u64 0xfdc00dc48df9e25c; u64 0x44500833d71d2e77; u64 0x2bda4c3c0bc103d5; 
    u64 0x51528408aa925d53; u64 0xefcb55b9c2f3a37d; u64 0x9f28f6bb9846c915; u64 0xe1547ce1d8340e55; 

    u64 0x97e310c1995b3ed2; u64 0xed861937196256e6; u64 0x1c6762abff2c65f2; u64 0x268345e0978fcedd; 
    u64 0x35ca2e572b784881; u64 0x28ac888da0acd1b7; u64 0x305640dc06a41baf; u64 0x997c6fd2cb671bfb; 

    u64 0xf40d9eaf4a31e15a; u64 0x8991dd7d54cfe03a; u64 0x4889a3463a8deb0c; u64 0x4cbf48092cd0a1fa; 
    u64 0xc6965c4fbe18fb8c; u64 0x1d499d0cb216fa84; u64 0x8d5fe52c705dd3eb; u64 0x812b268f84313b34; 

    u64 0x313b58808261591a; u64 0xc2c322508f53d933; u64 0xa49ef3f95094ed1b; u64 0x13e326786e98c63; 
    u64 0x34be8167cd460429; u64 0x698a328099a6b31; u64 0xb9be3ba51b0c922d; u64 0xe59cca03f7674ed; 
    
    u64 0x4fbf7e505d3aca7c; u64 0x2f4f8ba62020715; u64 0x840502262ac1ec42; u64 0xb8e0532775197de7; 
    u64 0x9142a358cf4e9b4b; u64 0xc86a3c567e5d8626; u64 0xd4051282b4a7992a; u64 0xe7573c5999e3974e;
    
    u64 0xd814a606da7bd76b; u64 0x15604730f38cb788; u64 0xbd195f868fbdd6c4; u64 0xdb96f5b00a51d3f7; 
    u64 0xe1385c8a9b507fea; u64 0x878e27813ee7310; u64 0x6d7d8b12aea7e096; u64 0x54978ad11e2f5cca; 
    
    u64 0x49fffd6c3c4d07d4; u64 0x703638f71fab7a5d; u64 0xbed6e367fcc73960; u64 0x215e161835a61d75; 
    u64 0xe52288a5e87a660b; u64 0xf1d127ee3c802cb5; u64 0xccde3c6aafc46044; u64 0xdc11c08ef14cff32; 

    u64 0x29216f9ceca46668; u64 0x22e584a3b2891c5e; u64 0xe6deecd7810f6d87; u64 0x6aff4b94a55659a3; 
   u64 0x12b59bb6d2e9f876; u64 0x27ed01943aa02eab; u64 0x8d6d420841f57075; u64 0xe7b47285ef60a461;   
  ] in 
  
    assert_norm(List.Tot.length x == 128);
    x


let points_radix_16_list (c: curve) : x: list uint64 {
  List.Tot.length x == v (16ul *! 2ul *! getCoordinateLenU64 c)} =
  match c with 
  |P256 -> points_radix_16_list_p256
  |_ -> admit()



inline_for_extraction
let points_radix_p256_16: x: glbuffer uint64 (128ul)
  {witnessed #uint64 #(size 128) x (Lib.Sequence.of_list points_radix_16_list_p256) /\ recallable x} = 
  createL_global points_radix_16_list_p256

open Hacl.Spec.EC.Definition
open Spec.ECC
open Hacl.Spec.MontgomeryMultiplication


inline_for_extraction
let points_radix_16_buffer (#c: curve): 
  (x: glbuffer uint64 (16ul *! 2ul *! getCoordinateLenU64 c) {
    witnessed #uint64 #(16ul *! 2ul *! getCoordinateLenU64 c) x (Lib.Sequence.of_list (points_radix_16_list c)) /\ 
    recallable x /\ (
    let len = v (getCoordinateLenU64 c) in 
    let points_radix_16_seq = Lib.Sequence.of_list (points_radix_16_list c) in
    forall (i: nat {i < 16}). 
      let pointX = lseq_as_nat (Lib.Sequence.sub points_radix_16_seq (i * (2 * len)) len) in 
      let pointY = lseq_as_nat (Lib.Sequence.sub points_radix_16_seq (i * (2 * len) + len) len) in 
      pointX < getPrime c /\ pointY < getPrime c /\
      pointEqual (fromDomainPoint #c #DH (pointX, pointY, 1)) == pointEqual (point_mult i (basePoint #c)))}) = 
  match c with 
  |P256 -> admit(); points_radix_p256_16
  |_ -> admit()


