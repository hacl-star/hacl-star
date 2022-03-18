module Hacl.Impl.EC.Precomputed

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.Loops

open FStar.Mul

open Spec.ECC
open Spec.ECC.Curves
open Hacl.Spec.EC.Definition
open Hacl.Spec.MontgomeryMultiplication

open Hacl.Impl.EC.Masking
open Hacl.Impl.EC.Masking.ScalarAccess 
open Hacl.Impl.P256.LowLevel

open Spec.ECC.Radix


#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

inline_for_extraction
let getPointI_jac (c: curve) (b: Lib.Sequence.lseq uint64 (v (getCoordinateLenU64 c) * 2 * 16) {
    forall (i: nat {i < 16}).   
      let l = v (getCoordinateLenU64 c) in
      lseq_as_nat (Lib.Sequence.sub b (2 * l * i) l) < getPrime c /\
      lseq_as_nat (Lib.Sequence.sub b (2 * l * i + l) l) < getPrime c}) 
    (i: nat {i < 16}) :  point_nat_prime #c = 
  let l = v (getCoordinateLenU64 c) in 
  let x = lseq_as_nat (Lib.Sequence.sub b (2 * l * i) l) in 
  let y = lseq_as_nat (Lib.Sequence.sub b (2 * l * i + l) l) in 
  toJacobianCoordinates (x, y)


inline_for_extraction
let points_radix_16_list_p256: x:list uint64 {List.Tot.length x == 128 /\ (
  let b = Lib.Sequence.of_list x in (
  forall (i: nat {i < 16}).
    let l = v (getCoordinateLenU64 P256) in
    lseq_as_nat (Lib.Sequence.sub b (2 * l * i) l) < getPrime P256 /\
    lseq_as_nat (Lib.Sequence.sub b (2 * l * i + l) l) < getPrime P256) /\ (  
    forall (i: nat {i < 16}). 
    let p0_i = point_mult #P256  i (basePoint #P256) in  
    let pi_fromDomain = fromDomainPoint #P256 #DH (getPointI_jac P256 b i) in 
    pointEqual pi_fromDomain p0_i))} =

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
  
    assume (forall (i: nat {i < 16}).   
      let b = Lib.Sequence.of_list x in 
      let l = v (getCoordinateLenU64 P256) in
      lseq_as_nat (Lib.Sequence.sub b (2 * l * i) l) < getPrime P256 /\
      lseq_as_nat (Lib.Sequence.sub b (2 * l * i + l) l) < getPrime P256);

    assume (
      let b = Lib.Sequence.of_list x in (
      forall (i: nat {i > 0 /\ i < 16}). 
    	let p0_i = point_mult #P256  i (basePoint #P256) in  
    	let pi_fromDomain = fromDomainPoint #P256 #DH (getPointI_jac P256 b i) in 
    	pointEqual pi_fromDomain p0_i));

  x


inline_for_extraction
let points_radix_16_list_p384: x:list uint64 {List.Tot.length x == 192 /\ (
  let b = Lib.Sequence.of_list x in (
  forall (i: nat {i < 16}).
    let l = v (getCoordinateLenU64 P384) in
    lseq_as_nat (Lib.Sequence.sub b (2 * l * i) l) < getPrime P384 /\
    lseq_as_nat (Lib.Sequence.sub b (2 * l * i + l) l) < getPrime P384) /\ (      
    forall (i: nat {i < 16}). 
    let p0_i = point_mult #P384  i (basePoint #P384) in  
    let pi_fromDomain = fromDomainPoint #P384 #DH (getPointI_jac P384 b i) in 
    pointEqual pi_fromDomain p0_i))} =
  let open FStar.Mul in 
  [@inline_let]
  let x = [ 
    u64 0x0; u64 0x0; u64 0x0; u64 0x0; u64 0x0; u64 0x0; 
    u64 0x0; u64 0x0; u64 0x0; u64 0x0; u64 0x0; u64 0x0; 

    u64 0x32f2345cb5536b82; u64 0x33ba95da2f7d6018; u64 0xf2cd7729b1c03094; u64 0x3159972fc3a90663; u64 0x5827e6777fec9ce6; u64 0x1af1e42821b04e1b; 
    u64 0xbbacc6d281184b31; u64 0x5a08d98b36984428; u64 0x73ba86bb86816030; u64 0xe77b3c32da8c0cac; u64 0x594336a7bc787585; u64 0x7d25d16cde0af6c9; 

    u64 0xf1540d582ba14b3e; u64 0x2e3457f23145b756; u64 0x3fe78dcc087cfd43; u64 0x281a423b111add53; u64 0xbd34e442a5114f1c; u64 0x3b519f3bffa3978d; 
    u64 0xb88dcc2161eb298a; u64 0x61a90c2284e4289f; u64 0x2c1a11d9238a73e1; u64 0x5bee7ef92b222947; u64 0x5cdb1c54277a3dc4; u64 0x4e0243249bf36fae; 

    u64 0x4ee989be21361f68; u64 0xafd40863847e1ec; u64 0x2c512f43cd83f0ff; u64 0xe48b4b50ed78fcc3; u64 0x9541b91d4a92a8a5; u64 0xfc09b8fb23ad6b1d; 
    u64 0xf10aa9975383b952; u64 0xde9ab5738926a227; u64 0x1f2ee4602710dc9e; u64 0x8ba5023a9baeb840; u64 0x237652a714d6dd45; u64 0x462295d6123091d3; 

    u64 0xcab20eb810602def; u64 0x8c395f33a87dd002; u64 0x2fec596c5924beac; u64 0x682b74489f1cf1e5; u64 0x490bd9a2564c7a1a; u64 0xe97a69779470060d; 
    u64 0xa2fd0fe85652626; u64 0xe6da1173a40f9c1b; u64 0x551f5e01228d56d1; u64 0xe3e4e92afae58eb9; u64 0xe84baf3a410bc2a9; u64 0x38e40f38ce54b806; 

    u64 0x575a03d904682c6; u64 0x3b1c513a911da1ec; u64 0x49244a4f32b54168; u64 0x5fd53f7cff693ebb; u64 0x92d0bb818421982d; u64 0x23cb51b8f5e404c0; 
    u64 0xe0a4c79de35bdc02; u64 0x42d14e31fad23659; u64 0x6b0b27c04f9f727e; u64 0x7452f7a9b46ead0f; u64 0x733ea8f242b7beaf; u64 0xfb39049721dbccc5; 

    u64 0x78bb9234f4efc52a; u64 0xb56de919acfc6e2e; u64 0x54feff0dea1c5ac8; u64 0xf7f299a34c38d68d; u64 0xa93c60d72804559f; u64 0x77fab5c23575c358; 
    u64 0x5efe3510a7dc82ff; u64 0x46c8fb1ee3434f87; u64 0x876eed877fc1935d; u64 0xb15f5e53c659cefc; u64 0x606d48b09f2bccac; u64 0xf22b90835d568517; 

    u64 0x4f57743cf3bbac55; u64 0x4f9f2fe49f19163c; u64 0x6bdfec70bbccb8af; u64 0xa651335f997c464d; u64 0x8f36ca3ea1f36e3d; u64 0x952f13f0b537981a; 
    u64 0x104dcf1b8ee3d83; u64 0x8aaea513ca0e5d27; u64 0x1b2cd544ccda849e; u64 0xe33a5040a6289fe; u64 0xce9de30ce002e4d0; u64 0x14c32c89a73fd5e4; 

    u64 0xf090393c563e511; u64 0x5d8fa7fb0ec9bbe6; u64 0xe14f207dc35fafc4; u64 0x4b69913b7770786; u64 0xe34d1b9807020105; u64 0xd7903931ccb65bbb; 
    u64 0x3ab44699c02a01a9; u64 0x13d57fc62b0f2ea5; u64 0xc3d135b66a95a394; u64 0x4d688cce33b6be17; u64 0xbe8737a518b6672f; u64 0x726e41af1eb169c0; 

    u64 0x41e3b3b2fe071c07; u64 0xdce07b75aa81d5d; u64 0x15bed0d8277456eb; u64 0x859db561a9bc0549; u64 0x2ad498c4f890452d; u64 0x10f2e86e0016a959; 
    u64 0x7519a47788194f3e; u64 0xea6411ae90c18dbf; u64 0xd510fed966098490; u64 0xbc8209e3702df180; u64 0xa12cbebc3e867526; u64 0xd8b1128d8c00435d; 

    u64 0x49b697ef353ba3b1; u64 0xbb54d2dbd6337dc9; u64 0xf48e5c8f3650059c; u64 0xe2b84c30b1a6d015; u64 0x6881c5bca729c88a; u64 0x2c80d8fd0ff92862; 
    u64 0x980fd9f699f80d77; u64 0x4e170e65491f0011; u64 0xdc39f58060a114d8; u64 0x3e7ae1d658c0cd11; u64 0x58a4abc6363ed354; u64 0x33bce3bfde927b1b; 

    u64 0x7bde77c8369a96f4; u64 0xad5993213577c683; u64 0x84029d386008bc1f; u64 0xf43fbc907cd9ea43; u64 0x79bee143a07c79fc; u64 0xfb21145d864cf408; 
    u64 0x5c980d203d789624; u64 0x56d8efff9e4100ff; u64 0xd212b18ba6da272b; u64 0x35ee5bf1ba5cc6f; u64 0x6ccb4f5ddc611c25; u64 0x597bc89d74c6b1e1; 

    u64 0x587f56751011395b; u64 0x7dbfba72b6d7edc9; u64 0x96bf46bbd4bf0e99; u64 0x77c9edabdc002fe0; u64 0x21bd69abe9421c26; u64 0x9de64f0b69c7dea9; 
    u64 0xcac40052cd7ab9fd; u64 0xe3288f7d04655922; u64 0x28d68b3bbb9a5f1c; u64 0x7988bc2bdfe219b4; u64 0xbbe3020d9eb46c29; u64 0x6b81bbb979c673d7; 

    u64 0x8860adb3cf4aa41; u64 0xaca9865403f1fb16; u64 0xaee8454ec4f735a2; u64 0xf2b875cd172e48f1; u64 0x989a2846aed5c186; u64 0x4907d727452e53e3; 
    u64 0xeec235cc38d73f5c; u64 0xdd072b3a970422a2; u64 0xc72d3adc399428f2; u64 0x273501e954467443; u64 0x120a7e861eb2319b; u64 0xe3d4ddf9d3e69a3a; 

    u64 0x66ae2a548bc58d5e; u64 0x412abebd62151597; u64 0xd295fe4b80e00d9f; u64 0x5db83d9f8bec48c0; u64 0x330869a025cc0464; u64 0xf3a45cc28e5fa579; 
    u64 0xb68395811ed3f011; u64 0x6abe3da17b5b49d2; u64 0x52df9a125384e282; u64 0xdbe01aa7dbefcf5a; u64 0x659954ee1ddfc5c3; u64 0x4e958f32b1188c4e; 

    u64 0x2797876f470b54c5; u64 0x4c6a43a656cf0b9c; u64 0xeebca5ad676ed03b; u64 0xae9208e7f7df959c; u64 0xd69f061b3079e553; u64 0xb81dba28e358689b; 
    u64 0x9b04ff9bdbe5cb49; u64 0x3b03c307686324ee; u64 0xe867901e57c05305; u64 0xaec776b3efdf9a57; u64 0x2efb6e881128ec96; u64 0xd86d8452f015fd7b; 



  ] in 
    assert_norm(List.Tot.length x == 192);

    assume (forall (i: nat {i < 16}).   
      let b = Lib.Sequence.of_list x in 
      let l = v (getCoordinateLenU64 P384) in
      lseq_as_nat (Lib.Sequence.sub b (2 * l * i) l) < getPrime P384 /\
      lseq_as_nat (Lib.Sequence.sub b (2 * l * i + l) l) < getPrime P384);

    assume (
      let b = Lib.Sequence.of_list x in (
      forall (i: nat {i < 16}). 
	let p0_i = point_mult #P384  i (basePoint #P384) in  
	let pi_fromDomain = fromDomainPoint #P384 #DH (getPointI_jac P384 b i) in 
	pointEqual pi_fromDomain p0_i));
    x


inline_for_extraction
let points_radix_16_list (c: curve) : x: list uint64 {List.Tot.length x == v (getCoordinateLenU64 c *! 2ul *! 16ul) /\ (
  let b = Lib.Sequence.of_list x in (
  forall (i: nat {i < 16}).
    let l = v (getCoordinateLenU64 c) in
    lseq_as_nat (Lib.Sequence.sub b (2 * l * i) l) < getPrime c /\
    lseq_as_nat (Lib.Sequence.sub b (2 * l * i + l) l) < getPrime c) /\ (      
    forall (i: nat {i > 0 /\ i < 16}). 
    let p0_i = point_mult #c  i (basePoint #c) in  
    let pi_fromDomain = fromDomainPoint #c #DH (getPointI_jac c b i) in 
    pointEqual pi_fromDomain p0_i))} =
  match c with
  | P256 -> points_radix_16_list_p256
  | P384 -> points_radix_16_list_p384


inline_for_extraction
let points_radix_16_p256: x: glbuffer uint64 128ul {
  witnessed #uint64 #(size 128) x (Lib.Sequence.of_list points_radix_16_list_p256) /\ recallable x} =
  createL_global points_radix_16_list_p256


let points_radix_16_p384: x: glbuffer uint64 192ul 
  {witnessed #uint64 #(size 192) x (Lib.Sequence.of_list points_radix_16_list_p384) /\ recallable x} = 
  createL_global points_radix_16_list_p384


inline_for_extraction
let points_radix_16 (#c: curve): x: glbuffer uint64 (getCoordinateLenU64 c *! 2ul *! 16ul) {
  witnessed #uint64 #(getCoordinateLenU64 c *! 2ul *! 16ul) x (Lib.Sequence.of_list (points_radix_16_list c)) /\ 
  recallable x} =
  match c with 
  | P256 -> points_radix_16_p256
  | P384 -> points_radix_16_p384


inline_for_extraction noextract
val copy_point_conditional_affine: #t: buftype -> #c: curve 
  -> pointToAdd: pointAffine c 
  -> x: lbuffer_t t uint64 (getCoordinateLenU64 c) 
  -> y: lbuffer_t t uint64 (getCoordinateLenU64 c)
  -> mask: uint64 {v mask = 0 \/ v mask = pow2 64 - 1} ->
  Stack unit
  (requires fun h -> 
    live h pointToAdd /\ live h x /\ live h y /\ 
    disjoint pointToAdd x /\ disjoint pointToAdd y /\
    lseq_as_nat (as_seq h x) < getPrime c /\
    lseq_as_nat (as_seq h y) < getPrime c )
  (ensures fun h0 _ h1 -> modifies (loc pointToAdd) h0 h1 /\ (
    let len = getCoordinateLenU64 c in 
    let pointToAddX = gsub pointToAdd (size 0) len in 
    let pointToAddY = gsub pointToAdd len len in 
    (v mask = pow2 64 - 1 ==> (felem_eval c h1 pointToAddX /\ felem_eval c h1 pointToAddY)) /\ (
    if v mask = 0 then
      as_nat c h1 pointToAddX == as_nat c h0 pointToAddX /\ as_nat c h1 pointToAddY == as_nat c h0 pointToAddY
    else 
      as_nat c h1 pointToAddX == lseq_as_nat (as_seq h0 x) /\ as_nat c h1 pointToAddY == lseq_as_nat (as_seq h0 y))))


let copy_point_conditional_affine #t #c pointToAdd x y mask = 
  [@inline_let]
  let len = getCoordinateLenU64 c in 
  let pointToAddX = sub pointToAdd (size 0) len in 
  let pointToAddY = sub pointToAdd len len in 

  copy_conditional #c pointToAddX x mask; 
  copy_conditional #c pointToAddY y mask


#push-options "--z3rlimit 300"

inline_for_extraction noextract
val getPointPrecomputedMixed_step: #c: curve -> i: size_t {v i < 16} 
  -> pointToAdd: pointAffine c -> mask: uint64 {v mask = 0 \/ v mask = pow2 64 - 1} ->
  Stack unit 
  (requires fun h -> live h pointToAdd)
  (ensures fun h0 _ h1 -> modifies (loc pointToAdd) h0 h1 /\ (
    let len = getCoordinateLenU64 c in 
      let pointToAddX = gsub pointToAdd (size 0) len in 
      let pointToAddY = gsub pointToAdd len len in 
    if v mask = pow2 64 - 1 then
      let pointPrecomputedJacobian =  toJacobianCoordinates (as_nat c h1 pointToAddX, as_nat c h1 pointToAddY) in 
      let pi_fromDomain = fromDomainPoint #c #DH pointPrecomputedJacobian in 
      felem_eval c h1 pointToAddX /\ felem_eval c h1 pointToAddY /\ (
      (v i < 16) ==> pointEqual pi_fromDomain (point_mult #c  (v i) (basePoint #c)))
    else
      as_nat c h0 pointToAddX == as_nat c h1 pointToAddX /\ as_nat c h0 pointToAddY == as_nat c h1 pointToAddY))


let getPointPrecomputedMixed_step #c k pointToAdd mask  = 
  let h0_ = ST.get() in 
    [@inline_let]
  let len = getCoordinateLenU64 c in 
  recall_contents (points_radix_16 #c) (Lib.Sequence.of_list (points_radix_16_list c)); 
  let lut_cmb_x = sub (points_radix_16 #c) (2ul *! len *! k) len in 
  let lut_cmb_y = sub (points_radix_16 #c) (2ul *! len *! k +! len) len in 
  copy_point_conditional_affine pointToAdd lut_cmb_x lut_cmb_y mask
  


inline_for_extraction noextract
val getPointPrecomputedMixed: #c: curve -> #buf_type: buftype -> scalar: scalar_t #buf_type #c -> 
  i:size_t {v i < v (getScalarLenBytes c) * 2} -> pointToAdd: pointAffine c ->
  Stack unit 
  (requires fun h -> live h scalar /\ live h pointToAdd)
  (ensures fun h0 _ h1 -> modifies (loc pointToAdd) h0 h1 /\ point_aff_eval c h1 pointToAdd /\ (
    let pointPrecomputedJacobian = toJacobianCoordinates (point_affine_as_nat c h1 pointToAdd) in 
    let pi_fromDomain = fromDomainPoint #c #DH pointPrecomputedJacobian in 
    let scalar = scalar_as_nat (as_seq h0 scalar) in 
    let bits = Math.Lib.arithmetic_shift_right scalar (v (getScalarLen c) - (v i + 1) * 4) % pow2 4 in
    pointEqual pi_fromDomain (point_mult #c bits (basePoint #c)) /\
    pointEqual pi_fromDomain (getPrecomputedPoint_Affine #c (basePoint #c) bits)))    

let getPointPrecomputedMixed #c scalar i pointToAdd = 
    let h0 = ST.get() in 
  let bits = getScalar_4 scalar i in 
  let invK h (k: nat) = live h pointToAdd /\ modifies (loc pointToAdd) h0 h /\ (
      let len = getCoordinateLenU64 c in 
      let pointToAddX = gsub pointToAdd (size 0) len in 
      let pointToAddY = gsub pointToAdd len len in 
   if k > v bits then
      let pointPrecomputedJacobian = toJacobianCoordinates (as_nat c h pointToAddX, as_nat c h pointToAddY) in 
      let pi_fromDomain = fromDomainPoint #c #DH pointPrecomputedJacobian in 
      felem_eval c h pointToAddX /\ felem_eval c h pointToAddY /\ 
      pointEqual pi_fromDomain (point_mult #c  (v bits) (basePoint #c))
    else
      as_nat c h0 pointToAddX == as_nat c h pointToAddX /\ as_nat c h0 pointToAddY == as_nat c h pointToAddY) in 

  Lib.Loops.for 0ul 16ul invK
    (fun k ->
      let mask = eq_mask (to_u64 bits) (to_u64 k) in 
      getPointPrecomputedMixed_step #c k pointToAdd mask
   )


(* 
prime = 2**256 - 2**224 + 2**192 + 2**96 -1

def norm(p):    
    x, y, z = p
    z2i = power_mod(z * z, -1, prime)
    z3i = power_mod(z * z * z, -1, prime)
    return ((x * z2i) % prime, (y * z3i) % prime, 1)

def toD(x):
    return x * power_mod (2 ** 256, 1, prime) % prime

def fromD(x):
    return x * power_mod (2 ** 256, prime - 2, prime) % prime

def toFakeAffine(p):
    x, y = p 
    multiplier = power_mod (2 ** 256, prime - 2, prime) 
    x = x * multiplier * multiplier % prime
    y = y * multiplier * multiplier * multiplier % prime
    return (x, y)

p256 = 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF
a256 = p256 - 3
b256 = 0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B
gx = 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296
gy = 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5
qq = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551
FF = GF(p256)

EC = EllipticCurve([FF(a256), FF(b256)])

EC.set_order(qq)

G = EC(FF(gx), FF(gy))

import __future__ 
def printf(p):
    x, y = p 
    for i in range(4):
        print(str(hex((Integer(x) >> (i * 64)) % 2 ** 64)) + "U; ", end = "")
    print("")
    for i in range(4):
        print(str (hex((Integer(y) >> (i * 64)) % 2 ** 64)) + "U; ", end = "")
    print("\n")
    
for i in range (1, 16):
    pxD = (i * G).xy()[0]
    pyD = (i * G).xy()[1]
    printf (toFakeAffine((toD (pxD), toD (pyD))))  *)


(* prime = 2^384 - 2^128 - 2^96 + 2^32 - 1
power = 384
len = 6


def norm(p):    
    x, y, z = p
    z2i = power_mod(z * z, -1, prime)
    z3i = power_mod(z * z * z, -1, prime)
    return ((x * z2i) % prime, (y * z3i) % prime, 1)

def toD(x):
    return x * power_mod (2 ** power, 1, prime) % prime

def fromD(x):
    return x * power_mod (2 ** power, prime - 2, prime) % prime

def toFakeAffine(p):
    x, y = p 
    multiplier = power_mod (2 ** power, prime - 2, prime) 
    x = x * multiplier * multiplier % prime
    y = y * multiplier * multiplier * multiplier % prime
    return (x, y)

p256 = 2^384 - 2^128 - 2^96 + 2^32 - 1
a256 = p256 - 3
b256 = 0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef

gx = 0xaa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7
gy = 0x3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f
FF = GF(p256)

EC = EllipticCurve([FF(a256), FF(b256)])

G = EC(FF(gx), FF(gy))

import __future__ 
def printf(p):
    x, y = p 
    for i in range(len):
        print("u64 " + str(hex((Integer(x) >> (i * 64)) % 2 ** 64)) + "; ", end = "")
    print("")
    for i in range(len):
        print("u64 " + str (hex((Integer(y) >> (i * 64)) % 2 ** 64)) + "; ", end = "")
    print("\n")
    
for i in range (1, 17):
    pxD = (i * G).xy()[0]
    pyD = (i * G).xy()[1]
    printf (toFakeAffine((toD (pxD), toD (pyD))))  *)
