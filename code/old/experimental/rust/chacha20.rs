#![allow(non_camel_case_types, non_snake_case, dead_code)]

type h8 = u8;
type h32 = u32;
type uint8_p = [u8];
type chacha_ctx = [h32; 16];


fn load32_le (k:&[h8]) -> h32 {
   let k0 = k[0] as u32;
   let k1 = k[1] as u32;
   let k2 = k[2] as u32;
   let k3 = k[3] as u32;
   let z = k0 | (k1 << 8) | (k2 << 16) | (k3 << 24);
   z
}

fn store32_le (k:&mut [h8],x:h32) {
   k[0] = x as u8;  
   k[1] = (x >> 8) as u8;
   k[2] = (x >> 16) as u8;
   k[3] = (x >> 24) as u8;
}


fn quarter_round (m:&mut chacha_ctx, a:usize, b:usize, c:usize, d:usize) {
  m[a] = m[a].wrapping_add(m[b]);
  m[d] = m[d] ^ m[a];
  m[d] = m[d].rotate_left(16);
  m[c] = m[c].wrapping_add(m[d]);
  m[b] = m[b] ^ m[c];
  m[b] = m[b].rotate_left(12);
  m[a] = m[a].wrapping_add(m[b]);
  m[d] = m[d] ^ m[a];
  m[d] = m[d].rotate_left(8);
  m[c] = m[c].wrapping_add(m[d]);
  m[b] = m[b] ^ m[c];
  m[b] = m[b].rotate_left(7);
}

fn chacha_keysetup(ctx:&mut chacha_ctx, k: &[h8;32]) {
    ctx[0] = 0x61707865;
    ctx[1] = 0x3320646e;
    ctx[2] = 0x79622d32;
    ctx[3] = 0x6b206574;
    ctx[4] = load32_le(&k[0 .. 4]);
    ctx[5] = load32_le(&k[4 .. 8]);
    ctx[6] = load32_le(&k[8 .. 12]);
    ctx[7] = load32_le(&k[12 .. 16]);
    ctx[8] = load32_le(&k[16 .. 20]);
    ctx[9] = load32_le(&k[20 .. 24]);
    ctx[10] = load32_le(&k[24 .. 28]);
    ctx[11] = load32_le(&k[28 .. 32]);
}

fn chacha_ivsetup(ctx:&mut chacha_ctx, iv:&[h8;8], counter:&[h8;8]) {
    ctx[12] = load32_le(&counter[0 .. 4]);
    ctx[13] = load32_le(&counter[4 .. 8]);
    ctx[14] = load32_le(&iv[0..4]);
    ctx[15] = load32_le(&iv[4..8]);
}

fn chacha_ietf_ivsetup(ctx:&mut chacha_ctx, iv:&[h8;12], counter:h32) {
    ctx[12] = counter;
    ctx[13] = load32_le(&iv[0..4]);
    ctx[14] = load32_le(&iv[4..8]);
    ctx[15] = load32_le(&iv[8..12]);
}


fn chacha_encrypt_bytes_core(ctx: &chacha_ctx, m:&[h8], c:&mut[h8]){
  let j0 = ctx[0];
  let j1 = ctx[1];
  let j2 = ctx[2];
  let j3 = ctx[3];
  let j4 = ctx[4];
  let j5 = ctx[5];
  let j6 = ctx[6];
  let j7 = ctx[7];
  let j8 = ctx[8];
  let j9 = ctx[9];
  let j10 = ctx[10];
  let j11 = ctx[11];
  let j12 = ctx[12];
  let j13 = ctx[13];
  let j14 = ctx[14];
  let j15 = ctx[15];

  let mut x : chacha_ctx = ctx.clone();

  quarter_round(&mut x,0,4,8,12);
  quarter_round(&mut x,1,5,9,13); 
  quarter_round(&mut x,2,6,10,14); 
  quarter_round(&mut x,3,7,11,15); 
  quarter_round(&mut x,0,5,10,15); 
  quarter_round(&mut x,1,6,11,12); 
  quarter_round(&mut x,2,7,8,13); 
  quarter_round(&mut x,3,4,9,14); 

  quarter_round(&mut x,0,4,8,12);
  quarter_round(&mut x,1,5,9,13); 
  quarter_round(&mut x,2,6,10,14); 
  quarter_round(&mut x,3,7,11,15); 
  quarter_round(&mut x,0,5,10,15); 
  quarter_round(&mut x,1,6,11,12); 
  quarter_round(&mut x,2,7,8,13); 
  quarter_round(&mut x,3,4,9,14); 

  quarter_round(&mut x,0,4,8,12);
  quarter_round(&mut x,1,5,9,13); 
  quarter_round(&mut x,2,6,10,14); 
  quarter_round(&mut x,3,7,11,15); 
  quarter_round(&mut x,0,5,10,15); 
  quarter_round(&mut x,1,6,11,12); 
  quarter_round(&mut x,2,7,8,13); 
  quarter_round(&mut x,3,4,9,14); 

  quarter_round(&mut x,0,4,8,12);
  quarter_round(&mut x,1,5,9,13); 
  quarter_round(&mut x,2,6,10,14); 
  quarter_round(&mut x,3,7,11,15); 
  quarter_round(&mut x,0,5,10,15); 
  quarter_round(&mut x,1,6,11,12); 
  quarter_round(&mut x,2,7,8,13); 
  quarter_round(&mut x,3,4,9,14); 

  quarter_round(&mut x,0,4,8,12);
  quarter_round(&mut x,1,5,9,13); 
  quarter_round(&mut x,2,6,10,14); 
  quarter_round(&mut x,3,7,11,15); 
  quarter_round(&mut x,0,5,10,15); 
  quarter_round(&mut x,1,6,11,12); 
  quarter_round(&mut x,2,7,8,13); 
  quarter_round(&mut x,3,4,9,14); 

  quarter_round(&mut x,0,4,8,12);
  quarter_round(&mut x,1,5,9,13); 
  quarter_round(&mut x,2,6,10,14); 
  quarter_round(&mut x,3,7,11,15); 
  quarter_round(&mut x,0,5,10,15); 
  quarter_round(&mut x,1,6,11,12); 
  quarter_round(&mut x,2,7,8,13); 
  quarter_round(&mut x,3,4,9,14); 

  quarter_round(&mut x,0,4,8,12);
  quarter_round(&mut x,1,5,9,13); 
  quarter_round(&mut x,2,6,10,14); 
  quarter_round(&mut x,3,7,11,15); 
  quarter_round(&mut x,0,5,10,15); 
  quarter_round(&mut x,1,6,11,12); 
  quarter_round(&mut x,2,7,8,13); 
  quarter_round(&mut x,3,4,9,14); 

  quarter_round(&mut x,0,4,8,12);
  quarter_round(&mut x,1,5,9,13); 
  quarter_round(&mut x,2,6,10,14); 
  quarter_round(&mut x,3,7,11,15); 
  quarter_round(&mut x,0,5,10,15); 
  quarter_round(&mut x,1,6,11,12); 
  quarter_round(&mut x,2,7,8,13); 
  quarter_round(&mut x,3,4,9,14); 

  quarter_round(&mut x,0,4,8,12);
  quarter_round(&mut x,1,5,9,13); 
  quarter_round(&mut x,2,6,10,14); 
  quarter_round(&mut x,3,7,11,15); 
  quarter_round(&mut x,0,5,10,15); 
  quarter_round(&mut x,1,6,11,12); 
  quarter_round(&mut x,2,7,8,13); 
  quarter_round(&mut x,3,4,9,14); 

  quarter_round(&mut x,0,4,8,12);
  quarter_round(&mut x,1,5,9,13); 
  quarter_round(&mut x,2,6,10,14); 
  quarter_round(&mut x,3,7,11,15); 
  quarter_round(&mut x,0,5,10,15); 
  quarter_round(&mut x,1,6,11,12); 
  quarter_round(&mut x,2,7,8,13); 
  quarter_round(&mut x,3,4,9,14); 

  x[0] = x[0].wrapping_add(j0);
  x[1] = x[1].wrapping_add(j1);
  x[2] = x[2].wrapping_add(j2);
  x[3] = x[3].wrapping_add(j3);
  x[4] = x[4].wrapping_add(j4);
  x[5] = x[5].wrapping_add(j5);
  x[6] = x[6].wrapping_add(j6);
  x[7] = x[7].wrapping_add(j7);
  x[8] = x[8].wrapping_add(j8);
  x[9] = x[9].wrapping_add(j9);
  x[10] = x[10].wrapping_add(j10);
  x[11] = x[11].wrapping_add(j11);
  x[12] = x[12].wrapping_add(j12);
  x[13] = x[13].wrapping_add(j13);
  x[14] = x[14].wrapping_add(j14);
  x[15] = x[15].wrapping_add(j15);


  let m0 = load32_le(&m[0..4]);
  let m1 = load32_le(&m[4..8]);
  let m2 = load32_le(&m[8..12]);
  let m3 = load32_le(&m[12..16]);
  let m4 = load32_le(&m[16..20]);
  let m5 = load32_le(&m[20..24]);
  let m6 = load32_le(&m[24..28]);
  let m7 = load32_le(&m[28..32]);
  let m8 = load32_le(&m[32..36]);
  let m9 = load32_le(&m[36..40]);
  let m10 = load32_le(&m[40..44]);
  let m11 = load32_le(&m[44..48]);
  let m12 = load32_le(&m[48..52]);
  let m13 = load32_le(&m[52..56]);
  let m14 = load32_le(&m[56..60]);
  let m15 = load32_le(&m[60..64]);

  x[0] = x[0] ^ m0;
  x[1] = x[1] ^ m1;
  x[2] = x[2] ^ m2;
  x[3] = x[3] ^ m3;
  x[4] = x[4] ^ m4;
  x[5] = x[5] ^ m5;
  x[6] = x[6] ^ m6;
  x[7] = x[7] ^ m7;
  x[8] = x[8] ^ m8;
  x[9] = x[9] ^ m9;
  x[10] = x[10] ^ m10;
  x[11] = x[11] ^ m11;
  x[12] = x[12] ^ m12;
  x[13] = x[13] ^ m13;
  x[14] = x[14] ^ m14;
  x[15] = x[15] ^ m15;
  
  store32_le(&mut c[0..4],x[0]);
  store32_le(&mut c[4..8],x[1]);
  store32_le(&mut c[8..12],x[2]);
  store32_le(&mut c[12..16],x[3]);
  store32_le(&mut c[16..20],x[4]);
  store32_le(&mut c[20..24],x[5]);
  store32_le(&mut c[24..28],x[6]);
  store32_le(&mut c[28..32],x[7]);
  store32_le(&mut c[32..36],x[8]);
  store32_le(&mut c[36..40],x[9]);
  store32_le(&mut c[40..44],x[10]);
  store32_le(&mut c[44..48],x[11]);
  store32_le(&mut c[48..52],x[12]);
  store32_le(&mut c[52..56],x[13]);
  store32_le(&mut c[56..60],x[14]);
  store32_le(&mut c[60..64],x[15]);
}

fn chacha_encrypt_bytes_loop(mut ctx:&mut chacha_ctx,m:&[h8],mut c:&mut[h8],len:usize) {
   let mut curr = 0;
   while len - curr >= 64 {
     let m1 = &m[0..64];
     let mut c1 = &mut c[0..64];
     chacha_encrypt_bytes_core(&ctx,&m1,&mut c1);
     curr = curr + 64;     
     ctx[12] = ctx[12] + 1;
   }
}

fn chacha_encrypt_bytes(mut ctx:&mut chacha_ctx, m:&[h8], mut c:&mut[h8], len:usize){
   chacha_encrypt_bytes_loop(&mut ctx,&m,&mut c,len);
   let rem = len & 63;
   if rem > 0 {
     let mut tmp_m : [h8;64] = [0;64];
     tmp_m[0..rem].clone_from_slice(&m[len-rem..len]);
     let mut tmp_c : [h8;64] = [0;64];
     chacha_encrypt_bytes_core(&ctx,&tmp_m,&mut tmp_c);
     for i in 0..rem {  
        c[len-rem+i] = tmp_c[i];
     }
   }
}

fn chacha20(mut c:&mut[h8],m:&[h8], len:usize, k:&[h8;32], n:&[h8;12], ctr:u32) {
  let mut ctx: chacha_ctx = [0, 0, 0, 0, 0, 0, 0, 0, 
      	   	         0, 0, 0, 0, 0, 0, 0, 0];
   chacha_keysetup(&mut ctx,k);
   chacha_ietf_ivsetup(&mut ctx,n,ctr);
   chacha_encrypt_bytes(&mut ctx,m,&mut c,len);
}


fn main() { 
  let plain: [h8;114] = [
    0x4cu8, 0x61u8, 0x64u8, 0x69u8, 0x65u8, 0x73u8, 0x20u8, 0x61u8,
    0x6eu8, 0x64u8, 0x20u8, 0x47u8, 0x65u8, 0x6eu8, 0x74u8, 0x6cu8,
    0x65u8, 0x6du8, 0x65u8, 0x6eu8, 0x20u8, 0x6fu8, 0x66u8, 0x20u8,
    0x74u8, 0x68u8, 0x65u8, 0x20u8, 0x63u8, 0x6cu8, 0x61u8, 0x73u8,
    0x73u8, 0x20u8, 0x6fu8, 0x66u8, 0x20u8, 0x27u8, 0x39u8, 0x39u8,
    0x3au8, 0x20u8, 0x49u8, 0x66u8, 0x20u8, 0x49u8, 0x20u8, 0x63u8,
    0x6fu8, 0x75u8, 0x6cu8, 0x64u8, 0x20u8, 0x6fu8, 0x66u8, 0x66u8,
    0x65u8, 0x72u8, 0x20u8, 0x79u8, 0x6fu8, 0x75u8, 0x20u8, 0x6fu8,
    0x6eu8, 0x6cu8, 0x79u8, 0x20u8, 0x6fu8, 0x6eu8, 0x65u8, 0x20u8,
    0x74u8, 0x69u8, 0x70u8, 0x20u8, 0x66u8, 0x6fu8, 0x72u8, 0x20u8,
    0x74u8, 0x68u8, 0x65u8, 0x20u8, 0x66u8, 0x75u8, 0x74u8, 0x75u8,
    0x72u8, 0x65u8, 0x2cu8, 0x20u8, 0x73u8, 0x75u8, 0x6eu8, 0x73u8,
    0x63u8, 0x72u8, 0x65u8, 0x65u8, 0x6eu8, 0x20u8, 0x77u8, 0x6fu8,
    0x75u8, 0x6cu8, 0x64u8, 0x20u8, 0x62u8, 0x65u8, 0x20u8, 0x69u8,
    0x74u8, 0x2eu8];

  let cipher: [h8;114] = [
    0x6eu8, 0x2eu8, 0x35u8, 0x9au8, 0x25u8, 0x68u8, 0xf9u8, 0x80u8,
    0x41u8, 0xbau8, 0x07u8, 0x28u8, 0xddu8, 0x0du8, 0x69u8, 0x81u8,
    0xe9u8, 0x7eu8, 0x7au8, 0xecu8, 0x1du8, 0x43u8, 0x60u8, 0xc2u8,
    0x0au8, 0x27u8, 0xafu8, 0xccu8, 0xfdu8, 0x9fu8, 0xaeu8, 0x0bu8,
    0xf9u8, 0x1bu8, 0x65u8, 0xc5u8, 0x52u8, 0x47u8, 0x33u8, 0xabu8,
    0x8fu8, 0x59u8, 0x3du8, 0xabu8, 0xcdu8, 0x62u8, 0xb3u8, 0x57u8,
    0x16u8, 0x39u8, 0xd6u8, 0x24u8, 0xe6u8, 0x51u8, 0x52u8, 0xabu8,
    0x8fu8, 0x53u8, 0x0cu8, 0x35u8, 0x9fu8, 0x08u8, 0x61u8, 0xd8u8,
    0x07u8, 0xcau8, 0x0du8, 0xbfu8, 0x50u8, 0x0du8, 0x6au8, 0x61u8,
    0x56u8, 0xa3u8, 0x8eu8, 0x08u8, 0x8au8, 0x22u8, 0xb6u8, 0x5eu8,
    0x52u8, 0xbcu8, 0x51u8, 0x4du8, 0x16u8, 0xccu8, 0xf8u8, 0x06u8,
    0x81u8, 0x8cu8, 0xe9u8, 0x1au8, 0xb7u8, 0x79u8, 0x37u8, 0x36u8,
    0x5au8, 0xf9u8, 0x0bu8, 0xbfu8, 0x74u8, 0xa3u8, 0x5bu8, 0xe6u8,
    0xb4u8, 0x0bu8, 0x8eu8, 0xedu8, 0xf2u8, 0x78u8, 0x5eu8, 0x42u8,
    0x87u8, 0x4du8];

  let key: [h8;32] = [
    0u8,   1u8,  2u8,  3u8,  4u8,  5u8,  6u8,  7u8,
    8u8,   9u8, 10u8, 11u8, 12u8, 13u8, 14u8, 15u8,
    16u8, 17u8, 18u8, 19u8, 20u8, 21u8, 22u8, 23u8,
    24u8, 25u8, 26u8, 27u8, 28u8, 29u8, 30u8, 31u8
    ];

  let nonce:[h8;12] = [
    0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0x4au8, 0u8, 0u8, 0u8, 0u8
    ];

  let counter: u32 = 1;

  let mut test_cipher: [h8;114] = [0; 114];
  chacha20(&mut test_cipher,&plain,114,&key,&nonce,counter);

  for i in 0..114 {
     if test_cipher[i] != cipher[i]  {
         println!("chacha20 failure!");
     }
  }
  println!("chacha20 success!");
}