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

  x[0] = x[0] + j0;
  x[1] = x[1] + j1;
  x[2] = x[2] + j2;
  x[3] = x[3] + j3;
  x[4] = x[4] + j4;
  x[5] = x[5] + j5;
  x[6] = x[6] + j6;
  x[7] = x[7] + j7;
  x[8] = x[8] + j8;
  x[9] = x[9] + j9;
  x[10] = x[10] + j10;
  x[11] = x[11] + j11;
  x[12] = x[12] + j12;
  x[13] = x[13] + j13;
  x[14] = x[14] + j14;
  x[15] = x[15] + j15;


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
   if len >= 64 { {
     let m1 = &m[0..64];
     let mut c1 = &mut c[0..64];
     chacha_encrypt_bytes_core(&ctx,&m1,&mut c1);
     }
     {
     let m2 = &m[64..len];
     let mut c2 = &mut c[64..len];
     ctx[12] = ctx[12] + 1;
     chacha_encrypt_bytes_loop(&mut ctx,&m2,&mut c2,len-64);
     }
   }
}

fn chacha_encrypt_bytes(mut ctx:&mut chacha_ctx, m:&[h8], mut c:&mut[h8], len:usize){
   chacha_encrypt_bytes_loop(&mut ctx,&m,&mut c,len);
   let rem = len & 63;
   if rem > 0 {
     let mut tmp : [h8;64] = [0;64];
     tmp[0..rem].clone_from_slice(&m[len-rem..len]);
     let mut crem = &mut c[len-rem..len];
     chacha_encrypt_bytes_core(&ctx,&tmp,&mut crem);
   }
}

fn main() {
    println!("Hello, world!");
}