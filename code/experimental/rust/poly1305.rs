#![allow(non_camel_case_types, non_snake_case, dead_code)]

type h8 = u8;
type h64 = u64;
type state = [h64; 6];
type u128 = (u64,u64);

fn constant_time_carry(a:u64, b:u64) -> u64 {
   ((a ^ ((a ^b) | ((a-b)^b))) >> 63)
}

/* Unsure about the logic here; seem to be missing some carry bits */
fn mul_wide(x:u64, y:u64) -> u128 {
   let y2 = y & 0xffffffff;
   let y1 = y >> 32;
   let x2 = x & 0xffffffff;
   let x1 = x >> 32;
   let x2y2 = x2 * y2;
   let x1y2 = x1 * y2;
   let x2y1 = x2 * y1;
   let x1y1 = x1 * y1;
   let r3 = x2y2 & 0xffffffff;
   let t3 = x2y2 >> 32;
   let t2 = x1y2 + x2y1 + t3;
   let r2 = (t2 & 0xffffffff) << 32;
   let t1 = t2 >> 32;
   let r01 = t1 + x1y1;
   let r23 = r2 + r3;
   (r01,r23) 
}

fn wrapping_add_128(x:u128,y:u128) -> u128 {
    let (x1,x2) = x;
    let (y1,y2) = y;
    let r2 = x2.wrapping_add(y2);
    let c = constant_time_carry(x2,y2);
    let r1 = x1.wrapping_add(y1).wrapping_add(c);
    (r1,r2)
}

fn shift_right_128(x:u128,y:u32) -> u128 {
    let (x1,x2) = x;
    let mask_64_m: u64 = ((y as u64) - 64) >> 63;
    let mask_64_p: u64 = (64 - (y as u64)) >> 63;
    let mask_64: u64 = !(mask_64_m | mask_64_p);
    let mask_0: u64 = ((y as u64) - 1) >> 63;

    let r1 = mask_64_m & (x1 >> y);
    let r2 = (mask_64_m & ((x2 >> y) | (!mask_0 & (x1 << (64 - y))))) |
         (mask_64_p & (x.high >> (y-64))) | (mask_64 & x1);
    (r1,r2)
}

fn load64_le (k:&[h8]) -> h64 {
   let k0 = k[0] as u64;
   let k1 = k[1] as u64;
   let k2 = k[2] as u64;
   let k3 = k[3] as u64;
   let k4 = k[4] as u64;
   let k5 = k[5] as u64;
   let k6 = k[6] as u64;
   let k7 = k[7] as u64;
   let z = k0 | 
          (k1 << 8) | 
	  (k2 << 16) | 
	  (k3 << 24) |
	  (k4 << 32) |
	  (k5 << 40) |
	  (k6 << 48) |
	  (k7 << 56) ;
   z
}

fn store64_le (k:&mut [h8],x:h64) {
   k[0] = x as u8;  
   k[1] = (x >> 8) as u8;
   k[2] = (x >> 16) as u8;
   k[3] = (x >> 24) as u8;
   k[3] = (x >> 32) as u8;
   k[3] = (x >> 40) as u8;
   k[3] = (x >> 48) as u8;
   k[3] = (x >> 56) as u8;
}

fn poly1305_init(st:&mut state,key:&[u8;32]) {
   {
    let mut h = &mut st[3..6];
    h[0] = 0;
    h[1] = 0;
    h[2] = 0;
   }
   let mut r = &mut st[0..3];
   let t0 = load64_le(&key[0..8]);
   let t1 = load64_le(&key[8..16]);
   r[0] = t0 & 0xffc0fffffff;
   r[1] = ((t0 >> 44) | (t1 << 20)) & 0xfffffc0ffff;
   r[2] = (t1 >> 24) & 0x00ffffffc0f;
}


fn poly1305_blocks_loop(st:&mut state, m:&[h8], len:u64, r0: h64, r1: h64, r2:h64,
   		        s1:h64, s2:h64, h0:h64, h1:h64, h2:h64) {
   if len < 16 {
    let mut h = &mut st[3..6];
    h[0] = h0;
    h[1] = h1;
    h[2] = h2;
   } 
   else {
    let t0 = load64_le(&m[0..8]);    
    let t1 = load64_le(&m[8..16]);    
    let mask_2_44 = 0xfffffffffff;
    let mask_2_42 = 0x3ffffffffff;
    let h0 = h0.wrapping_add((t0 & mask_2_44));
    let h1 = h1.wrapping_add((((t0 >> 44) | (t1 << 20)) & mask_2_44));
    let h2 = h2.wrapping_add((((t1 >> 24) & mask_2_42) | (1 << 40)));

    let d0 = mul_wide(h0, r0);
    let d  = mul_wide(h1, s2);
    d0 = d0.wrapping_add(d);
    d  = mul_wide(h2,s1);
    d0 = d0.wrapping_add(d);
    let d1 = mul_wide(h0,r1);
    d  = mul_wide(h1,r0);
    d1 = d1.wrapping_add(d);
    d  = mul_wide(h2,s2);
    d1 = d1.wrapping_add(d);
    let d2 = mul_wide(h0, r2);
    d  = mul_wide(h1, r1);
    d2 = d2.wrapping_add(d);
    d  = mul_wide(h2,r0);
    d2 = d2.wrapping_add(d);

    let c  = shift_right_128(d0,44);
    let cc = (0,c.1);
    h0 = d0.1 & mask_2_44;
    d1 = d1.wrapping_add(cc);

    c  = shift_right_128(d1,44);
    cc = (0,c.1);
    h1 = d1.1 & mask_2_44;
    d2 = d2.wrapping_add(cc) ;

    c  = shift_right_128(d2,44);
    cc = (0,c.1);
    h2 = d2.1 & mask_2_44;

    h0 = h0.wrapping_add(c.1.wrapping_mul(5));
    let x  = h0 >> 44;
    h0 = h0 & mask_2_44;
    h1 = h1.wrapping_add(x);
    
    poly1305_blocks_loop(st,&mut m[16..len],len - 16, r0, r1, r2, s1, s2, h0, h1, h2);

    
   }
			
}


fn main() {
    println!("Hello, world!");
}