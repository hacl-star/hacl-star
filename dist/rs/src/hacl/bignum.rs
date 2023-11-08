pub fn mod_inv_uint32(n0: u32) -> u32
{
  let alpha: u32 = 2147483648u32;
  let beta: u32 = n0;
  let mut ub: u32 = 0u32;
  let mut vb: u32 = 0u32;
  ub = 1u32;
  vb = 0u32;
  for i in 0u32..32u32
  {
    let us: u32 = ub;
    let vs: u32 = vb;
    let u_is_odd: u32 = 0u32.wrapping_sub(us & 1u32);
    let beta_if_u_is_odd: u32 = beta & u_is_odd;
    ub = (us ^ beta_if_u_is_odd).wrapping_shr(1u32).wrapping_add(us & beta_if_u_is_odd);
    let alpha_if_u_is_odd: u32 = alpha & u_is_odd;
    vb = vs.wrapping_shr(1u32).wrapping_add(alpha_if_u_is_odd)
  };
  vb
}

pub fn mod_inv_uint64(n0: u64) -> u64
{
  let alpha: u64 = 9223372036854775808u64;
  let beta: u64 = n0;
  let mut ub: u64 = 0u64;
  let mut vb: u64 = 0u64;
  ub = 1u64;
  vb = 0u64;
  for i in 0u32..64u32
  {
    let us: u64 = ub;
    let vs: u64 = vb;
    let u_is_odd: u64 = 0u64.wrapping_sub(us & 1u64);
    let beta_if_u_is_odd: u64 = beta & u_is_odd;
    ub = (us ^ beta_if_u_is_odd).wrapping_shr(1u32).wrapping_add(us & beta_if_u_is_odd);
    let alpha_if_u_is_odd: u64 = alpha & u_is_odd;
    vb = vs.wrapping_shr(1u32).wrapping_add(alpha_if_u_is_odd)
  };
  vb
}