pub fn eq_mask(a: u32, b: u32) -> u32
{
  let x = a ^ b;
  let minus_x = (!x).wrapping_add(1u32);
  let x_or_minus_x = x | minus_x;
  let xnx = x_or_minus_x.wrapping_shr(31);
  return xnx.wrapping_sub(1u32);
}

pub fn gte_mask(a: u32, b: u32) -> u32
{
  let x = a;
  let y = b;
  let x_xor_y = x ^ y;
  let x_sub_y = x.wrapping_sub(y);
  let x_sub_y_xor_y = x_sub_y ^ y;
  let q = x_xor_y | x_sub_y_xor_y;
  let x_xor_q = x ^ q;
  let x_xor_q_ = x_xor_q.wrapping_shr(31);
  return x_xor_q_.wrapping_sub(1u32);
}
