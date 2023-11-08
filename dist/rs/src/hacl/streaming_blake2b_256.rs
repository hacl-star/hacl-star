fn
op_Bang_Star__Hacl_Streaming_Functor_state_s  Lib_IntVector_Intrinsics_vec256* *  Lib_IntVector_Intrinsics_vec256* ()(
  p: &mut [crate::hacl::streaming::blake2b_256::blake2b_256_state]
) ->
  crate::hacl::streaming::blake2b_256::blake2b_256_state
{ p[0u32 as usize] }

fn
op_Star_Equals__Hacl_Streaming_Functor_state_s  Lib_IntVector_Intrinsics_vec256* *  Lib_IntVector_Intrinsics_vec256* ()(
  p: &mut [crate::hacl::streaming::blake2b_256::blake2b_256_state],
  v: crate::hacl::streaming::blake2b_256::blake2b_256_state
) ->
  ()
{ p[0u32 as usize] = v }