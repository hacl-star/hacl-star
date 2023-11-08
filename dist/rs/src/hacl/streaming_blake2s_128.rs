fn
op_Bang_Star__Hacl_Streaming_Functor_state_s  Lib_IntVector_Intrinsics_vec128* *  Lib_IntVector_Intrinsics_vec128* ()(
  p: &mut [crate::hacl::streaming::blake2s_128::blake2s_128_state]
) ->
  crate::hacl::streaming::blake2s_128::blake2s_128_state
{ p[0u32 as usize] }

fn
op_Star_Equals__Hacl_Streaming_Functor_state_s  Lib_IntVector_Intrinsics_vec128* *  Lib_IntVector_Intrinsics_vec128* ()(
  p: &mut [crate::hacl::streaming::blake2s_128::blake2s_128_state],
  v: crate::hacl::streaming::blake2s_128::blake2s_128_state
) ->
  ()
{ p[0u32 as usize] = v }