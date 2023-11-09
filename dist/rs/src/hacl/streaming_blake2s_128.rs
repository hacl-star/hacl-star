fn
op_Bang_Star__Hacl_Streaming_Functor_state_s  Lib_IntVector_Intrinsics_vec128* *  Lib_IntVector_Intrinsics_vec128* ()(
    p: &mut [blake2s_128_state]
) ->
    blake2s_128_state
{ p[0usize] }

fn
op_Star_Equals__Hacl_Streaming_Functor_state_s  Lib_IntVector_Intrinsics_vec128* *  Lib_IntVector_Intrinsics_vec128* ()(
    p: &mut [blake2s_128_state],
    v: blake2s_128_state
) ->
    ()
{ p[0usize] = v }
