fn
op_Bang_Star__Hacl_Streaming_Functor_state_s  Lib_IntVector_Intrinsics_vec256* *  Lib_IntVector_Intrinsics_vec256* ()(
    p: &mut [blake2b_256_state]
) ->
    blake2b_256_state
{ p[0usize] }

fn
op_Star_Equals__Hacl_Streaming_Functor_state_s  Lib_IntVector_Intrinsics_vec256* *  Lib_IntVector_Intrinsics_vec256* ()(
    p: &mut [blake2b_256_state],
    v: blake2b_256_state
) ->
    ()
{ p[0usize] = v }
