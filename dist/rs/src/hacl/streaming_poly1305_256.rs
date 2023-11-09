fn op_Bang_Star__Hacl_Streaming_Functor_state_s  Lib_IntVector_Intrinsics_vec256*  uint8_t*(
    p: &mut [poly1305_256_state]
) ->
    poly1305_256_state
{ p[0usize] }

fn op_Star_Equals__Hacl_Streaming_Functor_state_s  Lib_IntVector_Intrinsics_vec256*  uint8_t*(
    p: &mut [poly1305_256_state],
    v: poly1305_256_state
) ->
    ()
{ p[0usize] = v }
