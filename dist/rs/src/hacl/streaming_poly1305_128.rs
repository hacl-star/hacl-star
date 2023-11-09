fn op_Bang_Star__Hacl_Streaming_Functor_state_s  Lib_IntVector_Intrinsics_vec128*  uint8_t*(
    p: &mut [poly1305_128_state]
) ->
    poly1305_128_state
{ p[0usize] }

fn op_Star_Equals__Hacl_Streaming_Functor_state_s  Lib_IntVector_Intrinsics_vec128*  uint8_t*(
    p: &mut [poly1305_128_state],
    v: poly1305_128_state
) ->
    ()
{ p[0usize] = v }
