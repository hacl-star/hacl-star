fn op_Bang_Star__Hacl_Streaming_Functor_state_s  uint64_t*  uint8_t*(
    p: &mut [poly1305_32_state]
) ->
    poly1305_32_state
{ p[0usize] }

fn op_Star_Equals__Hacl_Streaming_Functor_state_s  uint64_t*  uint8_t*(
    p: &mut [poly1305_32_state],
    v: poly1305_32_state
) ->
    ()
{ p[0usize] = v }
