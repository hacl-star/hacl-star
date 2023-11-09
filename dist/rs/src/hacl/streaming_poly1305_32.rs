fn op_Bang_Star__Hacl_Streaming_Functor_state_s  uint64_t*  uint8_t*(
    p: &mut [crate::hacl::streaming::poly1305_32::poly1305_32_state]
) ->
    crate::hacl::streaming::poly1305_32::poly1305_32_state
{ p[0u32 as usize] }

fn op_Star_Equals__Hacl_Streaming_Functor_state_s  uint64_t*  uint8_t*(
    p: &mut [crate::hacl::streaming::poly1305_32::poly1305_32_state],
    v: crate::hacl::streaming::poly1305_32::poly1305_32_state
) ->
    ()
{ p[0u32 as usize] = v }