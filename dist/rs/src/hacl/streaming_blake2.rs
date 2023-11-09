fn op_Bang_Star__Hacl_Streaming_Functor_state_s  uint32_t* *  uint32_t* ()(
    p: &mut [crate::hacl::streaming::blake2::blake2s_32_state]
) ->
    crate::hacl::streaming::blake2::blake2s_32_state
{ p[0usize] }

fn op_Star_Equals__Hacl_Streaming_Functor_state_s  uint32_t* *  uint32_t* ()(
    p: &mut [crate::hacl::streaming::blake2::blake2s_32_state],
    v: crate::hacl::streaming::blake2::blake2s_32_state
) ->
    ()
{ p[0usize] = v }

fn op_Bang_Star__Hacl_Streaming_Functor_state_s  uint64_t* *  uint64_t* ()(
    p: &mut [crate::hacl::streaming::blake2::blake2b_32_state]
) ->
    crate::hacl::streaming::blake2::blake2b_32_state
{ p[0usize] }

fn op_Star_Equals__Hacl_Streaming_Functor_state_s  uint64_t* *  uint64_t* ()(
    p: &mut [crate::hacl::streaming::blake2::blake2b_32_state],
    v: crate::hacl::streaming::blake2::blake2b_32_state
) ->
    ()
{ p[0usize] = v }