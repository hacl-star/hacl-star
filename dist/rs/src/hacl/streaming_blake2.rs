fn op_Bang_Star__Hacl_Streaming_Functor_state_s  uint32_t* *  uint32_t* ()(
    p: &mut [blake2s_32_state]
) ->
    blake2s_32_state
{ p[0usize] }

fn op_Star_Equals__Hacl_Streaming_Functor_state_s  uint32_t* *  uint32_t* ()(
    p: &mut [blake2s_32_state],
    v: blake2s_32_state
) ->
    ()
{ p[0usize] = v }

fn op_Bang_Star__Hacl_Streaming_Functor_state_s  uint64_t* *  uint64_t* ()(
    p: &mut [blake2b_32_state]
) ->
    blake2b_32_state
{ p[0usize] }

fn op_Star_Equals__Hacl_Streaming_Functor_state_s  uint64_t* *  uint64_t* ()(
    p: &mut [blake2b_32_state],
    v: blake2b_32_state
) ->
    ()
{ p[0usize] = v }
