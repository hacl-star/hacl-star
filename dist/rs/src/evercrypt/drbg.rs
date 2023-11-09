pub const reseed_interval: u32 = 1024u32;

pub const max_output_length: u32 = 65536u32;

pub const max_length: u32 = 65536u32;

pub const max_personalization_string_length: u32 = 65536u32;

pub const max_additional_input_length: u32 = 65536u32;

pub fn create(a: crate::spec::hash_definitions::hash_alg) -> &mut [state_s] { create_in(a) }

fn op_Bang_Star__EverCrypt_DRBG_state_s(p: &mut [state_s]) -> state_s { p[0usize] }
