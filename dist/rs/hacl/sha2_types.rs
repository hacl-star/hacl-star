#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

pub struct uint8_2p <'a> { pub fst: &'a mut [u8], pub snd: &'a mut [u8] }

pub struct uint8_3p <'a> { pub fst: &'a mut [u8], pub snd: crate::sha2_types::uint8_2p <'a> }

pub struct uint8_4p <'a> { pub fst: &'a mut [u8], pub snd: crate::sha2_types::uint8_3p <'a> }

pub(crate) struct uint8_5p <'a>
{ pub fst: &'a mut [u8], pub snd: crate::sha2_types::uint8_4p <'a> }

pub(crate) struct uint8_6p <'a>
{ pub fst: &'a mut [u8], pub snd: crate::sha2_types::uint8_5p <'a> }

pub(crate) struct uint8_7p <'a>
{ pub fst: &'a mut [u8], pub snd: crate::sha2_types::uint8_6p <'a> }

pub(crate) struct uint8_8p <'a>
{ pub fst: &'a mut [u8], pub snd: crate::sha2_types::uint8_7p <'a> }

pub(crate) struct uint8_2x4p <'a>
{ pub fst: crate::sha2_types::uint8_4p <'a>, pub snd: crate::sha2_types::uint8_4p <'a> }

pub(crate) struct uint8_2x8p <'a>
{ pub fst: crate::sha2_types::uint8_8p <'a>, pub snd: crate::sha2_types::uint8_8p <'a> }

pub type bufx1 <'a> = &'a [u8];

pub type bufx4 <'a> = crate::sha2_types::uint8_4p <'a>;
