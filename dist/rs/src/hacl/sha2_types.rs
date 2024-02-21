#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

pub struct uint8_2p <'a> { pub fst: &'a mut [u8], pub snd: &'a mut [u8] }

pub struct uint8_3p <'a> { pub fst: &'a mut [u8], pub snd: uint8_2p <'a> }

pub struct uint8_4p <'a> { pub fst: &'a mut [u8], pub snd: uint8_3p <'a> }

pub struct uint8_5p <'a> { pub fst: &'a mut [u8], pub snd: uint8_4p <'a> }

pub struct uint8_6p <'a> { pub fst: &'a mut [u8], pub snd: uint8_5p <'a> }

pub struct uint8_7p <'a> { pub fst: &'a mut [u8], pub snd: uint8_6p <'a> }

pub struct uint8_8p <'a> { pub fst: &'a mut [u8], pub snd: uint8_7p <'a> }

pub struct uint8_2x4p <'a> { pub fst: uint8_4p <'a>, pub snd: uint8_4p <'a> }

pub struct uint8_2x8p <'a> { pub fst: uint8_8p <'a>, pub snd: uint8_8p <'a> }
