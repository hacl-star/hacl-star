#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]

pub struct uint8_2p <'a> { pub fst: &'a mut [u8], pub snd: &'a mut [u8] }

pub struct uint8_3p <'a> { pub fst: &'a mut [u8], pub snd: uint8_2p }

pub struct uint8_4p <'a> { pub fst: &'a mut [u8], pub snd: uint8_3p }

pub struct uint8_5p <'a> { pub fst: &'a mut [u8], pub snd: uint8_4p }

pub struct uint8_6p <'a> { pub fst: &'a mut [u8], pub snd: uint8_5p }

pub struct uint8_7p <'a> { pub fst: &'a mut [u8], pub snd: uint8_6p }

pub struct uint8_8p <'a> { pub fst: &'a mut [u8], pub snd: uint8_7p }

pub struct uint8_2x4p <'a> { pub fst: uint8_4p, pub snd: uint8_4p }

pub struct uint8_2x8p <'a> { pub fst: uint8_8p, pub snd: uint8_8p }
