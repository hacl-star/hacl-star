#include "Hacl_Symmetric_Salsa20.h"

uint32_t Hacl_Symmetric_Salsa20_rotate(uint32_t a, uint32_t s)
{
  return a << s | a >> (uint32_t )32 - s;
}

uint32_t Hacl_Symmetric_Salsa20_load32_le(uint8_t *k)
{
  uint8_t k0 = k[(uint32_t )0];
  uint8_t k1 = k[(uint32_t )1];
  uint8_t k2 = k[(uint32_t )2];
  uint8_t k3 = k[(uint32_t )3];
  return
    (uint32_t )k0
    | (uint32_t )k1 << (uint32_t )8
    | (uint32_t )k2 << (uint32_t )16
    | (uint32_t )k3 << (uint32_t )24;
}

void Hacl_Symmetric_Salsa20_store32_le(uint8_t *k, uint32_t x)
{
  k[(uint32_t )0] = (uint8_t )x;
  k[(uint32_t )1] = (uint8_t )(x >> (uint32_t )8);
  k[(uint32_t )2] = (uint8_t )(x >> (uint32_t )16);
  k[(uint32_t )3] = (uint8_t )(x >> (uint32_t )24);
}

void Hacl_Symmetric_Salsa20_crypto_core_salsa20(uint8_t *output, uint8_t *input, uint8_t *key)
{
  uint32_t x00 = (uint32_t )0x61707865;
  uint32_t x50 = (uint32_t )0x3320646e;
  uint32_t x100 = (uint32_t )0x79622d32;
  uint32_t x150 = (uint32_t )0x6b206574;
  uint32_t x16 = Hacl_Symmetric_Salsa20_load32_le(key + (uint32_t )0);
  uint32_t x20 = Hacl_Symmetric_Salsa20_load32_le(key + (uint32_t )4);
  uint32_t x30 = Hacl_Symmetric_Salsa20_load32_le(key + (uint32_t )8);
  uint32_t x40 = Hacl_Symmetric_Salsa20_load32_le(key + (uint32_t )12);
  uint32_t x110 = Hacl_Symmetric_Salsa20_load32_le(key + (uint32_t )16);
  uint32_t x120 = Hacl_Symmetric_Salsa20_load32_le(key + (uint32_t )20);
  uint32_t x130 = Hacl_Symmetric_Salsa20_load32_le(key + (uint32_t )24);
  uint32_t x140 = Hacl_Symmetric_Salsa20_load32_le(key + (uint32_t )28);
  uint32_t x60 = Hacl_Symmetric_Salsa20_load32_le(input + (uint32_t )0);
  uint32_t x70 = Hacl_Symmetric_Salsa20_load32_le(input + (uint32_t )4);
  uint32_t x80 = Hacl_Symmetric_Salsa20_load32_le(input + (uint32_t )8);
  uint32_t x90 = Hacl_Symmetric_Salsa20_load32_le(input + (uint32_t )12);
  uint32_t j0 = x00;
  uint32_t j1 = x16;
  uint32_t j2 = x20;
  uint32_t j3 = x30;
  uint32_t j4 = x40;
  uint32_t j5 = x50;
  uint32_t j6 = x60;
  uint32_t j7 = x70;
  uint32_t j8 = x80;
  uint32_t j9 = x90;
  uint32_t j10 = x100;
  uint32_t j11 = x110;
  uint32_t j12 = x120;
  uint32_t j13 = x130;
  uint32_t j14 = x140;
  uint32_t j15 = x150;
  uint32_t x41 = x40 ^ Hacl_Symmetric_Salsa20_rotate(x00 + x120, (uint32_t )7);
  uint32_t x81 = x80 ^ Hacl_Symmetric_Salsa20_rotate(x41 + x00, (uint32_t )9);
  uint32_t x121 = x120 ^ Hacl_Symmetric_Salsa20_rotate(x81 + x41, (uint32_t )13);
  uint32_t x01 = x00 ^ Hacl_Symmetric_Salsa20_rotate(x121 + x81, (uint32_t )18);
  uint32_t x91 = x90 ^ Hacl_Symmetric_Salsa20_rotate(x50 + x16, (uint32_t )7);
  uint32_t x131 = x130 ^ Hacl_Symmetric_Salsa20_rotate(x91 + x50, (uint32_t )9);
  uint32_t x17 = x16 ^ Hacl_Symmetric_Salsa20_rotate(x131 + x91, (uint32_t )13);
  uint32_t x51 = x50 ^ Hacl_Symmetric_Salsa20_rotate(x17 + x131, (uint32_t )18);
  uint32_t x141 = x140 ^ Hacl_Symmetric_Salsa20_rotate(x100 + x60, (uint32_t )7);
  uint32_t x21 = x20 ^ Hacl_Symmetric_Salsa20_rotate(x141 + x100, (uint32_t )9);
  uint32_t x61 = x60 ^ Hacl_Symmetric_Salsa20_rotate(x21 + x141, (uint32_t )13);
  uint32_t x101 = x100 ^ Hacl_Symmetric_Salsa20_rotate(x61 + x21, (uint32_t )18);
  uint32_t x31 = x30 ^ Hacl_Symmetric_Salsa20_rotate(x150 + x110, (uint32_t )7);
  uint32_t x71 = x70 ^ Hacl_Symmetric_Salsa20_rotate(x31 + x150, (uint32_t )9);
  uint32_t x111 = x110 ^ Hacl_Symmetric_Salsa20_rotate(x71 + x31, (uint32_t )13);
  uint32_t x151 = x150 ^ Hacl_Symmetric_Salsa20_rotate(x111 + x71, (uint32_t )18);
  uint32_t x18 = x17 ^ Hacl_Symmetric_Salsa20_rotate(x01 + x31, (uint32_t )7);
  uint32_t x22 = x21 ^ Hacl_Symmetric_Salsa20_rotate(x18 + x01, (uint32_t )9);
  uint32_t x32 = x31 ^ Hacl_Symmetric_Salsa20_rotate(x22 + x18, (uint32_t )13);
  uint32_t x02 = x01 ^ Hacl_Symmetric_Salsa20_rotate(x32 + x22, (uint32_t )18);
  uint32_t x62 = x61 ^ Hacl_Symmetric_Salsa20_rotate(x51 + x41, (uint32_t )7);
  uint32_t x72 = x71 ^ Hacl_Symmetric_Salsa20_rotate(x62 + x51, (uint32_t )9);
  uint32_t x42 = x41 ^ Hacl_Symmetric_Salsa20_rotate(x72 + x62, (uint32_t )13);
  uint32_t x52 = x51 ^ Hacl_Symmetric_Salsa20_rotate(x42 + x72, (uint32_t )18);
  uint32_t x112 = x111 ^ Hacl_Symmetric_Salsa20_rotate(x101 + x91, (uint32_t )7);
  uint32_t x82 = x81 ^ Hacl_Symmetric_Salsa20_rotate(x112 + x101, (uint32_t )9);
  uint32_t x92 = x91 ^ Hacl_Symmetric_Salsa20_rotate(x82 + x112, (uint32_t )13);
  uint32_t x102 = x101 ^ Hacl_Symmetric_Salsa20_rotate(x92 + x82, (uint32_t )18);
  uint32_t x122 = x121 ^ Hacl_Symmetric_Salsa20_rotate(x151 + x141, (uint32_t )7);
  uint32_t x132 = x131 ^ Hacl_Symmetric_Salsa20_rotate(x122 + x151, (uint32_t )9);
  uint32_t x142 = x141 ^ Hacl_Symmetric_Salsa20_rotate(x132 + x122, (uint32_t )13);
  uint32_t x152 = x151 ^ Hacl_Symmetric_Salsa20_rotate(x142 + x132, (uint32_t )18);
  uint32_t x43 = x42 ^ Hacl_Symmetric_Salsa20_rotate(x02 + x122, (uint32_t )7);
  uint32_t x83 = x82 ^ Hacl_Symmetric_Salsa20_rotate(x43 + x02, (uint32_t )9);
  uint32_t x123 = x122 ^ Hacl_Symmetric_Salsa20_rotate(x83 + x43, (uint32_t )13);
  uint32_t x03 = x02 ^ Hacl_Symmetric_Salsa20_rotate(x123 + x83, (uint32_t )18);
  uint32_t x93 = x92 ^ Hacl_Symmetric_Salsa20_rotate(x52 + x18, (uint32_t )7);
  uint32_t x133 = x132 ^ Hacl_Symmetric_Salsa20_rotate(x93 + x52, (uint32_t )9);
  uint32_t x19 = x18 ^ Hacl_Symmetric_Salsa20_rotate(x133 + x93, (uint32_t )13);
  uint32_t x53 = x52 ^ Hacl_Symmetric_Salsa20_rotate(x19 + x133, (uint32_t )18);
  uint32_t x143 = x142 ^ Hacl_Symmetric_Salsa20_rotate(x102 + x62, (uint32_t )7);
  uint32_t x23 = x22 ^ Hacl_Symmetric_Salsa20_rotate(x143 + x102, (uint32_t )9);
  uint32_t x63 = x62 ^ Hacl_Symmetric_Salsa20_rotate(x23 + x143, (uint32_t )13);
  uint32_t x103 = x102 ^ Hacl_Symmetric_Salsa20_rotate(x63 + x23, (uint32_t )18);
  uint32_t x33 = x32 ^ Hacl_Symmetric_Salsa20_rotate(x152 + x112, (uint32_t )7);
  uint32_t x73 = x72 ^ Hacl_Symmetric_Salsa20_rotate(x33 + x152, (uint32_t )9);
  uint32_t x113 = x112 ^ Hacl_Symmetric_Salsa20_rotate(x73 + x33, (uint32_t )13);
  uint32_t x153 = x152 ^ Hacl_Symmetric_Salsa20_rotate(x113 + x73, (uint32_t )18);
  uint32_t x114 = x19 ^ Hacl_Symmetric_Salsa20_rotate(x03 + x33, (uint32_t )7);
  uint32_t x24 = x23 ^ Hacl_Symmetric_Salsa20_rotate(x114 + x03, (uint32_t )9);
  uint32_t x34 = x33 ^ Hacl_Symmetric_Salsa20_rotate(x24 + x114, (uint32_t )13);
  uint32_t x04 = x03 ^ Hacl_Symmetric_Salsa20_rotate(x34 + x24, (uint32_t )18);
  uint32_t x64 = x63 ^ Hacl_Symmetric_Salsa20_rotate(x53 + x43, (uint32_t )7);
  uint32_t x74 = x73 ^ Hacl_Symmetric_Salsa20_rotate(x64 + x53, (uint32_t )9);
  uint32_t x44 = x43 ^ Hacl_Symmetric_Salsa20_rotate(x74 + x64, (uint32_t )13);
  uint32_t x54 = x53 ^ Hacl_Symmetric_Salsa20_rotate(x44 + x74, (uint32_t )18);
  uint32_t x115 = x113 ^ Hacl_Symmetric_Salsa20_rotate(x103 + x93, (uint32_t )7);
  uint32_t x84 = x83 ^ Hacl_Symmetric_Salsa20_rotate(x115 + x103, (uint32_t )9);
  uint32_t x94 = x93 ^ Hacl_Symmetric_Salsa20_rotate(x84 + x115, (uint32_t )13);
  uint32_t x104 = x103 ^ Hacl_Symmetric_Salsa20_rotate(x94 + x84, (uint32_t )18);
  uint32_t x124 = x123 ^ Hacl_Symmetric_Salsa20_rotate(x153 + x143, (uint32_t )7);
  uint32_t x134 = x133 ^ Hacl_Symmetric_Salsa20_rotate(x124 + x153, (uint32_t )9);
  uint32_t x144 = x143 ^ Hacl_Symmetric_Salsa20_rotate(x134 + x124, (uint32_t )13);
  uint32_t x154 = x153 ^ Hacl_Symmetric_Salsa20_rotate(x144 + x134, (uint32_t )18);
  uint32_t x45 = x44 ^ Hacl_Symmetric_Salsa20_rotate(x04 + x124, (uint32_t )7);
  uint32_t x85 = x84 ^ Hacl_Symmetric_Salsa20_rotate(x45 + x04, (uint32_t )9);
  uint32_t x125 = x124 ^ Hacl_Symmetric_Salsa20_rotate(x85 + x45, (uint32_t )13);
  uint32_t x05 = x04 ^ Hacl_Symmetric_Salsa20_rotate(x125 + x85, (uint32_t )18);
  uint32_t x95 = x94 ^ Hacl_Symmetric_Salsa20_rotate(x54 + x114, (uint32_t )7);
  uint32_t x135 = x134 ^ Hacl_Symmetric_Salsa20_rotate(x95 + x54, (uint32_t )9);
  uint32_t x116 = x114 ^ Hacl_Symmetric_Salsa20_rotate(x135 + x95, (uint32_t )13);
  uint32_t x55 = x54 ^ Hacl_Symmetric_Salsa20_rotate(x116 + x135, (uint32_t )18);
  uint32_t x145 = x144 ^ Hacl_Symmetric_Salsa20_rotate(x104 + x64, (uint32_t )7);
  uint32_t x25 = x24 ^ Hacl_Symmetric_Salsa20_rotate(x145 + x104, (uint32_t )9);
  uint32_t x65 = x64 ^ Hacl_Symmetric_Salsa20_rotate(x25 + x145, (uint32_t )13);
  uint32_t x105 = x104 ^ Hacl_Symmetric_Salsa20_rotate(x65 + x25, (uint32_t )18);
  uint32_t x35 = x34 ^ Hacl_Symmetric_Salsa20_rotate(x154 + x115, (uint32_t )7);
  uint32_t x75 = x74 ^ Hacl_Symmetric_Salsa20_rotate(x35 + x154, (uint32_t )9);
  uint32_t x117 = x115 ^ Hacl_Symmetric_Salsa20_rotate(x75 + x35, (uint32_t )13);
  uint32_t x155 = x154 ^ Hacl_Symmetric_Salsa20_rotate(x117 + x75, (uint32_t )18);
  uint32_t x118 = x116 ^ Hacl_Symmetric_Salsa20_rotate(x05 + x35, (uint32_t )7);
  uint32_t x26 = x25 ^ Hacl_Symmetric_Salsa20_rotate(x118 + x05, (uint32_t )9);
  uint32_t x36 = x35 ^ Hacl_Symmetric_Salsa20_rotate(x26 + x118, (uint32_t )13);
  uint32_t x06 = x05 ^ Hacl_Symmetric_Salsa20_rotate(x36 + x26, (uint32_t )18);
  uint32_t x66 = x65 ^ Hacl_Symmetric_Salsa20_rotate(x55 + x45, (uint32_t )7);
  uint32_t x76 = x75 ^ Hacl_Symmetric_Salsa20_rotate(x66 + x55, (uint32_t )9);
  uint32_t x46 = x45 ^ Hacl_Symmetric_Salsa20_rotate(x76 + x66, (uint32_t )13);
  uint32_t x56 = x55 ^ Hacl_Symmetric_Salsa20_rotate(x46 + x76, (uint32_t )18);
  uint32_t x119 = x117 ^ Hacl_Symmetric_Salsa20_rotate(x105 + x95, (uint32_t )7);
  uint32_t x86 = x85 ^ Hacl_Symmetric_Salsa20_rotate(x119 + x105, (uint32_t )9);
  uint32_t x96 = x95 ^ Hacl_Symmetric_Salsa20_rotate(x86 + x119, (uint32_t )13);
  uint32_t x106 = x105 ^ Hacl_Symmetric_Salsa20_rotate(x96 + x86, (uint32_t )18);
  uint32_t x126 = x125 ^ Hacl_Symmetric_Salsa20_rotate(x155 + x145, (uint32_t )7);
  uint32_t x136 = x135 ^ Hacl_Symmetric_Salsa20_rotate(x126 + x155, (uint32_t )9);
  uint32_t x146 = x145 ^ Hacl_Symmetric_Salsa20_rotate(x136 + x126, (uint32_t )13);
  uint32_t x156 = x155 ^ Hacl_Symmetric_Salsa20_rotate(x146 + x136, (uint32_t )18);
  uint32_t x47 = x46 ^ Hacl_Symmetric_Salsa20_rotate(x06 + x126, (uint32_t )7);
  uint32_t x87 = x86 ^ Hacl_Symmetric_Salsa20_rotate(x47 + x06, (uint32_t )9);
  uint32_t x127 = x126 ^ Hacl_Symmetric_Salsa20_rotate(x87 + x47, (uint32_t )13);
  uint32_t x07 = x06 ^ Hacl_Symmetric_Salsa20_rotate(x127 + x87, (uint32_t )18);
  uint32_t x97 = x96 ^ Hacl_Symmetric_Salsa20_rotate(x56 + x118, (uint32_t )7);
  uint32_t x137 = x136 ^ Hacl_Symmetric_Salsa20_rotate(x97 + x56, (uint32_t )9);
  uint32_t x128 = x118 ^ Hacl_Symmetric_Salsa20_rotate(x137 + x97, (uint32_t )13);
  uint32_t x57 = x56 ^ Hacl_Symmetric_Salsa20_rotate(x128 + x137, (uint32_t )18);
  uint32_t x147 = x146 ^ Hacl_Symmetric_Salsa20_rotate(x106 + x66, (uint32_t )7);
  uint32_t x27 = x26 ^ Hacl_Symmetric_Salsa20_rotate(x147 + x106, (uint32_t )9);
  uint32_t x67 = x66 ^ Hacl_Symmetric_Salsa20_rotate(x27 + x147, (uint32_t )13);
  uint32_t x107 = x106 ^ Hacl_Symmetric_Salsa20_rotate(x67 + x27, (uint32_t )18);
  uint32_t x37 = x36 ^ Hacl_Symmetric_Salsa20_rotate(x156 + x119, (uint32_t )7);
  uint32_t x77 = x76 ^ Hacl_Symmetric_Salsa20_rotate(x37 + x156, (uint32_t )9);
  uint32_t x1110 = x119 ^ Hacl_Symmetric_Salsa20_rotate(x77 + x37, (uint32_t )13);
  uint32_t x157 = x156 ^ Hacl_Symmetric_Salsa20_rotate(x1110 + x77, (uint32_t )18);
  uint32_t x129 = x128 ^ Hacl_Symmetric_Salsa20_rotate(x07 + x37, (uint32_t )7);
  uint32_t x28 = x27 ^ Hacl_Symmetric_Salsa20_rotate(x129 + x07, (uint32_t )9);
  uint32_t x38 = x37 ^ Hacl_Symmetric_Salsa20_rotate(x28 + x129, (uint32_t )13);
  uint32_t x08 = x07 ^ Hacl_Symmetric_Salsa20_rotate(x38 + x28, (uint32_t )18);
  uint32_t x68 = x67 ^ Hacl_Symmetric_Salsa20_rotate(x57 + x47, (uint32_t )7);
  uint32_t x78 = x77 ^ Hacl_Symmetric_Salsa20_rotate(x68 + x57, (uint32_t )9);
  uint32_t x48 = x47 ^ Hacl_Symmetric_Salsa20_rotate(x78 + x68, (uint32_t )13);
  uint32_t x58 = x57 ^ Hacl_Symmetric_Salsa20_rotate(x48 + x78, (uint32_t )18);
  uint32_t x1111 = x1110 ^ Hacl_Symmetric_Salsa20_rotate(x107 + x97, (uint32_t )7);
  uint32_t x88 = x87 ^ Hacl_Symmetric_Salsa20_rotate(x1111 + x107, (uint32_t )9);
  uint32_t x98 = x97 ^ Hacl_Symmetric_Salsa20_rotate(x88 + x1111, (uint32_t )13);
  uint32_t x108 = x107 ^ Hacl_Symmetric_Salsa20_rotate(x98 + x88, (uint32_t )18);
  uint32_t x1210 = x127 ^ Hacl_Symmetric_Salsa20_rotate(x157 + x147, (uint32_t )7);
  uint32_t x138 = x137 ^ Hacl_Symmetric_Salsa20_rotate(x1210 + x157, (uint32_t )9);
  uint32_t x148 = x147 ^ Hacl_Symmetric_Salsa20_rotate(x138 + x1210, (uint32_t )13);
  uint32_t x158 = x157 ^ Hacl_Symmetric_Salsa20_rotate(x148 + x138, (uint32_t )18);
  uint32_t x49 = x48 ^ Hacl_Symmetric_Salsa20_rotate(x08 + x1210, (uint32_t )7);
  uint32_t x89 = x88 ^ Hacl_Symmetric_Salsa20_rotate(x49 + x08, (uint32_t )9);
  uint32_t x1211 = x1210 ^ Hacl_Symmetric_Salsa20_rotate(x89 + x49, (uint32_t )13);
  uint32_t x09 = x08 ^ Hacl_Symmetric_Salsa20_rotate(x1211 + x89, (uint32_t )18);
  uint32_t x99 = x98 ^ Hacl_Symmetric_Salsa20_rotate(x58 + x129, (uint32_t )7);
  uint32_t x139 = x138 ^ Hacl_Symmetric_Salsa20_rotate(x99 + x58, (uint32_t )9);
  uint32_t x149 = x129 ^ Hacl_Symmetric_Salsa20_rotate(x139 + x99, (uint32_t )13);
  uint32_t x59 = x58 ^ Hacl_Symmetric_Salsa20_rotate(x149 + x139, (uint32_t )18);
  uint32_t x1410 = x148 ^ Hacl_Symmetric_Salsa20_rotate(x108 + x68, (uint32_t )7);
  uint32_t x29 = x28 ^ Hacl_Symmetric_Salsa20_rotate(x1410 + x108, (uint32_t )9);
  uint32_t x69 = x68 ^ Hacl_Symmetric_Salsa20_rotate(x29 + x1410, (uint32_t )13);
  uint32_t x109 = x108 ^ Hacl_Symmetric_Salsa20_rotate(x69 + x29, (uint32_t )18);
  uint32_t x39 = x38 ^ Hacl_Symmetric_Salsa20_rotate(x158 + x1111, (uint32_t )7);
  uint32_t x79 = x78 ^ Hacl_Symmetric_Salsa20_rotate(x39 + x158, (uint32_t )9);
  uint32_t x1112 = x1111 ^ Hacl_Symmetric_Salsa20_rotate(x79 + x39, (uint32_t )13);
  uint32_t x159 = x158 ^ Hacl_Symmetric_Salsa20_rotate(x1112 + x79, (uint32_t )18);
  uint32_t x160 = x149 ^ Hacl_Symmetric_Salsa20_rotate(x09 + x39, (uint32_t )7);
  uint32_t x210 = x29 ^ Hacl_Symmetric_Salsa20_rotate(x160 + x09, (uint32_t )9);
  uint32_t x310 = x39 ^ Hacl_Symmetric_Salsa20_rotate(x210 + x160, (uint32_t )13);
  uint32_t x010 = x09 ^ Hacl_Symmetric_Salsa20_rotate(x310 + x210, (uint32_t )18);
  uint32_t x610 = x69 ^ Hacl_Symmetric_Salsa20_rotate(x59 + x49, (uint32_t )7);
  uint32_t x710 = x79 ^ Hacl_Symmetric_Salsa20_rotate(x610 + x59, (uint32_t )9);
  uint32_t x410 = x49 ^ Hacl_Symmetric_Salsa20_rotate(x710 + x610, (uint32_t )13);
  uint32_t x510 = x59 ^ Hacl_Symmetric_Salsa20_rotate(x410 + x710, (uint32_t )18);
  uint32_t x1113 = x1112 ^ Hacl_Symmetric_Salsa20_rotate(x109 + x99, (uint32_t )7);
  uint32_t x810 = x89 ^ Hacl_Symmetric_Salsa20_rotate(x1113 + x109, (uint32_t )9);
  uint32_t x910 = x99 ^ Hacl_Symmetric_Salsa20_rotate(x810 + x1113, (uint32_t )13);
  uint32_t x1010 = x109 ^ Hacl_Symmetric_Salsa20_rotate(x910 + x810, (uint32_t )18);
  uint32_t x1212 = x1211 ^ Hacl_Symmetric_Salsa20_rotate(x159 + x1410, (uint32_t )7);
  uint32_t x1310 = x139 ^ Hacl_Symmetric_Salsa20_rotate(x1212 + x159, (uint32_t )9);
  uint32_t x1411 = x1410 ^ Hacl_Symmetric_Salsa20_rotate(x1310 + x1212, (uint32_t )13);
  uint32_t x1510 = x159 ^ Hacl_Symmetric_Salsa20_rotate(x1411 + x1310, (uint32_t )18);
  uint32_t x411 = x410 ^ Hacl_Symmetric_Salsa20_rotate(x010 + x1212, (uint32_t )7);
  uint32_t x811 = x810 ^ Hacl_Symmetric_Salsa20_rotate(x411 + x010, (uint32_t )9);
  uint32_t x1213 = x1212 ^ Hacl_Symmetric_Salsa20_rotate(x811 + x411, (uint32_t )13);
  uint32_t x011 = x010 ^ Hacl_Symmetric_Salsa20_rotate(x1213 + x811, (uint32_t )18);
  uint32_t x911 = x910 ^ Hacl_Symmetric_Salsa20_rotate(x510 + x160, (uint32_t )7);
  uint32_t x1311 = x1310 ^ Hacl_Symmetric_Salsa20_rotate(x911 + x510, (uint32_t )9);
  uint32_t x161 = x160 ^ Hacl_Symmetric_Salsa20_rotate(x1311 + x911, (uint32_t )13);
  uint32_t x511 = x510 ^ Hacl_Symmetric_Salsa20_rotate(x161 + x1311, (uint32_t )18);
  uint32_t x1412 = x1411 ^ Hacl_Symmetric_Salsa20_rotate(x1010 + x610, (uint32_t )7);
  uint32_t x211 = x210 ^ Hacl_Symmetric_Salsa20_rotate(x1412 + x1010, (uint32_t )9);
  uint32_t x611 = x610 ^ Hacl_Symmetric_Salsa20_rotate(x211 + x1412, (uint32_t )13);
  uint32_t x1011 = x1010 ^ Hacl_Symmetric_Salsa20_rotate(x611 + x211, (uint32_t )18);
  uint32_t x311 = x310 ^ Hacl_Symmetric_Salsa20_rotate(x1510 + x1113, (uint32_t )7);
  uint32_t x711 = x710 ^ Hacl_Symmetric_Salsa20_rotate(x311 + x1510, (uint32_t )9);
  uint32_t x1114 = x1113 ^ Hacl_Symmetric_Salsa20_rotate(x711 + x311, (uint32_t )13);
  uint32_t x1511 = x1510 ^ Hacl_Symmetric_Salsa20_rotate(x1114 + x711, (uint32_t )18);
  uint32_t x162 = x161 ^ Hacl_Symmetric_Salsa20_rotate(x011 + x311, (uint32_t )7);
  uint32_t x212 = x211 ^ Hacl_Symmetric_Salsa20_rotate(x162 + x011, (uint32_t )9);
  uint32_t x312 = x311 ^ Hacl_Symmetric_Salsa20_rotate(x212 + x162, (uint32_t )13);
  uint32_t x012 = x011 ^ Hacl_Symmetric_Salsa20_rotate(x312 + x212, (uint32_t )18);
  uint32_t x612 = x611 ^ Hacl_Symmetric_Salsa20_rotate(x511 + x411, (uint32_t )7);
  uint32_t x712 = x711 ^ Hacl_Symmetric_Salsa20_rotate(x612 + x511, (uint32_t )9);
  uint32_t x412 = x411 ^ Hacl_Symmetric_Salsa20_rotate(x712 + x612, (uint32_t )13);
  uint32_t x512 = x511 ^ Hacl_Symmetric_Salsa20_rotate(x412 + x712, (uint32_t )18);
  uint32_t x1115 = x1114 ^ Hacl_Symmetric_Salsa20_rotate(x1011 + x911, (uint32_t )7);
  uint32_t x812 = x811 ^ Hacl_Symmetric_Salsa20_rotate(x1115 + x1011, (uint32_t )9);
  uint32_t x912 = x911 ^ Hacl_Symmetric_Salsa20_rotate(x812 + x1115, (uint32_t )13);
  uint32_t x1012 = x1011 ^ Hacl_Symmetric_Salsa20_rotate(x912 + x812, (uint32_t )18);
  uint32_t x1214 = x1213 ^ Hacl_Symmetric_Salsa20_rotate(x1511 + x1412, (uint32_t )7);
  uint32_t x1312 = x1311 ^ Hacl_Symmetric_Salsa20_rotate(x1214 + x1511, (uint32_t )9);
  uint32_t x1413 = x1412 ^ Hacl_Symmetric_Salsa20_rotate(x1312 + x1214, (uint32_t )13);
  uint32_t x1512 = x1511 ^ Hacl_Symmetric_Salsa20_rotate(x1413 + x1312, (uint32_t )18);
  uint32_t x413 = x412 ^ Hacl_Symmetric_Salsa20_rotate(x012 + x1214, (uint32_t )7);
  uint32_t x813 = x812 ^ Hacl_Symmetric_Salsa20_rotate(x413 + x012, (uint32_t )9);
  uint32_t x1215 = x1214 ^ Hacl_Symmetric_Salsa20_rotate(x813 + x413, (uint32_t )13);
  uint32_t x013 = x012 ^ Hacl_Symmetric_Salsa20_rotate(x1215 + x813, (uint32_t )18);
  uint32_t x913 = x912 ^ Hacl_Symmetric_Salsa20_rotate(x512 + x162, (uint32_t )7);
  uint32_t x1313 = x1312 ^ Hacl_Symmetric_Salsa20_rotate(x913 + x512, (uint32_t )9);
  uint32_t x163 = x162 ^ Hacl_Symmetric_Salsa20_rotate(x1313 + x913, (uint32_t )13);
  uint32_t x513 = x512 ^ Hacl_Symmetric_Salsa20_rotate(x163 + x1313, (uint32_t )18);
  uint32_t x1414 = x1413 ^ Hacl_Symmetric_Salsa20_rotate(x1012 + x612, (uint32_t )7);
  uint32_t x213 = x212 ^ Hacl_Symmetric_Salsa20_rotate(x1414 + x1012, (uint32_t )9);
  uint32_t x613 = x612 ^ Hacl_Symmetric_Salsa20_rotate(x213 + x1414, (uint32_t )13);
  uint32_t x1013 = x1012 ^ Hacl_Symmetric_Salsa20_rotate(x613 + x213, (uint32_t )18);
  uint32_t x313 = x312 ^ Hacl_Symmetric_Salsa20_rotate(x1512 + x1115, (uint32_t )7);
  uint32_t x713 = x712 ^ Hacl_Symmetric_Salsa20_rotate(x313 + x1512, (uint32_t )9);
  uint32_t x1116 = x1115 ^ Hacl_Symmetric_Salsa20_rotate(x713 + x313, (uint32_t )13);
  uint32_t x1513 = x1512 ^ Hacl_Symmetric_Salsa20_rotate(x1116 + x713, (uint32_t )18);
  uint32_t x164 = x163 ^ Hacl_Symmetric_Salsa20_rotate(x013 + x313, (uint32_t )7);
  uint32_t x214 = x213 ^ Hacl_Symmetric_Salsa20_rotate(x164 + x013, (uint32_t )9);
  uint32_t x314 = x313 ^ Hacl_Symmetric_Salsa20_rotate(x214 + x164, (uint32_t )13);
  uint32_t x014 = x013 ^ Hacl_Symmetric_Salsa20_rotate(x314 + x214, (uint32_t )18);
  uint32_t x614 = x613 ^ Hacl_Symmetric_Salsa20_rotate(x513 + x413, (uint32_t )7);
  uint32_t x714 = x713 ^ Hacl_Symmetric_Salsa20_rotate(x614 + x513, (uint32_t )9);
  uint32_t x414 = x413 ^ Hacl_Symmetric_Salsa20_rotate(x714 + x614, (uint32_t )13);
  uint32_t x514 = x513 ^ Hacl_Symmetric_Salsa20_rotate(x414 + x714, (uint32_t )18);
  uint32_t x1117 = x1116 ^ Hacl_Symmetric_Salsa20_rotate(x1013 + x913, (uint32_t )7);
  uint32_t x814 = x813 ^ Hacl_Symmetric_Salsa20_rotate(x1117 + x1013, (uint32_t )9);
  uint32_t x914 = x913 ^ Hacl_Symmetric_Salsa20_rotate(x814 + x1117, (uint32_t )13);
  uint32_t x1014 = x1013 ^ Hacl_Symmetric_Salsa20_rotate(x914 + x814, (uint32_t )18);
  uint32_t x1216 = x1215 ^ Hacl_Symmetric_Salsa20_rotate(x1513 + x1414, (uint32_t )7);
  uint32_t x1314 = x1313 ^ Hacl_Symmetric_Salsa20_rotate(x1216 + x1513, (uint32_t )9);
  uint32_t x1415 = x1414 ^ Hacl_Symmetric_Salsa20_rotate(x1314 + x1216, (uint32_t )13);
  uint32_t x1514 = x1513 ^ Hacl_Symmetric_Salsa20_rotate(x1415 + x1314, (uint32_t )18);
  uint32_t x415 = x414 ^ Hacl_Symmetric_Salsa20_rotate(x014 + x1216, (uint32_t )7);
  uint32_t x815 = x814 ^ Hacl_Symmetric_Salsa20_rotate(x415 + x014, (uint32_t )9);
  uint32_t x1217 = x1216 ^ Hacl_Symmetric_Salsa20_rotate(x815 + x415, (uint32_t )13);
  uint32_t x015 = x014 ^ Hacl_Symmetric_Salsa20_rotate(x1217 + x815, (uint32_t )18);
  uint32_t x915 = x914 ^ Hacl_Symmetric_Salsa20_rotate(x514 + x164, (uint32_t )7);
  uint32_t x1315 = x1314 ^ Hacl_Symmetric_Salsa20_rotate(x915 + x514, (uint32_t )9);
  uint32_t x165 = x164 ^ Hacl_Symmetric_Salsa20_rotate(x1315 + x915, (uint32_t )13);
  uint32_t x515 = x514 ^ Hacl_Symmetric_Salsa20_rotate(x165 + x1315, (uint32_t )18);
  uint32_t x1416 = x1415 ^ Hacl_Symmetric_Salsa20_rotate(x1014 + x614, (uint32_t )7);
  uint32_t x215 = x214 ^ Hacl_Symmetric_Salsa20_rotate(x1416 + x1014, (uint32_t )9);
  uint32_t x615 = x614 ^ Hacl_Symmetric_Salsa20_rotate(x215 + x1416, (uint32_t )13);
  uint32_t x1015 = x1014 ^ Hacl_Symmetric_Salsa20_rotate(x615 + x215, (uint32_t )18);
  uint32_t x315 = x314 ^ Hacl_Symmetric_Salsa20_rotate(x1514 + x1117, (uint32_t )7);
  uint32_t x715 = x714 ^ Hacl_Symmetric_Salsa20_rotate(x315 + x1514, (uint32_t )9);
  uint32_t x1118 = x1117 ^ Hacl_Symmetric_Salsa20_rotate(x715 + x315, (uint32_t )13);
  uint32_t x1515 = x1514 ^ Hacl_Symmetric_Salsa20_rotate(x1118 + x715, (uint32_t )18);
  uint32_t x166 = x165 ^ Hacl_Symmetric_Salsa20_rotate(x015 + x315, (uint32_t )7);
  uint32_t x216 = x215 ^ Hacl_Symmetric_Salsa20_rotate(x166 + x015, (uint32_t )9);
  uint32_t x316 = x315 ^ Hacl_Symmetric_Salsa20_rotate(x216 + x166, (uint32_t )13);
  uint32_t x016 = x015 ^ Hacl_Symmetric_Salsa20_rotate(x316 + x216, (uint32_t )18);
  uint32_t x616 = x615 ^ Hacl_Symmetric_Salsa20_rotate(x515 + x415, (uint32_t )7);
  uint32_t x716 = x715 ^ Hacl_Symmetric_Salsa20_rotate(x616 + x515, (uint32_t )9);
  uint32_t x416 = x415 ^ Hacl_Symmetric_Salsa20_rotate(x716 + x616, (uint32_t )13);
  uint32_t x516 = x515 ^ Hacl_Symmetric_Salsa20_rotate(x416 + x716, (uint32_t )18);
  uint32_t x1119 = x1118 ^ Hacl_Symmetric_Salsa20_rotate(x1015 + x915, (uint32_t )7);
  uint32_t x816 = x815 ^ Hacl_Symmetric_Salsa20_rotate(x1119 + x1015, (uint32_t )9);
  uint32_t x916 = x915 ^ Hacl_Symmetric_Salsa20_rotate(x816 + x1119, (uint32_t )13);
  uint32_t x1016 = x1015 ^ Hacl_Symmetric_Salsa20_rotate(x916 + x816, (uint32_t )18);
  uint32_t x1218 = x1217 ^ Hacl_Symmetric_Salsa20_rotate(x1515 + x1416, (uint32_t )7);
  uint32_t x1316 = x1315 ^ Hacl_Symmetric_Salsa20_rotate(x1218 + x1515, (uint32_t )9);
  uint32_t x1417 = x1416 ^ Hacl_Symmetric_Salsa20_rotate(x1316 + x1218, (uint32_t )13);
  uint32_t x1516 = x1515 ^ Hacl_Symmetric_Salsa20_rotate(x1417 + x1316, (uint32_t )18);
  uint32_t x417 = x416 ^ Hacl_Symmetric_Salsa20_rotate(x016 + x1218, (uint32_t )7);
  uint32_t x817 = x816 ^ Hacl_Symmetric_Salsa20_rotate(x417 + x016, (uint32_t )9);
  uint32_t x1219 = x1218 ^ Hacl_Symmetric_Salsa20_rotate(x817 + x417, (uint32_t )13);
  uint32_t x017 = x016 ^ Hacl_Symmetric_Salsa20_rotate(x1219 + x817, (uint32_t )18);
  uint32_t x917 = x916 ^ Hacl_Symmetric_Salsa20_rotate(x516 + x166, (uint32_t )7);
  uint32_t x1317 = x1316 ^ Hacl_Symmetric_Salsa20_rotate(x917 + x516, (uint32_t )9);
  uint32_t x167 = x166 ^ Hacl_Symmetric_Salsa20_rotate(x1317 + x917, (uint32_t )13);
  uint32_t x517 = x516 ^ Hacl_Symmetric_Salsa20_rotate(x167 + x1317, (uint32_t )18);
  uint32_t x1418 = x1417 ^ Hacl_Symmetric_Salsa20_rotate(x1016 + x616, (uint32_t )7);
  uint32_t x217 = x216 ^ Hacl_Symmetric_Salsa20_rotate(x1418 + x1016, (uint32_t )9);
  uint32_t x617 = x616 ^ Hacl_Symmetric_Salsa20_rotate(x217 + x1418, (uint32_t )13);
  uint32_t x1017 = x1016 ^ Hacl_Symmetric_Salsa20_rotate(x617 + x217, (uint32_t )18);
  uint32_t x317 = x316 ^ Hacl_Symmetric_Salsa20_rotate(x1516 + x1119, (uint32_t )7);
  uint32_t x717 = x716 ^ Hacl_Symmetric_Salsa20_rotate(x317 + x1516, (uint32_t )9);
  uint32_t x1120 = x1119 ^ Hacl_Symmetric_Salsa20_rotate(x717 + x317, (uint32_t )13);
  uint32_t x1517 = x1516 ^ Hacl_Symmetric_Salsa20_rotate(x1120 + x717, (uint32_t )18);
  uint32_t x168 = x167 ^ Hacl_Symmetric_Salsa20_rotate(x017 + x317, (uint32_t )7);
  uint32_t x218 = x217 ^ Hacl_Symmetric_Salsa20_rotate(x168 + x017, (uint32_t )9);
  uint32_t x318 = x317 ^ Hacl_Symmetric_Salsa20_rotate(x218 + x168, (uint32_t )13);
  uint32_t x018 = x017 ^ Hacl_Symmetric_Salsa20_rotate(x318 + x218, (uint32_t )18);
  uint32_t x618 = x617 ^ Hacl_Symmetric_Salsa20_rotate(x517 + x417, (uint32_t )7);
  uint32_t x718 = x717 ^ Hacl_Symmetric_Salsa20_rotate(x618 + x517, (uint32_t )9);
  uint32_t x418 = x417 ^ Hacl_Symmetric_Salsa20_rotate(x718 + x618, (uint32_t )13);
  uint32_t x518 = x517 ^ Hacl_Symmetric_Salsa20_rotate(x418 + x718, (uint32_t )18);
  uint32_t x1121 = x1120 ^ Hacl_Symmetric_Salsa20_rotate(x1017 + x917, (uint32_t )7);
  uint32_t x818 = x817 ^ Hacl_Symmetric_Salsa20_rotate(x1121 + x1017, (uint32_t )9);
  uint32_t x918 = x917 ^ Hacl_Symmetric_Salsa20_rotate(x818 + x1121, (uint32_t )13);
  uint32_t x1018 = x1017 ^ Hacl_Symmetric_Salsa20_rotate(x918 + x818, (uint32_t )18);
  uint32_t x1220 = x1219 ^ Hacl_Symmetric_Salsa20_rotate(x1517 + x1418, (uint32_t )7);
  uint32_t x1318 = x1317 ^ Hacl_Symmetric_Salsa20_rotate(x1220 + x1517, (uint32_t )9);
  uint32_t x1419 = x1418 ^ Hacl_Symmetric_Salsa20_rotate(x1318 + x1220, (uint32_t )13);
  uint32_t x1518 = x1517 ^ Hacl_Symmetric_Salsa20_rotate(x1419 + x1318, (uint32_t )18);
  uint32_t x419 = x418 ^ Hacl_Symmetric_Salsa20_rotate(x018 + x1220, (uint32_t )7);
  uint32_t x819 = x818 ^ Hacl_Symmetric_Salsa20_rotate(x419 + x018, (uint32_t )9);
  uint32_t x1221 = x1220 ^ Hacl_Symmetric_Salsa20_rotate(x819 + x419, (uint32_t )13);
  uint32_t x019 = x018 ^ Hacl_Symmetric_Salsa20_rotate(x1221 + x819, (uint32_t )18);
  uint32_t x919 = x918 ^ Hacl_Symmetric_Salsa20_rotate(x518 + x168, (uint32_t )7);
  uint32_t x1319 = x1318 ^ Hacl_Symmetric_Salsa20_rotate(x919 + x518, (uint32_t )9);
  uint32_t x169 = x168 ^ Hacl_Symmetric_Salsa20_rotate(x1319 + x919, (uint32_t )13);
  uint32_t x519 = x518 ^ Hacl_Symmetric_Salsa20_rotate(x169 + x1319, (uint32_t )18);
  uint32_t x1420 = x1419 ^ Hacl_Symmetric_Salsa20_rotate(x1018 + x618, (uint32_t )7);
  uint32_t x219 = x218 ^ Hacl_Symmetric_Salsa20_rotate(x1420 + x1018, (uint32_t )9);
  uint32_t x619 = x618 ^ Hacl_Symmetric_Salsa20_rotate(x219 + x1420, (uint32_t )13);
  uint32_t x1019 = x1018 ^ Hacl_Symmetric_Salsa20_rotate(x619 + x219, (uint32_t )18);
  uint32_t x319 = x318 ^ Hacl_Symmetric_Salsa20_rotate(x1518 + x1121, (uint32_t )7);
  uint32_t x719 = x718 ^ Hacl_Symmetric_Salsa20_rotate(x319 + x1518, (uint32_t )9);
  uint32_t x1122 = x1121 ^ Hacl_Symmetric_Salsa20_rotate(x719 + x319, (uint32_t )13);
  uint32_t x1519 = x1518 ^ Hacl_Symmetric_Salsa20_rotate(x1122 + x719, (uint32_t )18);
  uint32_t x170 = x169 ^ Hacl_Symmetric_Salsa20_rotate(x019 + x319, (uint32_t )7);
  uint32_t x220 = x219 ^ Hacl_Symmetric_Salsa20_rotate(x170 + x019, (uint32_t )9);
  uint32_t x320 = x319 ^ Hacl_Symmetric_Salsa20_rotate(x220 + x170, (uint32_t )13);
  uint32_t x020 = x019 ^ Hacl_Symmetric_Salsa20_rotate(x320 + x220, (uint32_t )18);
  uint32_t x620 = x619 ^ Hacl_Symmetric_Salsa20_rotate(x519 + x419, (uint32_t )7);
  uint32_t x720 = x719 ^ Hacl_Symmetric_Salsa20_rotate(x620 + x519, (uint32_t )9);
  uint32_t x420 = x419 ^ Hacl_Symmetric_Salsa20_rotate(x720 + x620, (uint32_t )13);
  uint32_t x520 = x519 ^ Hacl_Symmetric_Salsa20_rotate(x420 + x720, (uint32_t )18);
  uint32_t x1123 = x1122 ^ Hacl_Symmetric_Salsa20_rotate(x1019 + x919, (uint32_t )7);
  uint32_t x820 = x819 ^ Hacl_Symmetric_Salsa20_rotate(x1123 + x1019, (uint32_t )9);
  uint32_t x920 = x919 ^ Hacl_Symmetric_Salsa20_rotate(x820 + x1123, (uint32_t )13);
  uint32_t x1020 = x1019 ^ Hacl_Symmetric_Salsa20_rotate(x920 + x820, (uint32_t )18);
  uint32_t x1222 = x1221 ^ Hacl_Symmetric_Salsa20_rotate(x1519 + x1420, (uint32_t )7);
  uint32_t x1320 = x1319 ^ Hacl_Symmetric_Salsa20_rotate(x1222 + x1519, (uint32_t )9);
  uint32_t x1421 = x1420 ^ Hacl_Symmetric_Salsa20_rotate(x1320 + x1222, (uint32_t )13);
  uint32_t x1520 = x1519 ^ Hacl_Symmetric_Salsa20_rotate(x1421 + x1320, (uint32_t )18);
  uint32_t x0 = x020 + j0;
  uint32_t x1 = x170 + j1;
  uint32_t x2 = x220 + j2;
  uint32_t x3 = x320 + j3;
  uint32_t x4 = x420 + j4;
  uint32_t x5 = x520 + j5;
  uint32_t x6 = x620 + j6;
  uint32_t x7 = x720 + j7;
  uint32_t x8 = x820 + j8;
  uint32_t x9 = x920 + j9;
  uint32_t x10 = x1020 + j10;
  uint32_t x11 = x1123 + j11;
  uint32_t x12 = x1222 + j12;
  uint32_t x13 = x1320 + j13;
  uint32_t x14 = x1421 + j14;
  uint32_t x15 = x1520 + j15;
  Hacl_Symmetric_Salsa20_store32_le(output + (uint32_t )0, x0);
  Hacl_Symmetric_Salsa20_store32_le(output + (uint32_t )4, x1);
  Hacl_Symmetric_Salsa20_store32_le(output + (uint32_t )8, x2);
  Hacl_Symmetric_Salsa20_store32_le(output + (uint32_t )12, x3);
  Hacl_Symmetric_Salsa20_store32_le(output + (uint32_t )16, x4);
  Hacl_Symmetric_Salsa20_store32_le(output + (uint32_t )20, x5);
  Hacl_Symmetric_Salsa20_store32_le(output + (uint32_t )24, x6);
  Hacl_Symmetric_Salsa20_store32_le(output + (uint32_t )28, x7);
  Hacl_Symmetric_Salsa20_store32_le(output + (uint32_t )32, x8);
  Hacl_Symmetric_Salsa20_store32_le(output + (uint32_t )36, x9);
  Hacl_Symmetric_Salsa20_store32_le(output + (uint32_t )40, x10);
  Hacl_Symmetric_Salsa20_store32_le(output + (uint32_t )44, x11);
  Hacl_Symmetric_Salsa20_store32_le(output + (uint32_t )48, x12);
  Hacl_Symmetric_Salsa20_store32_le(output + (uint32_t )52, x13);
  Hacl_Symmetric_Salsa20_store32_le(output + (uint32_t )56, x14);
  Hacl_Symmetric_Salsa20_store32_le(output + (uint32_t )60, x15);
  return;
}

void Hacl_Symmetric_Salsa20_xor_(uint8_t *c, uint8_t *m, uint8_t *block)
{
  uint8_t m0 = m[(uint32_t )0];
  uint8_t block0 = block[(uint32_t )0];
  uint8_t m1 = m[(uint32_t )1];
  uint8_t block1 = block[(uint32_t )1];
  uint8_t m2 = m[(uint32_t )2];
  uint8_t block2 = block[(uint32_t )2];
  uint8_t m3 = m[(uint32_t )3];
  uint8_t block3 = block[(uint32_t )3];
  uint8_t m4 = m[(uint32_t )4];
  uint8_t block4 = block[(uint32_t )4];
  uint8_t m5 = m[(uint32_t )5];
  uint8_t block5 = block[(uint32_t )5];
  uint8_t m6 = m[(uint32_t )6];
  uint8_t block6 = block[(uint32_t )6];
  uint8_t m7 = m[(uint32_t )7];
  uint8_t block7 = block[(uint32_t )7];
  uint8_t m8 = m[(uint32_t )8];
  uint8_t block8 = block[(uint32_t )8];
  uint8_t m9 = m[(uint32_t )9];
  uint8_t block9 = block[(uint32_t )9];
  uint8_t m10 = m[(uint32_t )10];
  uint8_t block10 = block[(uint32_t )10];
  uint8_t m11 = m[(uint32_t )11];
  uint8_t block11 = block[(uint32_t )11];
  uint8_t m12 = m[(uint32_t )12];
  uint8_t block12 = block[(uint32_t )12];
  uint8_t m13 = m[(uint32_t )13];
  uint8_t block13 = block[(uint32_t )13];
  uint8_t m14 = m[(uint32_t )14];
  uint8_t block14 = block[(uint32_t )14];
  uint8_t m15 = m[(uint32_t )15];
  uint8_t block15 = block[(uint32_t )15];
  uint8_t m16 = m[(uint32_t )16];
  uint8_t block16 = block[(uint32_t )16];
  uint8_t m17 = m[(uint32_t )17];
  uint8_t block17 = block[(uint32_t )17];
  uint8_t m18 = m[(uint32_t )18];
  uint8_t block18 = block[(uint32_t )18];
  uint8_t m19 = m[(uint32_t )19];
  uint8_t block19 = block[(uint32_t )19];
  uint8_t m20 = m[(uint32_t )20];
  uint8_t block20 = block[(uint32_t )20];
  uint8_t m21 = m[(uint32_t )21];
  uint8_t block21 = block[(uint32_t )21];
  uint8_t m22 = m[(uint32_t )22];
  uint8_t block22 = block[(uint32_t )22];
  uint8_t m23 = m[(uint32_t )23];
  uint8_t block23 = block[(uint32_t )23];
  uint8_t m24 = m[(uint32_t )24];
  uint8_t block24 = block[(uint32_t )24];
  uint8_t m25 = m[(uint32_t )25];
  uint8_t block25 = block[(uint32_t )25];
  uint8_t m26 = m[(uint32_t )26];
  uint8_t block26 = block[(uint32_t )26];
  uint8_t m27 = m[(uint32_t )27];
  uint8_t block27 = block[(uint32_t )27];
  uint8_t m28 = m[(uint32_t )28];
  uint8_t block28 = block[(uint32_t )28];
  uint8_t m29 = m[(uint32_t )29];
  uint8_t block29 = block[(uint32_t )29];
  uint8_t m30 = m[(uint32_t )30];
  uint8_t block30 = block[(uint32_t )30];
  uint8_t m31 = m[(uint32_t )31];
  uint8_t block31 = block[(uint32_t )31];
  uint8_t m32 = m[(uint32_t )32];
  uint8_t block32 = block[(uint32_t )32];
  uint8_t m33 = m[(uint32_t )33];
  uint8_t block33 = block[(uint32_t )33];
  uint8_t m34 = m[(uint32_t )34];
  uint8_t block34 = block[(uint32_t )34];
  uint8_t m35 = m[(uint32_t )35];
  uint8_t block35 = block[(uint32_t )35];
  uint8_t m36 = m[(uint32_t )36];
  uint8_t block36 = block[(uint32_t )36];
  uint8_t m37 = m[(uint32_t )37];
  uint8_t block37 = block[(uint32_t )37];
  uint8_t m38 = m[(uint32_t )38];
  uint8_t block38 = block[(uint32_t )38];
  uint8_t m39 = m[(uint32_t )39];
  uint8_t block39 = block[(uint32_t )39];
  uint8_t m40 = m[(uint32_t )40];
  uint8_t block40 = block[(uint32_t )40];
  uint8_t m41 = m[(uint32_t )41];
  uint8_t block41 = block[(uint32_t )41];
  uint8_t m42 = m[(uint32_t )42];
  uint8_t block42 = block[(uint32_t )42];
  uint8_t m43 = m[(uint32_t )43];
  uint8_t block43 = block[(uint32_t )43];
  uint8_t m44 = m[(uint32_t )44];
  uint8_t block44 = block[(uint32_t )44];
  uint8_t m45 = m[(uint32_t )45];
  uint8_t block45 = block[(uint32_t )45];
  uint8_t m46 = m[(uint32_t )46];
  uint8_t block46 = block[(uint32_t )46];
  uint8_t m47 = m[(uint32_t )47];
  uint8_t block47 = block[(uint32_t )47];
  uint8_t m48 = m[(uint32_t )48];
  uint8_t block48 = block[(uint32_t )48];
  uint8_t m49 = m[(uint32_t )49];
  uint8_t block49 = block[(uint32_t )49];
  uint8_t m50 = m[(uint32_t )50];
  uint8_t block50 = block[(uint32_t )50];
  uint8_t m51 = m[(uint32_t )51];
  uint8_t block51 = block[(uint32_t )51];
  uint8_t m52 = m[(uint32_t )52];
  uint8_t block52 = block[(uint32_t )52];
  uint8_t m53 = m[(uint32_t )53];
  uint8_t block53 = block[(uint32_t )53];
  uint8_t m54 = m[(uint32_t )54];
  uint8_t block54 = block[(uint32_t )54];
  uint8_t m55 = m[(uint32_t )55];
  uint8_t block55 = block[(uint32_t )55];
  uint8_t m56 = m[(uint32_t )56];
  uint8_t block56 = block[(uint32_t )56];
  uint8_t m57 = m[(uint32_t )57];
  uint8_t block57 = block[(uint32_t )57];
  uint8_t m58 = m[(uint32_t )58];
  uint8_t block58 = block[(uint32_t )58];
  uint8_t m59 = m[(uint32_t )59];
  uint8_t block59 = block[(uint32_t )59];
  uint8_t m60 = m[(uint32_t )60];
  uint8_t block60 = block[(uint32_t )60];
  uint8_t m61 = m[(uint32_t )61];
  uint8_t block61 = block[(uint32_t )61];
  uint8_t m62 = m[(uint32_t )62];
  uint8_t block62 = block[(uint32_t )62];
  uint8_t m63 = m[(uint32_t )63];
  uint8_t block63 = block[(uint32_t )63];
  c[(uint32_t )0] = m0 ^ block0;
  c[(uint32_t )1] = m1 ^ block1;
  c[(uint32_t )2] = m2 ^ block2;
  c[(uint32_t )3] = m3 ^ block3;
  c[(uint32_t )4] = m4 ^ block4;
  c[(uint32_t )5] = m5 ^ block5;
  c[(uint32_t )6] = m6 ^ block6;
  c[(uint32_t )7] = m7 ^ block7;
  c[(uint32_t )8] = m8 ^ block8;
  c[(uint32_t )9] = m9 ^ block9;
  c[(uint32_t )10] = m10 ^ block10;
  c[(uint32_t )11] = m11 ^ block11;
  c[(uint32_t )12] = m12 ^ block12;
  c[(uint32_t )13] = m13 ^ block13;
  c[(uint32_t )14] = m14 ^ block14;
  c[(uint32_t )15] = m15 ^ block15;
  c[(uint32_t )16] = m16 ^ block16;
  c[(uint32_t )17] = m17 ^ block17;
  c[(uint32_t )18] = m18 ^ block18;
  c[(uint32_t )19] = m19 ^ block19;
  c[(uint32_t )20] = m20 ^ block20;
  c[(uint32_t )21] = m21 ^ block21;
  c[(uint32_t )22] = m22 ^ block22;
  c[(uint32_t )23] = m23 ^ block23;
  c[(uint32_t )24] = m24 ^ block24;
  c[(uint32_t )25] = m25 ^ block25;
  c[(uint32_t )26] = m26 ^ block26;
  c[(uint32_t )27] = m27 ^ block27;
  c[(uint32_t )28] = m28 ^ block28;
  c[(uint32_t )29] = m29 ^ block29;
  c[(uint32_t )30] = m30 ^ block30;
  c[(uint32_t )31] = m31 ^ block31;
  c[(uint32_t )32] = m32 ^ block32;
  c[(uint32_t )33] = m33 ^ block33;
  c[(uint32_t )34] = m34 ^ block34;
  c[(uint32_t )35] = m35 ^ block35;
  c[(uint32_t )36] = m36 ^ block36;
  c[(uint32_t )37] = m37 ^ block37;
  c[(uint32_t )38] = m38 ^ block38;
  c[(uint32_t )39] = m39 ^ block39;
  c[(uint32_t )40] = m40 ^ block40;
  c[(uint32_t )41] = m41 ^ block41;
  c[(uint32_t )42] = m42 ^ block42;
  c[(uint32_t )43] = m43 ^ block43;
  c[(uint32_t )44] = m44 ^ block44;
  c[(uint32_t )45] = m45 ^ block45;
  c[(uint32_t )46] = m46 ^ block46;
  c[(uint32_t )47] = m47 ^ block47;
  c[(uint32_t )48] = m48 ^ block48;
  c[(uint32_t )49] = m49 ^ block49;
  c[(uint32_t )50] = m50 ^ block50;
  c[(uint32_t )51] = m51 ^ block51;
  c[(uint32_t )52] = m52 ^ block52;
  c[(uint32_t )53] = m53 ^ block53;
  c[(uint32_t )54] = m54 ^ block54;
  c[(uint32_t )55] = m55 ^ block55;
  c[(uint32_t )56] = m56 ^ block56;
  c[(uint32_t )57] = m57 ^ block57;
  c[(uint32_t )58] = m58 ^ block58;
  c[(uint32_t )59] = m59 ^ block59;
  c[(uint32_t )60] = m60 ^ block60;
  c[(uint32_t )61] = m61 ^ block61;
  c[(uint32_t )62] = m62 ^ block62;
  c[(uint32_t )63] = m63 ^ block63;
}

void
Hacl_Symmetric_Salsa20_lemma_modifies_3(
  uint8_t *c,
  uint8_t *input,
  uint8_t *block,
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1,
  FStar_HyperStack_mem h2
)
{
  return;
}

void
Hacl_Symmetric_Salsa20_lemma_modifies_3_(
  uint8_t *c,
  uint8_t *input,
  uint8_t *block,
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1,
  FStar_HyperStack_mem h2
)
{
  return;
}

uint64_t
Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor_ic_loop(
  uint8_t *c,
  uint8_t *m,
  uint8_t *block,
  uint8_t *input,
  uint8_t *kcopy,
  uint64_t mlen
)
{
  if (mlen < (uint64_t )64)
    return mlen;
  else
  {
    Hacl_Symmetric_Salsa20_crypto_core_salsa20(block, input, kcopy);
    Hacl_Symmetric_Salsa20_xor_(c, m, block);
    uint8_t i8 = input[(uint32_t )8];
    uint8_t i9 = input[(uint32_t )9];
    uint8_t i10 = input[(uint32_t )10];
    uint8_t i11 = input[(uint32_t )11];
    uint8_t i12 = input[(uint32_t )12];
    uint8_t i13 = input[(uint32_t )13];
    uint8_t i14 = input[(uint32_t )14];
    uint8_t i15 = input[(uint32_t )15];
    uint64_t
    u =
      (uint64_t )i8
      + ((uint64_t )i9 << (uint32_t )8)
      + ((uint64_t )i10 << (uint32_t )16)
      + ((uint64_t )i11 << (uint32_t )24)
      + ((uint64_t )i12 << (uint32_t )32)
      + ((uint64_t )i13 << (uint32_t )40)
      + ((uint64_t )i14 << (uint32_t )48)
      + ((uint64_t )i15 << (uint32_t )56)
      + (uint64_t )1;
    input[(uint32_t )8] = (uint8_t )u;
    input[(uint32_t )9] = (uint8_t )(u >> (uint32_t )8);
    input[(uint32_t )10] = (uint8_t )(u >> (uint32_t )16);
    input[(uint32_t )11] = (uint8_t )(u >> (uint32_t )24);
    input[(uint32_t )12] = (uint8_t )(u >> (uint32_t )32);
    input[(uint32_t )13] = (uint8_t )(u >> (uint32_t )40);
    input[(uint32_t )14] = (uint8_t )(u >> (uint32_t )48);
    input[(uint32_t )15] = (uint8_t )(u >> (uint32_t )56);
    uint64_t mlen0 = mlen - (uint64_t )64;
    uint8_t *c_ = c + (uint32_t )64;
    uint8_t *m0 = m + (uint32_t )64;
    uint64_t
    res =
      Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor_ic_loop(c_,
        m0,
        block,
        input,
        kcopy,
        mlen0);
    return res;
  }
}

void Hacl_Symmetric_Salsa20_xor_bytes(uint8_t *x, uint8_t *y, uint8_t *z, uint32_t len)
{
  if (len == (uint32_t )0)
    return;
  else
  {
    uint32_t i = len - (uint32_t )1;
    uint8_t yi = y[i];
    uint8_t zi = z[i];
    x[i] = yi ^ zi;
    Hacl_Symmetric_Salsa20_xor_bytes(x, y, z, i);
    return;
  }
}

uint32_t Hacl_Symmetric_Salsa20_mod_64(uint64_t mlen)
{
  return (uint32_t )(mlen & (uint64_t )63);
}

void
Hacl_Symmetric_Salsa20_lemma_modifies_3_1(
  uint8_t *c,
  uint8_t *input,
  uint8_t *block,
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1,
  FStar_HyperStack_mem h2,
  FStar_HyperStack_mem h3
)
{
  return;
}

void
Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor_ic__(
  uint8_t *n,
  uint64_t ic,
  uint8_t *k,
  uint8_t *local_state
)
{
  uint8_t *input = local_state + (uint32_t )0;
  uint8_t *block = local_state + (uint32_t )16;
  uint8_t *kcopy = local_state + (uint32_t )80;
  uint8_t k0 = k[(uint32_t )0];
  uint8_t k1 = k[(uint32_t )1];
  uint8_t k2 = k[(uint32_t )2];
  uint8_t k3 = k[(uint32_t )3];
  uint8_t k4 = k[(uint32_t )4];
  uint8_t k5 = k[(uint32_t )5];
  uint8_t k6 = k[(uint32_t )6];
  uint8_t k7 = k[(uint32_t )7];
  uint8_t k8 = k[(uint32_t )8];
  uint8_t k9 = k[(uint32_t )9];
  uint8_t k10 = k[(uint32_t )10];
  uint8_t k11 = k[(uint32_t )11];
  uint8_t k12 = k[(uint32_t )12];
  uint8_t k13 = k[(uint32_t )13];
  uint8_t k14 = k[(uint32_t )14];
  uint8_t k15 = k[(uint32_t )15];
  uint8_t k16 = k[(uint32_t )16];
  uint8_t k17 = k[(uint32_t )17];
  uint8_t k18 = k[(uint32_t )18];
  uint8_t k19 = k[(uint32_t )19];
  uint8_t k20 = k[(uint32_t )20];
  uint8_t k21 = k[(uint32_t )21];
  uint8_t k22 = k[(uint32_t )22];
  uint8_t k23 = k[(uint32_t )23];
  uint8_t k24 = k[(uint32_t )24];
  uint8_t k25 = k[(uint32_t )25];
  uint8_t k26 = k[(uint32_t )26];
  uint8_t k27 = k[(uint32_t )27];
  uint8_t k28 = k[(uint32_t )28];
  uint8_t k29 = k[(uint32_t )29];
  uint8_t k30 = k[(uint32_t )30];
  uint8_t k31 = k[(uint32_t )31];
  uint8_t n0 = n[(uint32_t )0];
  uint8_t n1 = n[(uint32_t )1];
  uint8_t n2 = n[(uint32_t )2];
  uint8_t n3 = n[(uint32_t )3];
  uint8_t n4 = n[(uint32_t )4];
  uint8_t n5 = n[(uint32_t )5];
  uint8_t n6 = n[(uint32_t )6];
  uint8_t n7 = n[(uint32_t )7];
  kcopy[(uint32_t )0] = k0;
  kcopy[(uint32_t )1] = k1;
  kcopy[(uint32_t )2] = k2;
  kcopy[(uint32_t )3] = k3;
  kcopy[(uint32_t )4] = k4;
  kcopy[(uint32_t )5] = k5;
  kcopy[(uint32_t )6] = k6;
  kcopy[(uint32_t )7] = k7;
  kcopy[(uint32_t )8] = k8;
  kcopy[(uint32_t )9] = k9;
  kcopy[(uint32_t )10] = k10;
  kcopy[(uint32_t )11] = k11;
  kcopy[(uint32_t )12] = k12;
  kcopy[(uint32_t )13] = k13;
  kcopy[(uint32_t )14] = k14;
  kcopy[(uint32_t )15] = k15;
  kcopy[(uint32_t )16] = k16;
  kcopy[(uint32_t )17] = k17;
  kcopy[(uint32_t )18] = k18;
  kcopy[(uint32_t )19] = k19;
  kcopy[(uint32_t )20] = k20;
  kcopy[(uint32_t )21] = k21;
  kcopy[(uint32_t )22] = k22;
  kcopy[(uint32_t )23] = k23;
  kcopy[(uint32_t )24] = k24;
  kcopy[(uint32_t )25] = k25;
  kcopy[(uint32_t )26] = k26;
  kcopy[(uint32_t )27] = k27;
  kcopy[(uint32_t )28] = k28;
  kcopy[(uint32_t )29] = k29;
  kcopy[(uint32_t )30] = k30;
  kcopy[(uint32_t )31] = k31;
  input[(uint32_t )0] = n0;
  input[(uint32_t )1] = n1;
  input[(uint32_t )2] = n2;
  input[(uint32_t )3] = n3;
  input[(uint32_t )4] = n4;
  input[(uint32_t )5] = n5;
  input[(uint32_t )6] = n6;
  input[(uint32_t )7] = n7;
  input[(uint32_t )8] = (uint8_t )ic;
  input[(uint32_t )9] = (uint8_t )(ic >> (uint32_t )8);
  input[(uint32_t )10] = (uint8_t )(ic >> (uint32_t )16);
  input[(uint32_t )11] = (uint8_t )(ic >> (uint32_t )24);
  input[(uint32_t )12] = (uint8_t )(ic >> (uint32_t )32);
  input[(uint32_t )13] = (uint8_t )(ic >> (uint32_t )40);
  input[(uint32_t )14] = (uint8_t )(ic >> (uint32_t )48);
  input[(uint32_t )15] = (uint8_t )(ic >> (uint32_t )56);
}

void
Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor_ic_(
  uint8_t *c,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n,
  uint64_t ic,
  uint8_t *k
)
{
  uint8_t zero = (uint8_t )0;
  uint8_t local_state[112];
  for (uintmax_t i = 0; i < (uint32_t )112; ++i)
    local_state[i] = zero;
  uint8_t *input = local_state + (uint32_t )0;
  uint8_t *block = local_state + (uint32_t )16;
  uint8_t *kcopy = local_state + (uint32_t )80;
  Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor_ic__(n, ic, k, local_state);
  uint64_t
  uu____2129 =
    Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor_ic_loop(c,
      m,
      block,
      input,
      kcopy,
      mlen);
  uint32_t mlen_ = (uint32_t )(mlen & (uint64_t )63);
  uint32_t off = (uint32_t )mlen - mlen_;
  if (mlen_ >= (uint32_t )0)
  {
    Hacl_Symmetric_Salsa20_crypto_core_salsa20(block, input, kcopy);
    Hacl_Symmetric_Salsa20_xor_bytes(c + off, m + off, block, mlen_);
  }
}

void
Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor_ic(
  uint8_t *c,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n,
  uint64_t ic,
  uint8_t *k
)
{
  if (mlen == (uint64_t )0)
    return;
  else
  {
    Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor_ic_(c, m, mlen, n, ic, k);
    return;
  }
}

uint64_t
Hacl_Symmetric_Salsa20_crypto_stream_salsa20_loop(
  uint8_t *c,
  uint64_t clen,
  uint8_t *n,
  uint8_t *k,
  uint8_t *input
)
{
  if (clen < (uint64_t )64)
    return clen;
  else
  {
    Hacl_Symmetric_Salsa20_crypto_core_salsa20(c + (uint32_t )0, input, k);
    uint8_t i8 = input[(uint32_t )8];
    uint8_t i9 = input[(uint32_t )9];
    uint8_t i10 = input[(uint32_t )10];
    uint8_t i11 = input[(uint32_t )11];
    uint8_t i12 = input[(uint32_t )12];
    uint8_t i13 = input[(uint32_t )13];
    uint8_t i14 = input[(uint32_t )14];
    uint8_t i15 = input[(uint32_t )15];
    uint64_t
    u =
      (uint64_t )i8
      + ((uint64_t )i9 << (uint32_t )8)
      + ((uint64_t )i10 << (uint32_t )16)
      + ((uint64_t )i11 << (uint32_t )24)
      + ((uint64_t )i12 << (uint32_t )32)
      + ((uint64_t )i13 << (uint32_t )40)
      + ((uint64_t )i14 << (uint32_t )48)
      + ((uint64_t )i15 << (uint32_t )56)
      + (uint64_t )1;
    input[(uint32_t )8] = (uint8_t )u;
    input[(uint32_t )9] = (uint8_t )(u >> (uint32_t )8);
    input[(uint32_t )10] = (uint8_t )(u >> (uint32_t )16);
    input[(uint32_t )11] = (uint8_t )(u >> (uint32_t )24);
    input[(uint32_t )12] = (uint8_t )(u >> (uint32_t )32);
    input[(uint32_t )13] = (uint8_t )(u >> (uint32_t )40);
    input[(uint32_t )14] = (uint8_t )(u >> (uint32_t )48);
    input[(uint32_t )15] = (uint8_t )(u >> (uint32_t )56);
    uint64_t clen0 = clen - (uint64_t )64;
    uint8_t *c0 = c + (uint32_t )64;
    return Hacl_Symmetric_Salsa20_crypto_stream_salsa20_loop(c0, clen0, n, k, input);
  }
}

void
Hacl_Symmetric_Salsa20_lemma_modifies_4(
  uint8_t *c,
  uint8_t *input,
  uint8_t *block,
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1,
  FStar_HyperStack_mem h2,
  FStar_HyperStack_mem h3
)
{
  return;
}

void
Hacl_Symmetric_Salsa20_crypto_stream_salsa20_(uint8_t *n, uint8_t *k, uint8_t *local_state)
{
  uint8_t zero = (uint8_t )0;
  uint8_t *input = local_state + (uint32_t )0;
  uint8_t *block = local_state + (uint32_t )16;
  uint8_t *kcopy = local_state + (uint32_t )80;
  uint8_t k0 = k[(uint32_t )0];
  uint8_t k1 = k[(uint32_t )1];
  uint8_t k2 = k[(uint32_t )2];
  uint8_t k3 = k[(uint32_t )3];
  uint8_t k4 = k[(uint32_t )4];
  uint8_t k5 = k[(uint32_t )5];
  uint8_t k6 = k[(uint32_t )6];
  uint8_t k7 = k[(uint32_t )7];
  uint8_t k8 = k[(uint32_t )8];
  uint8_t k9 = k[(uint32_t )9];
  uint8_t k10 = k[(uint32_t )10];
  uint8_t k11 = k[(uint32_t )11];
  uint8_t k12 = k[(uint32_t )12];
  uint8_t k13 = k[(uint32_t )13];
  uint8_t k14 = k[(uint32_t )14];
  uint8_t k15 = k[(uint32_t )15];
  uint8_t k16 = k[(uint32_t )16];
  uint8_t k17 = k[(uint32_t )17];
  uint8_t k18 = k[(uint32_t )18];
  uint8_t k19 = k[(uint32_t )19];
  uint8_t k20 = k[(uint32_t )20];
  uint8_t k21 = k[(uint32_t )21];
  uint8_t k22 = k[(uint32_t )22];
  uint8_t k23 = k[(uint32_t )23];
  uint8_t k24 = k[(uint32_t )24];
  uint8_t k25 = k[(uint32_t )25];
  uint8_t k26 = k[(uint32_t )26];
  uint8_t k27 = k[(uint32_t )27];
  uint8_t k28 = k[(uint32_t )28];
  uint8_t k29 = k[(uint32_t )29];
  uint8_t k30 = k[(uint32_t )30];
  uint8_t k31 = k[(uint32_t )31];
  uint8_t n0 = n[(uint32_t )0];
  uint8_t n1 = n[(uint32_t )1];
  uint8_t n2 = n[(uint32_t )2];
  uint8_t n3 = n[(uint32_t )3];
  uint8_t n4 = n[(uint32_t )4];
  uint8_t n5 = n[(uint32_t )5];
  uint8_t n6 = n[(uint32_t )6];
  uint8_t n7 = n[(uint32_t )7];
  kcopy[(uint32_t )0] = k0;
  kcopy[(uint32_t )1] = k1;
  kcopy[(uint32_t )2] = k2;
  kcopy[(uint32_t )3] = k3;
  kcopy[(uint32_t )4] = k4;
  kcopy[(uint32_t )5] = k5;
  kcopy[(uint32_t )6] = k6;
  kcopy[(uint32_t )7] = k7;
  kcopy[(uint32_t )8] = k8;
  kcopy[(uint32_t )9] = k9;
  kcopy[(uint32_t )10] = k10;
  kcopy[(uint32_t )11] = k11;
  kcopy[(uint32_t )12] = k12;
  kcopy[(uint32_t )13] = k13;
  kcopy[(uint32_t )14] = k14;
  kcopy[(uint32_t )15] = k15;
  kcopy[(uint32_t )16] = k16;
  kcopy[(uint32_t )17] = k17;
  kcopy[(uint32_t )18] = k18;
  kcopy[(uint32_t )19] = k19;
  kcopy[(uint32_t )20] = k20;
  kcopy[(uint32_t )21] = k21;
  kcopy[(uint32_t )22] = k22;
  kcopy[(uint32_t )23] = k23;
  kcopy[(uint32_t )24] = k24;
  kcopy[(uint32_t )25] = k25;
  kcopy[(uint32_t )26] = k26;
  kcopy[(uint32_t )27] = k27;
  kcopy[(uint32_t )28] = k28;
  kcopy[(uint32_t )29] = k29;
  kcopy[(uint32_t )30] = k30;
  kcopy[(uint32_t )31] = k31;
  input[(uint32_t )0] = n0;
  input[(uint32_t )1] = n1;
  input[(uint32_t )2] = n2;
  input[(uint32_t )3] = n3;
  input[(uint32_t )4] = n4;
  input[(uint32_t )5] = n5;
  input[(uint32_t )6] = n6;
  input[(uint32_t )7] = n7;
  input[(uint32_t )8] = zero;
  input[(uint32_t )9] = zero;
  input[(uint32_t )10] = zero;
  input[(uint32_t )11] = zero;
  input[(uint32_t )12] = zero;
  input[(uint32_t )13] = zero;
  input[(uint32_t )14] = zero;
  input[(uint32_t )15] = zero;
}

void
Hacl_Symmetric_Salsa20_crypto_stream_salsa20(uint8_t *c, uint64_t clen, uint8_t *n, uint8_t *k)
{
  if (clen == (uint64_t )0)
  {
    
  }
  else
  {
    uint32_t clen_ = (uint32_t )(clen & (uint64_t )63);
    uint32_t off = (uint32_t )clen - clen_;
    uint8_t zero = (uint8_t )0;
    uint8_t local_state[112];
    for (uintmax_t i = 0; i < (uint32_t )112; ++i)
      local_state[i] = zero;
    uint8_t *input = local_state + (uint32_t )0;
    uint8_t *block = local_state + (uint32_t )16;
    uint8_t *kcopy = local_state + (uint32_t )80;
    Hacl_Symmetric_Salsa20_crypto_stream_salsa20_(n, k, local_state);
    uint64_t
    uu____2822 = Hacl_Symmetric_Salsa20_crypto_stream_salsa20_loop(c, clen, n, kcopy, input);
    if (clen_ >= (uint32_t )0)
    {
      Hacl_Symmetric_Salsa20_crypto_core_salsa20(block, input, kcopy);
      memcpy(c + off, block, clen_ * sizeof block[0]);
    }
  }
}

void
Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor(
  uint8_t *c,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n,
  uint8_t *k
)
{
  Hacl_Symmetric_Salsa20_crypto_stream_salsa20_xor_ic(c, m, mlen, n, (uint64_t )0, k);
  return;
}

