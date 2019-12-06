
#include "Hacl_NaCl.h"
#include "ctypes_cstubs_internals.h"
value _1_Hacl_NaCl_crypto_secretbox_detached(value x6, value x5, value x4,
                                             value x3, value x2, value x1)
{
   uint8_t* x7 = CTYPES_ADDR_OF_FATPTR(x6);
   uint8_t* x8 = CTYPES_ADDR_OF_FATPTR(x5);
   uint8_t* x9 = CTYPES_ADDR_OF_FATPTR(x4);
   uint32_t x10 = Uint32_val(x3);
   uint8_t* x13 = CTYPES_ADDR_OF_FATPTR(x2);
   uint8_t* x14 = CTYPES_ADDR_OF_FATPTR(x1);
   uint32_t x15 =
   Hacl_NaCl_crypto_secretbox_detached(x7, x8, x9, x10, x13, x14);
   return integers_copy_uint32(x15);
}
value _1_Hacl_NaCl_crypto_secretbox_detached_byte6(value* argv, int argc)
{
   value x16 = argv[5];
   value x17 = argv[4];
   value x18 = argv[3];
   value x19 = argv[2];
   value x20 = argv[1];
   value x21 = argv[0];
   return
     _1_Hacl_NaCl_crypto_secretbox_detached(x21, x20, x19, x18, x17, x16);
}
value _2_Hacl_NaCl_crypto_secretbox_open_detached(value x27, value x26,
                                                  value x25, value x24,
                                                  value x23, value x22)
{
   uint8_t* x28 = CTYPES_ADDR_OF_FATPTR(x27);
   uint8_t* x29 = CTYPES_ADDR_OF_FATPTR(x26);
   uint8_t* x30 = CTYPES_ADDR_OF_FATPTR(x25);
   uint32_t x31 = Uint32_val(x24);
   uint8_t* x34 = CTYPES_ADDR_OF_FATPTR(x23);
   uint8_t* x35 = CTYPES_ADDR_OF_FATPTR(x22);
   uint32_t x36 =
   Hacl_NaCl_crypto_secretbox_open_detached(x28, x29, x30, x31, x34, x35);
   return integers_copy_uint32(x36);
}
value _2_Hacl_NaCl_crypto_secretbox_open_detached_byte6(value* argv,
                                                        int argc)
{
   value x37 = argv[5];
   value x38 = argv[4];
   value x39 = argv[3];
   value x40 = argv[2];
   value x41 = argv[1];
   value x42 = argv[0];
   return
     _2_Hacl_NaCl_crypto_secretbox_open_detached(x42, x41, x40, x39, 
                                                 x38, x37);
}
value _3_Hacl_NaCl_crypto_secretbox_easy(value x47, value x46, value x45,
                                         value x44, value x43)
{
   uint8_t* x48 = CTYPES_ADDR_OF_FATPTR(x47);
   uint8_t* x49 = CTYPES_ADDR_OF_FATPTR(x46);
   uint32_t x50 = Uint32_val(x45);
   uint8_t* x53 = CTYPES_ADDR_OF_FATPTR(x44);
   uint8_t* x54 = CTYPES_ADDR_OF_FATPTR(x43);
   uint32_t x55 = Hacl_NaCl_crypto_secretbox_easy(x48, x49, x50, x53, x54);
   return integers_copy_uint32(x55);
}
value _4_Hacl_NaCl_crypto_secretbox_open_easy(value x60, value x59,
                                              value x58, value x57,
                                              value x56)
{
   uint8_t* x61 = CTYPES_ADDR_OF_FATPTR(x60);
   uint8_t* x62 = CTYPES_ADDR_OF_FATPTR(x59);
   uint32_t x63 = Uint32_val(x58);
   uint8_t* x66 = CTYPES_ADDR_OF_FATPTR(x57);
   uint8_t* x67 = CTYPES_ADDR_OF_FATPTR(x56);
   uint32_t x68 =
   Hacl_NaCl_crypto_secretbox_open_easy(x61, x62, x63, x66, x67);
   return integers_copy_uint32(x68);
}
value _5_Hacl_NaCl_crypto_box_beforenm(value x71, value x70, value x69)
{
   uint8_t* x72 = CTYPES_ADDR_OF_FATPTR(x71);
   uint8_t* x73 = CTYPES_ADDR_OF_FATPTR(x70);
   uint8_t* x74 = CTYPES_ADDR_OF_FATPTR(x69);
   uint32_t x75 = Hacl_NaCl_crypto_box_beforenm(x72, x73, x74);
   return integers_copy_uint32(x75);
}
value _6_Hacl_NaCl_crypto_box_detached_afternm(value x81, value x80,
                                               value x79, value x78,
                                               value x77, value x76)
{
   uint8_t* x82 = CTYPES_ADDR_OF_FATPTR(x81);
   uint8_t* x83 = CTYPES_ADDR_OF_FATPTR(x80);
   uint8_t* x84 = CTYPES_ADDR_OF_FATPTR(x79);
   uint32_t x85 = Uint32_val(x78);
   uint8_t* x88 = CTYPES_ADDR_OF_FATPTR(x77);
   uint8_t* x89 = CTYPES_ADDR_OF_FATPTR(x76);
   uint32_t x90 =
   Hacl_NaCl_crypto_box_detached_afternm(x82, x83, x84, x85, x88, x89);
   return integers_copy_uint32(x90);
}
value _6_Hacl_NaCl_crypto_box_detached_afternm_byte6(value* argv, int argc)
{
   value x91 = argv[5];
   value x92 = argv[4];
   value x93 = argv[3];
   value x94 = argv[2];
   value x95 = argv[1];
   value x96 = argv[0];
   return
     _6_Hacl_NaCl_crypto_box_detached_afternm(x96, x95, x94, x93, x92, x91);
}
value _7_Hacl_NaCl_crypto_box_detached(value x103, value x102, value x101,
                                       value x100, value x99, value x98,
                                       value x97)
{
   uint8_t* x104 = CTYPES_ADDR_OF_FATPTR(x103);
   uint8_t* x105 = CTYPES_ADDR_OF_FATPTR(x102);
   uint8_t* x106 = CTYPES_ADDR_OF_FATPTR(x101);
   uint32_t x107 = Uint32_val(x100);
   uint8_t* x110 = CTYPES_ADDR_OF_FATPTR(x99);
   uint8_t* x111 = CTYPES_ADDR_OF_FATPTR(x98);
   uint8_t* x112 = CTYPES_ADDR_OF_FATPTR(x97);
   uint32_t x113 =
   Hacl_NaCl_crypto_box_detached(x104, x105, x106, x107, x110, x111, x112);
   return integers_copy_uint32(x113);
}
value _7_Hacl_NaCl_crypto_box_detached_byte7(value* argv, int argc)
{
   value x114 = argv[6];
   value x115 = argv[5];
   value x116 = argv[4];
   value x117 = argv[3];
   value x118 = argv[2];
   value x119 = argv[1];
   value x120 = argv[0];
   return
     _7_Hacl_NaCl_crypto_box_detached(x120, x119, x118, x117, x116, x115,
                                      x114);
}
value _8_Hacl_NaCl_crypto_box_open_detached_afternm(value x126, value x125,
                                                    value x124, value x123,
                                                    value x122, value x121)
{
   uint8_t* x127 = CTYPES_ADDR_OF_FATPTR(x126);
   uint8_t* x128 = CTYPES_ADDR_OF_FATPTR(x125);
   uint8_t* x129 = CTYPES_ADDR_OF_FATPTR(x124);
   uint32_t x130 = Uint32_val(x123);
   uint8_t* x133 = CTYPES_ADDR_OF_FATPTR(x122);
   uint8_t* x134 = CTYPES_ADDR_OF_FATPTR(x121);
   uint32_t x135 =
   Hacl_NaCl_crypto_box_open_detached_afternm(x127, x128, x129, x130, 
                                              x133, x134);
   return integers_copy_uint32(x135);
}
value _8_Hacl_NaCl_crypto_box_open_detached_afternm_byte6(value* argv,
                                                          int argc)
{
   value x136 = argv[5];
   value x137 = argv[4];
   value x138 = argv[3];
   value x139 = argv[2];
   value x140 = argv[1];
   value x141 = argv[0];
   return
     _8_Hacl_NaCl_crypto_box_open_detached_afternm(x141, x140, x139, 
                                                   x138, x137, x136);
}
value _9_Hacl_NaCl_crypto_box_open_detached(value x148, value x147,
                                            value x146, value x145,
                                            value x144, value x143,
                                            value x142)
{
   uint8_t* x149 = CTYPES_ADDR_OF_FATPTR(x148);
   uint8_t* x150 = CTYPES_ADDR_OF_FATPTR(x147);
   uint8_t* x151 = CTYPES_ADDR_OF_FATPTR(x146);
   uint32_t x152 = Uint32_val(x145);
   uint8_t* x155 = CTYPES_ADDR_OF_FATPTR(x144);
   uint8_t* x156 = CTYPES_ADDR_OF_FATPTR(x143);
   uint8_t* x157 = CTYPES_ADDR_OF_FATPTR(x142);
   uint32_t x158 =
   Hacl_NaCl_crypto_box_open_detached(x149, x150, x151, x152, x155, x156,
                                      x157);
   return integers_copy_uint32(x158);
}
value _9_Hacl_NaCl_crypto_box_open_detached_byte7(value* argv, int argc)
{
   value x159 = argv[6];
   value x160 = argv[5];
   value x161 = argv[4];
   value x162 = argv[3];
   value x163 = argv[2];
   value x164 = argv[1];
   value x165 = argv[0];
   return
     _9_Hacl_NaCl_crypto_box_open_detached(x165, x164, x163, x162, x161,
                                           x160, x159);
}
value _10_Hacl_NaCl_crypto_box_easy_afternm(value x170, value x169,
                                            value x168, value x167,
                                            value x166)
{
   uint8_t* x171 = CTYPES_ADDR_OF_FATPTR(x170);
   uint8_t* x172 = CTYPES_ADDR_OF_FATPTR(x169);
   uint32_t x173 = Uint32_val(x168);
   uint8_t* x176 = CTYPES_ADDR_OF_FATPTR(x167);
   uint8_t* x177 = CTYPES_ADDR_OF_FATPTR(x166);
   uint32_t x178 =
   Hacl_NaCl_crypto_box_easy_afternm(x171, x172, x173, x176, x177);
   return integers_copy_uint32(x178);
}
value _11_Hacl_NaCl_crypto_box_easy(value x184, value x183, value x182,
                                    value x181, value x180, value x179)
{
   uint8_t* x185 = CTYPES_ADDR_OF_FATPTR(x184);
   uint8_t* x186 = CTYPES_ADDR_OF_FATPTR(x183);
   uint32_t x187 = Uint32_val(x182);
   uint8_t* x190 = CTYPES_ADDR_OF_FATPTR(x181);
   uint8_t* x191 = CTYPES_ADDR_OF_FATPTR(x180);
   uint8_t* x192 = CTYPES_ADDR_OF_FATPTR(x179);
   uint32_t x193 =
   Hacl_NaCl_crypto_box_easy(x185, x186, x187, x190, x191, x192);
   return integers_copy_uint32(x193);
}
value _11_Hacl_NaCl_crypto_box_easy_byte6(value* argv, int argc)
{
   value x194 = argv[5];
   value x195 = argv[4];
   value x196 = argv[3];
   value x197 = argv[2];
   value x198 = argv[1];
   value x199 = argv[0];
   return _11_Hacl_NaCl_crypto_box_easy(x199, x198, x197, x196, x195, x194);
}
value _12_Hacl_NaCl_crypto_box_open_easy_afternm(value x204, value x203,
                                                 value x202, value x201,
                                                 value x200)
{
   uint8_t* x205 = CTYPES_ADDR_OF_FATPTR(x204);
   uint8_t* x206 = CTYPES_ADDR_OF_FATPTR(x203);
   uint32_t x207 = Uint32_val(x202);
   uint8_t* x210 = CTYPES_ADDR_OF_FATPTR(x201);
   uint8_t* x211 = CTYPES_ADDR_OF_FATPTR(x200);
   uint32_t x212 =
   Hacl_NaCl_crypto_box_open_easy_afternm(x205, x206, x207, x210, x211);
   return integers_copy_uint32(x212);
}
value _13_Hacl_NaCl_crypto_box_open_easy(value x218, value x217, value x216,
                                         value x215, value x214, value x213)
{
   uint8_t* x219 = CTYPES_ADDR_OF_FATPTR(x218);
   uint8_t* x220 = CTYPES_ADDR_OF_FATPTR(x217);
   uint32_t x221 = Uint32_val(x216);
   uint8_t* x224 = CTYPES_ADDR_OF_FATPTR(x215);
   uint8_t* x225 = CTYPES_ADDR_OF_FATPTR(x214);
   uint8_t* x226 = CTYPES_ADDR_OF_FATPTR(x213);
   uint32_t x227 =
   Hacl_NaCl_crypto_box_open_easy(x219, x220, x221, x224, x225, x226);
   return integers_copy_uint32(x227);
}
value _13_Hacl_NaCl_crypto_box_open_easy_byte6(value* argv, int argc)
{
   value x228 = argv[5];
   value x229 = argv[4];
   value x230 = argv[3];
   value x231 = argv[2];
   value x232 = argv[1];
   value x233 = argv[0];
   return
     _13_Hacl_NaCl_crypto_box_open_easy(x233, x232, x231, x230, x229, x228);
}
