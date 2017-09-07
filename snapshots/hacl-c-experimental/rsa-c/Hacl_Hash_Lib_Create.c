#include "Hacl_Hash_Lib_Create.h"

uint8_t Hacl_Hash_Lib_Create_u8_to_s8(uint8_t a)
{
  return a;
}

uint32_t Hacl_Hash_Lib_Create_u32_to_s32(uint32_t a)
{
  return a;
}

uint64_t Hacl_Hash_Lib_Create_u32_to_s64(uint32_t a)
{
  return (uint64_t )a;
}

uint8_t Hacl_Hash_Lib_Create_s32_to_s8(uint32_t a)
{
  return (uint8_t )a;
}

uint64_t Hacl_Hash_Lib_Create_s32_to_s64(uint32_t a)
{
  return (uint64_t )a;
}

uint64_t Hacl_Hash_Lib_Create_u64_to_s64(uint64_t a)
{
  return a;
}

void
Hacl_Hash_Lib_Create_hupd_4(uint32_t *buf, uint32_t v0, uint32_t v1, uint32_t v2, uint32_t v3)
{
  buf[0] = v0;
  buf[1] = v1;
  buf[2] = v2;
  buf[3] = v3;
}

void
Hacl_Hash_Lib_Create_hupd_8(
  uint32_t *buf,
  uint32_t v0,
  uint32_t v1,
  uint32_t v2,
  uint32_t v3,
  uint32_t v4,
  uint32_t v5,
  uint32_t v6,
  uint32_t v7
)
{
  uint32_t *p1 = buf;
  uint32_t *p2 = buf + (uint32_t )4;
  p1[0] = v0;
  p1[1] = v1;
  p1[2] = v2;
  p1[3] = v3;
  p2[0] = v4;
  p2[1] = v5;
  p2[2] = v6;
  p2[3] = v7;
}

void
Hacl_Hash_Lib_Create_hupd_16(
  uint32_t *buf,
  uint32_t v0,
  uint32_t v1,
  uint32_t v2,
  uint32_t v3,
  uint32_t v4,
  uint32_t v5,
  uint32_t v6,
  uint32_t v7,
  uint32_t v8,
  uint32_t v9,
  uint32_t v10,
  uint32_t v11,
  uint32_t v12,
  uint32_t v13,
  uint32_t v14,
  uint32_t v15
)
{
  uint32_t *p10 = buf;
  uint32_t *p20 = buf + (uint32_t )8;
  uint32_t *p1 = p10;
  uint32_t *p21 = p10 + (uint32_t )4;
  p1[0] = v0;
  p1[1] = v1;
  p1[2] = v2;
  p1[3] = v3;
  p21[0] = v4;
  p21[1] = v5;
  p21[2] = v6;
  p21[3] = v7;
  uint32_t *p11 = p20;
  uint32_t *p2 = p20 + (uint32_t )4;
  p11[0] = v8;
  p11[1] = v9;
  p11[2] = v10;
  p11[3] = v11;
  p2[0] = v12;
  p2[1] = v13;
  p2[2] = v14;
  p2[3] = v15;
}

void
Hacl_Hash_Lib_Create_hupd_64(
  uint32_t *buf,
  uint32_t v0,
  uint32_t v1,
  uint32_t v2,
  uint32_t v3,
  uint32_t v4,
  uint32_t v5,
  uint32_t v6,
  uint32_t v7,
  uint32_t v8,
  uint32_t v9,
  uint32_t v10,
  uint32_t v11,
  uint32_t v12,
  uint32_t v13,
  uint32_t v14,
  uint32_t v15,
  uint32_t v16,
  uint32_t v17,
  uint32_t v18,
  uint32_t v19,
  uint32_t v20,
  uint32_t v21,
  uint32_t v22,
  uint32_t v23,
  uint32_t v24,
  uint32_t v25,
  uint32_t v26,
  uint32_t v27,
  uint32_t v28,
  uint32_t v29,
  uint32_t v30,
  uint32_t v31,
  uint32_t v32,
  uint32_t v33,
  uint32_t v34,
  uint32_t v35,
  uint32_t v36,
  uint32_t v37,
  uint32_t v38,
  uint32_t v39,
  uint32_t v40,
  uint32_t v41,
  uint32_t v42,
  uint32_t v43,
  uint32_t v44,
  uint32_t v45,
  uint32_t v46,
  uint32_t v47,
  uint32_t v48,
  uint32_t v49,
  uint32_t v50,
  uint32_t v51,
  uint32_t v52,
  uint32_t v53,
  uint32_t v54,
  uint32_t v55,
  uint32_t v56,
  uint32_t v57,
  uint32_t v58,
  uint32_t v59,
  uint32_t v60,
  uint32_t v61,
  uint32_t v62,
  uint32_t v63
)
{
  uint32_t *p10 = buf;
  uint32_t *p20 = buf + (uint32_t )16;
  uint32_t *p3 = buf + (uint32_t )32;
  uint32_t *p4 = buf + (uint32_t )48;
  uint32_t *p11 = p10;
  uint32_t *p21 = p10 + (uint32_t )8;
  uint32_t *p12 = p11;
  uint32_t *p22 = p11 + (uint32_t )4;
  p12[0] = v0;
  p12[1] = v1;
  p12[2] = v2;
  p12[3] = v3;
  p22[0] = v4;
  p22[1] = v5;
  p22[2] = v6;
  p22[3] = v7;
  uint32_t *p13 = p21;
  uint32_t *p23 = p21 + (uint32_t )4;
  p13[0] = v8;
  p13[1] = v9;
  p13[2] = v10;
  p13[3] = v11;
  p23[0] = v12;
  p23[1] = v13;
  p23[2] = v14;
  p23[3] = v15;
  uint32_t *p14 = p20;
  uint32_t *p24 = p20 + (uint32_t )8;
  uint32_t *p15 = p14;
  uint32_t *p25 = p14 + (uint32_t )4;
  p15[0] = v16;
  p15[1] = v17;
  p15[2] = v18;
  p15[3] = v19;
  p25[0] = v20;
  p25[1] = v21;
  p25[2] = v22;
  p25[3] = v23;
  uint32_t *p16 = p24;
  uint32_t *p26 = p24 + (uint32_t )4;
  p16[0] = v24;
  p16[1] = v25;
  p16[2] = v26;
  p16[3] = v27;
  p26[0] = v28;
  p26[1] = v29;
  p26[2] = v30;
  p26[3] = v31;
  uint32_t *p17 = p3;
  uint32_t *p27 = p3 + (uint32_t )8;
  uint32_t *p18 = p17;
  uint32_t *p28 = p17 + (uint32_t )4;
  p18[0] = v32;
  p18[1] = v33;
  p18[2] = v34;
  p18[3] = v35;
  p28[0] = v36;
  p28[1] = v37;
  p28[2] = v38;
  p28[3] = v39;
  uint32_t *p19 = p27;
  uint32_t *p29 = p27 + (uint32_t )4;
  p19[0] = v40;
  p19[1] = v41;
  p19[2] = v42;
  p19[3] = v43;
  p29[0] = v44;
  p29[1] = v45;
  p29[2] = v46;
  p29[3] = v47;
  uint32_t *p110 = p4;
  uint32_t *p210 = p4 + (uint32_t )8;
  uint32_t *p1 = p110;
  uint32_t *p211 = p110 + (uint32_t )4;
  p1[0] = v48;
  p1[1] = v49;
  p1[2] = v50;
  p1[3] = v51;
  p211[0] = v52;
  p211[1] = v53;
  p211[2] = v54;
  p211[3] = v55;
  uint32_t *p111 = p210;
  uint32_t *p2 = p210 + (uint32_t )4;
  p111[0] = v56;
  p111[1] = v57;
  p111[2] = v58;
  p111[3] = v59;
  p2[0] = v60;
  p2[1] = v61;
  p2[2] = v62;
  p2[3] = v63;
}

void
Hacl_Hash_Lib_Create_hupd64_4(
  uint64_t *buf,
  uint64_t v0,
  uint64_t v1,
  uint64_t v2,
  uint64_t v3
)
{
  buf[0] = v0;
  buf[1] = v1;
  buf[2] = v2;
  buf[3] = v3;
}

void
Hacl_Hash_Lib_Create_hupd64_8(
  uint64_t *buf,
  uint64_t v0,
  uint64_t v1,
  uint64_t v2,
  uint64_t v3,
  uint64_t v4,
  uint64_t v5,
  uint64_t v6,
  uint64_t v7
)
{
  uint64_t *p1 = buf;
  uint64_t *p2 = buf + (uint32_t )4;
  p1[0] = v0;
  p1[1] = v1;
  p1[2] = v2;
  p1[3] = v3;
  p2[0] = v4;
  p2[1] = v5;
  p2[2] = v6;
  p2[3] = v7;
}

void
Hacl_Hash_Lib_Create_hupd64_16(
  uint64_t *buf,
  uint64_t v0,
  uint64_t v1,
  uint64_t v2,
  uint64_t v3,
  uint64_t v4,
  uint64_t v5,
  uint64_t v6,
  uint64_t v7,
  uint64_t v8,
  uint64_t v9,
  uint64_t v10,
  uint64_t v11,
  uint64_t v12,
  uint64_t v13,
  uint64_t v14,
  uint64_t v15
)
{
  uint64_t *p10 = buf;
  uint64_t *p20 = buf + (uint32_t )8;
  uint64_t *p1 = p10;
  uint64_t *p21 = p10 + (uint32_t )4;
  p1[0] = v0;
  p1[1] = v1;
  p1[2] = v2;
  p1[3] = v3;
  p21[0] = v4;
  p21[1] = v5;
  p21[2] = v6;
  p21[3] = v7;
  uint64_t *p11 = p20;
  uint64_t *p2 = p20 + (uint32_t )4;
  p11[0] = v8;
  p11[1] = v9;
  p11[2] = v10;
  p11[3] = v11;
  p2[0] = v12;
  p2[1] = v13;
  p2[2] = v14;
  p2[3] = v15;
}

void
Hacl_Hash_Lib_Create_hupd64_80(
  uint64_t *buf,
  uint64_t v0,
  uint64_t v1,
  uint64_t v2,
  uint64_t v3,
  uint64_t v4,
  uint64_t v5,
  uint64_t v6,
  uint64_t v7,
  uint64_t v8,
  uint64_t v9,
  uint64_t v10,
  uint64_t v11,
  uint64_t v12,
  uint64_t v13,
  uint64_t v14,
  uint64_t v15,
  uint64_t v16,
  uint64_t v17,
  uint64_t v18,
  uint64_t v19,
  uint64_t v20,
  uint64_t v21,
  uint64_t v22,
  uint64_t v23,
  uint64_t v24,
  uint64_t v25,
  uint64_t v26,
  uint64_t v27,
  uint64_t v28,
  uint64_t v29,
  uint64_t v30,
  uint64_t v31,
  uint64_t v32,
  uint64_t v33,
  uint64_t v34,
  uint64_t v35,
  uint64_t v36,
  uint64_t v37,
  uint64_t v38,
  uint64_t v39,
  uint64_t v40,
  uint64_t v41,
  uint64_t v42,
  uint64_t v43,
  uint64_t v44,
  uint64_t v45,
  uint64_t v46,
  uint64_t v47,
  uint64_t v48,
  uint64_t v49,
  uint64_t v50,
  uint64_t v51,
  uint64_t v52,
  uint64_t v53,
  uint64_t v54,
  uint64_t v55,
  uint64_t v56,
  uint64_t v57,
  uint64_t v58,
  uint64_t v59,
  uint64_t v60,
  uint64_t v61,
  uint64_t v62,
  uint64_t v63,
  uint64_t v64,
  uint64_t v65,
  uint64_t v66,
  uint64_t v67,
  uint64_t v68,
  uint64_t v69,
  uint64_t v70,
  uint64_t v71,
  uint64_t v72,
  uint64_t v73,
  uint64_t v74,
  uint64_t v75,
  uint64_t v76,
  uint64_t v77,
  uint64_t v78,
  uint64_t v79
)
{
  uint64_t *p10 = buf;
  uint64_t *p20 = buf + (uint32_t )16;
  uint64_t *p3 = buf + (uint32_t )32;
  uint64_t *p4 = buf + (uint32_t )48;
  uint64_t *p5 = buf + (uint32_t )64;
  uint64_t *p11 = p10;
  uint64_t *p21 = p10 + (uint32_t )8;
  uint64_t *p12 = p11;
  uint64_t *p22 = p11 + (uint32_t )4;
  p12[0] = v0;
  p12[1] = v1;
  p12[2] = v2;
  p12[3] = v3;
  p22[0] = v4;
  p22[1] = v5;
  p22[2] = v6;
  p22[3] = v7;
  uint64_t *p13 = p21;
  uint64_t *p23 = p21 + (uint32_t )4;
  p13[0] = v8;
  p13[1] = v9;
  p13[2] = v10;
  p13[3] = v11;
  p23[0] = v12;
  p23[1] = v13;
  p23[2] = v14;
  p23[3] = v15;
  uint64_t *p14 = p20;
  uint64_t *p24 = p20 + (uint32_t )8;
  uint64_t *p15 = p14;
  uint64_t *p25 = p14 + (uint32_t )4;
  p15[0] = v16;
  p15[1] = v17;
  p15[2] = v18;
  p15[3] = v19;
  p25[0] = v20;
  p25[1] = v21;
  p25[2] = v22;
  p25[3] = v23;
  uint64_t *p16 = p24;
  uint64_t *p26 = p24 + (uint32_t )4;
  p16[0] = v24;
  p16[1] = v25;
  p16[2] = v26;
  p16[3] = v27;
  p26[0] = v28;
  p26[1] = v29;
  p26[2] = v30;
  p26[3] = v31;
  uint64_t *p17 = p3;
  uint64_t *p27 = p3 + (uint32_t )8;
  uint64_t *p18 = p17;
  uint64_t *p28 = p17 + (uint32_t )4;
  p18[0] = v32;
  p18[1] = v33;
  p18[2] = v34;
  p18[3] = v35;
  p28[0] = v36;
  p28[1] = v37;
  p28[2] = v38;
  p28[3] = v39;
  uint64_t *p19 = p27;
  uint64_t *p29 = p27 + (uint32_t )4;
  p19[0] = v40;
  p19[1] = v41;
  p19[2] = v42;
  p19[3] = v43;
  p29[0] = v44;
  p29[1] = v45;
  p29[2] = v46;
  p29[3] = v47;
  uint64_t *p110 = p4;
  uint64_t *p210 = p4 + (uint32_t )8;
  uint64_t *p111 = p110;
  uint64_t *p211 = p110 + (uint32_t )4;
  p111[0] = v48;
  p111[1] = v49;
  p111[2] = v50;
  p111[3] = v51;
  p211[0] = v52;
  p211[1] = v53;
  p211[2] = v54;
  p211[3] = v55;
  uint64_t *p112 = p210;
  uint64_t *p212 = p210 + (uint32_t )4;
  p112[0] = v56;
  p112[1] = v57;
  p112[2] = v58;
  p112[3] = v59;
  p212[0] = v60;
  p212[1] = v61;
  p212[2] = v62;
  p212[3] = v63;
  uint64_t *p113 = p5;
  uint64_t *p213 = p5 + (uint32_t )8;
  uint64_t *p1 = p113;
  uint64_t *p214 = p113 + (uint32_t )4;
  p1[0] = v64;
  p1[1] = v65;
  p1[2] = v66;
  p1[3] = v67;
  p214[0] = v68;
  p214[1] = v69;
  p214[2] = v70;
  p214[3] = v71;
  uint64_t *p114 = p213;
  uint64_t *p2 = p213 + (uint32_t )4;
  p114[0] = v72;
  p114[1] = v73;
  p114[2] = v74;
  p114[3] = v75;
  p2[0] = v76;
  p2[1] = v77;
  p2[2] = v78;
  p2[3] = v79;
}

