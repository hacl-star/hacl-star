#include "sha256_main_i.h"

void
__stdcall
sha256_main_i_DafnyMemcpy(
  uint8_t *dst,
  uint64_t dst_offset,
  uint8_t *src,
  uint64_t src_offset,
  uint64_t len
)
{
  uint64_t pos = (uint64_t)0;
  pos = (uint64_t)0;
  while (pos < len)
  {
    dst[(uint32_t)(dst_offset + pos)] = src[(uint32_t)(src_offset + pos)];
    pos = pos + (uint64_t)1;
  }
}

void __stdcall sha256_main_i_DafnyBzero(uint8_t *ptr, uint32_t offset, uint32_t len)
{
  uint32_t pos = (uint32_t)0;
  pos = (uint32_t)0;
  while (pos < len)
  {
    ptr[(uint32_t)(offset + pos)] = (uint8_t)0;
    pos = pos + (uint32_t)1;
  }
}

void __stdcall sha256_main_i_CopyUint64ToByteArray(uint8_t *a, uint64_t offset, uint64_t u)
{
  a[(uint32_t)offset] = (uint8_t)(u / (uint64_t)72057594037927936);
  a[(uint32_t)(offset + (uint64_t)1)] = (uint8_t)(u / (uint64_t)281474976710656 % (uint64_t)256);
  a[(uint32_t)(offset + (uint64_t)2)] = (uint8_t)(u / (uint64_t)1099511627776 % (uint64_t)256);
  a[(uint32_t)(offset + (uint64_t)3)] = (uint8_t)(u / (uint64_t)4294967296 % (uint64_t)256);
  a[(uint32_t)(offset + (uint64_t)4)] = (uint8_t)(u / (uint64_t)16777216 % (uint64_t)256);
  a[(uint32_t)(offset + (uint64_t)5)] = (uint8_t)(u / (uint64_t)65536 % (uint64_t)256);
  a[(uint32_t)(offset + (uint64_t)6)] = (uint8_t)(u / (uint64_t)256 % (uint64_t)256);
  a[(uint32_t)(offset + (uint64_t)7)] = (uint8_t)(u % (uint64_t)256);
}

void __stdcall sha256_main_i_CopyUint32Array(uint32_t *dst, uint32_t *src, uint64_t len)
{
  uint64_t pos = (uint64_t)0;
  pos = (uint64_t)0;
  while (pos < len)
  {
    dst[(uint32_t)pos] = src[(uint32_t)pos];
    pos = pos + (uint64_t)1;
  }
}

void
__stdcall
sha256_main_i_SHA256_DigestOneBlock(
  sha256_main_i_SHA256Context *ctx,
  uint32_t *W,
  uint8_t *ptr,
  uint64_t offset
)
{
  sha256_main_i_SHA256_ComputeInitialWs(ptr,
    (uint32_t)offset,
    W,
    (uint32_t)0,
    (uint32_t)1,
    (uint32_t)2,
    (uint32_t)3);
  sha256_main_i_SHA256_Compute64Steps(ctx->H,
    W,
    (uint32_t)0,
    (uint32_t)1,
    (uint32_t)2,
    (uint32_t)3,
    (uint32_t)4,
    (uint32_t)5,
    (uint32_t)6,
    (uint32_t)7,
    (uint32_t)8,
    (uint32_t)9,
    (uint32_t)10,
    (uint32_t)11,
    (uint32_t)12,
    (uint32_t)13,
    (uint32_t)14,
    (uint32_t)15,
    (uint32_t)16);
}

void
__stdcall
sha256_main_i_SHA256_BlockDataOrder(
  sha256_main_i_SHA256Context *ctx,
  uint8_t *ptr,
  uint64_t offset,
  uint64_t len
)
{
  uint64_t pos = (uint64_t)0;
  pos = (uint64_t)0;
  uint32_t *W;
  KRML_CHECK_SIZE((uint32_t)0, (uint32_t)(uint64_t)64);
  uint32_t buf[(uint32_t)(uint64_t)64];
  memset(buf, 0, (uint32_t)(uint64_t)64 * sizeof buf[0]);
  W = buf;
  while (pos < len)
  {
    sha256_main_i_SHA256_DigestOneBlock(ctx, W, ptr, offset + pos);
    pos = pos + (uint64_t)64;
  }
}

void
__stdcall
sha256_main_i_SHA256UpdateWhenNoUnprocessedBytes(
  sha256_main_i_SHA256Context *ctx,
  uint8_t *bytes,
  uint64_t offset,
  uint64_t len
)
{
  uint64_t num_blocks = (uint64_t)0;
  num_blocks = len / (uint64_t)64;
  uint32_t num_leftover_bytes = (uint32_t)0;
  num_leftover_bytes = (uint32_t)(len % (uint64_t)64);
  uint64_t num_block_bytes = (uint64_t)0;
  num_block_bytes = (uint64_t)64 * num_blocks;
  sha256_main_i_SHA256_BlockDataOrder(ctx, bytes, offset, num_block_bytes);
  if (num_leftover_bytes == (uint32_t)0)
  {
    ctx->num_total_bytes = ctx->num_total_bytes + num_block_bytes;
    return;
  }
  sha256_main_i_DafnyMemcpy(ctx->unprocessed_bytes,
    (uint64_t)0,
    bytes,
    offset + num_block_bytes,
    (uint64_t)num_leftover_bytes);
  ctx->num_unprocessed_bytes = num_leftover_bytes;
  ctx->num_total_bytes = ctx->num_total_bytes + num_block_bytes + (uint64_t)num_leftover_bytes;
}

void __stdcall sha256_main_i_SHA256_Init(sha256_main_i_SHA256Context *ctx)
{
  ctx->H[(uint32_t)(uint64_t)0] = (uint32_t)1779033703;
  ctx->H[(uint32_t)(uint64_t)1] = (uint32_t)3144134277;
  ctx->H[(uint32_t)(uint64_t)2] = (uint32_t)1013904242;
  ctx->H[(uint32_t)(uint64_t)3] = (uint32_t)2773480762;
  ctx->H[(uint32_t)(uint64_t)4] = (uint32_t)1359893119;
  ctx->H[(uint32_t)(uint64_t)5] = (uint32_t)2600822924;
  ctx->H[(uint32_t)(uint64_t)6] = (uint32_t)528734635;
  ctx->H[(uint32_t)(uint64_t)7] = (uint32_t)1541459225;
  ctx->num_unprocessed_bytes = (uint32_t)0;
  ctx->num_total_bytes = (uint64_t)0;
}

void
__stdcall
sha256_main_i_SHA256_Update(
  sha256_main_i_SHA256Context *ctx,
  uint8_t *bytes,
  uint64_t offset,
  uint64_t len
)
{
  if (len == (uint64_t)0)
    return;
  if (ctx->num_unprocessed_bytes == (uint32_t)0)
  {
    sha256_main_i_SHA256UpdateWhenNoUnprocessedBytes(ctx, bytes, offset, len);
    return;
  }
  uint64_t remaining_room = (uint64_t)0;
  remaining_room = (uint64_t)((uint32_t)64 - ctx->num_unprocessed_bytes);
  if (len < remaining_room)
  {
    sha256_main_i_DafnyMemcpy(ctx->unprocessed_bytes,
      (uint64_t)ctx->num_unprocessed_bytes,
      bytes,
      offset,
      len);
    ctx->num_unprocessed_bytes = ctx->num_unprocessed_bytes + (uint32_t)len;
    ctx->num_total_bytes = ctx->num_total_bytes + len;
    return;
  }
  sha256_main_i_DafnyMemcpy(ctx->unprocessed_bytes,
    (uint64_t)ctx->num_unprocessed_bytes,
    bytes,
    offset,
    remaining_room);
  sha256_main_i_SHA256_BlockDataOrder(ctx, ctx->unprocessed_bytes, (uint64_t)0, (uint64_t)64);
  ctx->num_total_bytes = ctx->num_total_bytes + remaining_room;
  ctx->num_unprocessed_bytes = (uint32_t)0;
  if (len == remaining_room)
    return;
  uint64_t new_offset = (uint64_t)0;
  new_offset = offset + remaining_room;
  uint64_t new_len = (uint64_t)0;
  new_len = len - remaining_room;
  sha256_main_i_SHA256UpdateWhenNoUnprocessedBytes(ctx, bytes, new_offset, new_len);
}

void __stdcall sha256_main_i_SHA256_Final(sha256_main_i_SHA256Context *ctx, uint32_t *digest)
{
  uint64_t message_bits = (uint64_t)0;
  message_bits = ctx->num_total_bytes * (uint64_t)8;
  ctx->unprocessed_bytes[(uint32_t)ctx->num_unprocessed_bytes] = (uint8_t)128;
  if (ctx->num_unprocessed_bytes <= (uint32_t)55)
  {
    sha256_main_i_DafnyBzero(ctx->unprocessed_bytes,
      ctx->num_unprocessed_bytes + (uint32_t)1,
      (uint32_t)55 - ctx->num_unprocessed_bytes);
    sha256_main_i_CopyUint64ToByteArray(ctx->unprocessed_bytes, (uint64_t)56, message_bits);
    sha256_main_i_SHA256_BlockDataOrder(ctx, ctx->unprocessed_bytes, (uint64_t)0, (uint64_t)64);
  }
  else
  {
    sha256_main_i_DafnyBzero(ctx->unprocessed_bytes,
      ctx->num_unprocessed_bytes + (uint32_t)1,
      (uint32_t)63 - ctx->num_unprocessed_bytes);
    sha256_main_i_SHA256_BlockDataOrder(ctx, ctx->unprocessed_bytes, (uint64_t)0, (uint64_t)64);
    sha256_main_i_DafnyBzero(ctx->unprocessed_bytes, (uint32_t)0, (uint32_t)56);
    sha256_main_i_CopyUint64ToByteArray(ctx->unprocessed_bytes, (uint64_t)56, message_bits);
    sha256_main_i_SHA256_BlockDataOrder(ctx, ctx->unprocessed_bytes, (uint64_t)0, (uint64_t)64);
  }
  sha256_main_i_CopyUint32Array(digest, ctx->H, (uint64_t)8);
}

void
__stdcall
sha256_main_i_SHA256_Complete(uint8_t *bytes, uint64_t offset, uint64_t len, uint32_t *digest)
{
  sha256_main_i_SHA256Context *ctx;
  sha256_main_i_SHA256Context
  buf0[1] =
    {
      (
        (sha256_main_i_SHA256Context){
          .H = (void *)0,
          .unprocessed_bytes = (void *)0,
          .num_unprocessed_bytes = (uint32_t)0,
          .num_total_bytes = (uint64_t)0
        }
      )
    };
  ctx = buf0;
  sha256_main_i_SHA256Context *_nw0 = ctx;
  KRML_CHECK_SIZE((uint32_t)0, (uint32_t)(uint64_t)8);
  uint32_t buf[(uint32_t)(uint64_t)8];
  memset(buf, 0, (uint32_t)(uint64_t)8 * sizeof buf[0]);
  _nw0->H = buf;
  KRML_CHECK_SIZE((uint8_t)0, (uint32_t)(uint64_t)64);
  uint8_t buf1[(uint32_t)(uint64_t)64];
  memset(buf1, 0, (uint32_t)(uint64_t)64 * sizeof buf1[0]);
  _nw0->unprocessed_bytes = buf1;
  _nw0->num_unprocessed_bytes = (uint32_t)0;
  sha256_main_i_SHA256_Init(ctx);
  sha256_main_i_SHA256_Update(ctx, bytes, offset, len);
  sha256_main_i_SHA256_Final(ctx, digest);
}

