/* hmac-sha224.c

   HMAC-SHA224 message authentication code.

   Copyright (C) 2003, 2010 Niels Möller

   This file is part of GNU Nettle.

   GNU Nettle is free software: you can redistribute it and/or
   modify it under the terms of either:

     * the GNU Lesser General Public License as published by the Free
       Software Foundation; either version 3 of the License, or (at your
       option) any later version.

   or

     * the GNU General Public License as published by the Free
       Software Foundation; either version 2 of the License, or (at your
       option) any later version.

   or both in parallel, as here.

   GNU Nettle is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   General Public License for more details.

   You should have received copies of the GNU General Public License and
   the GNU Lesser General Public License along with this program.  If
   not, see http://www.gnu.org/licenses/.
*/

#if HAVE_CONFIG_H
# include "config.h"
#endif

#include <string.h>

#include "hmac.h"
#include "memxor.h"

#define IPAD 0x36
#define OPAD 0x5c

void
hmac_sha224_set_key(struct hmac_sha224_ctx *ctx,
		    size_t key_length, const uint8_t *key)
{
  uint8_t digest[SHA224_DIGEST_SIZE];

  sha224_init (&ctx->state);
  if (key_length > SHA224_BLOCK_SIZE)
    {
      sha224_update (&ctx->state, key_length, key);
      sha224_digest (&ctx->state, SHA224_DIGEST_SIZE, digest);
      key = digest;
      key_length = SHA224_DIGEST_SIZE;
    }

  memset (ctx->state.block, OPAD, SHA224_BLOCK_SIZE);
  memxor (ctx->state.block, key, key_length);
  sha224_update (&ctx->state, SHA224_BLOCK_SIZE, ctx->state.block);
  memcpy (ctx->outer, ctx->state.state, sizeof(ctx->outer));

  sha224_init (&ctx->state);
  memset (ctx->state.block, IPAD, SHA224_BLOCK_SIZE);
  memxor (ctx->state.block, key, key_length);
  sha224_update (&ctx->state, SHA224_BLOCK_SIZE, ctx->state.block);
  memcpy (ctx->inner, ctx->state.state, sizeof(ctx->outer));
}

void
hmac_sha224_digest(struct hmac_sha224_ctx *ctx,
		   size_t length, uint8_t *digest)
{
  uint8_t inner_digest[SHA224_DIGEST_SIZE];
  sha224_digest (&ctx->state, SHA224_DIGEST_SIZE, inner_digest);

  memcpy (ctx->state.state, ctx->outer, sizeof (ctx->state.state));
  ctx->state.count = 1;
  sha224_update (&ctx->state, SHA224_DIGEST_SIZE, inner_digest);
  sha224_digest (&ctx->state, length, digest);

  memcpy (ctx->state.state, ctx->inner, sizeof (ctx->state.state));
  ctx->state.count = 1;
}
