/* hmac-streebog.c

   HMAC-Streebog message authentication code.

   Copyright (C) 2016 Dmitry Eremin-Solenikov
   Copyright (C) 2024 Niels Möller

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

#include "hmac.h"
#include "hmac-internal.h"

void
hmac_streebog512_set_key(struct hmac_streebog512_ctx *ctx,
			 size_t key_length, const uint8_t *key)
{
  _nettle_hmac_set_key (sizeof(ctx->outer), ctx->outer, ctx->inner, &ctx->state,
			ctx->state.block, &nettle_streebog512, key_length, key);
}

void
hmac_streebog512_update(struct hmac_streebog512_ctx *ctx,
			size_t length, const uint8_t *data)
{
  streebog512_update(&ctx->state, length, data);
}

void
hmac_streebog512_digest(struct hmac_streebog512_ctx *ctx,
			size_t length, uint8_t *digest)
{
  /* Using _NETTLE_HMAC_DIGEST doesn't work since
     STREEBOG512_DIGEST_SIZE == STREEBOG512_BLOCK_SIZE. */
  streebog512_digest (&ctx->state, STREEBOG512_DIGEST_SIZE, ctx->state.block);
  memcpy (&ctx->state, ctx->outer, sizeof (ctx->outer));
  streebog512_update (&ctx->state, STREEBOG512_DIGEST_SIZE, ctx->state.block);
  streebog512_digest (&ctx->state, length, digest);
  memcpy (&ctx->state, ctx->inner, sizeof (ctx->inner));
}

void
hmac_streebog256_set_key(struct hmac_streebog256_ctx *ctx,
			 size_t key_length, const uint8_t *key)
{
  _nettle_hmac_set_key (sizeof(ctx->outer), ctx->outer, ctx->inner, &ctx->state,
			ctx->state.block, &nettle_streebog256, key_length, key);
}

void
hmac_streebog256_digest(struct hmac_streebog256_ctx *ctx,
			size_t length, uint8_t *digest)
{
  streebog256_digest (&ctx->state, STREEBOG256_DIGEST_SIZE, ctx->state.block);
  ctx->state.index = STREEBOG256_DIGEST_SIZE;
  _NETTLE_HMAC_DIGEST (ctx->outer, ctx->inner, &ctx->state, streebog256_digest, length, digest);
}
