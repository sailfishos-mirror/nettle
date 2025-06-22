/* hmac-gosthash94.c

   HMAC-GOSTHASH94 message authentication code.

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
hmac_gosthash94_set_key(struct hmac_gosthash94_ctx *ctx,
			size_t key_length, const uint8_t *key)
{
  _nettle_hmac_set_key (sizeof(ctx->outer), ctx->outer, ctx->inner, &ctx->state,
			ctx->state.block, &nettle_gosthash94, key_length, key);
}

void
hmac_gosthash94_update(struct hmac_gosthash94_ctx *ctx,
		   size_t length, const uint8_t *data)
{
  gosthash94_update(&ctx->state, length, data);
}

void
hmac_gosthash94_digest(struct hmac_gosthash94_ctx *ctx,
		       uint8_t *digest)
{
  /* Needs a call to gosthash94_update, since
     GOSTHASH94_DIGEST_SIZE == GOSTHASH94_BLOCK_SIZE. */
  _NETTLE_HMAC_DIGEST_U (ctx->outer, ctx->inner, &ctx->state, gosthash94_digest,
			 gosthash94_update, digest);
}

void
hmac_gosthash94cp_set_key(struct hmac_gosthash94cp_ctx *ctx,
		    size_t key_length, const uint8_t *key)
{
  _nettle_hmac_set_key (sizeof(ctx->outer), ctx->outer, ctx->inner, &ctx->state,
			ctx->state.block, &nettle_gosthash94cp, key_length, key);
}

void
hmac_gosthash94cp_update(struct hmac_gosthash94cp_ctx *ctx,
		   size_t length, const uint8_t *data)
{
  gosthash94cp_update(&ctx->state, length, data);
}

void
hmac_gosthash94cp_digest(struct hmac_gosthash94cp_ctx *ctx,
			 uint8_t *digest)
{
  /* Needs a call to gosthash94cp_update, since
     GOSTHASH94CP_DIGEST_SIZE == GOSTHASH94CP_BLOCK_SIZE. */
  _NETTLE_HMAC_DIGEST_U (ctx->outer, ctx->inner, &ctx->state, gosthash94cp_digest,
			 gosthash94cp_update, digest);
}
