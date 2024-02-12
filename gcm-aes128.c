/* gcm-aes128.c

   Galois counter mode using AES128 as the underlying cipher.

   Copyright (C) 2011, 2014 Niels Möller

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

#include <assert.h>

#include "gcm.h"
#include "gcm-internal.h"

void
gcm_aes128_set_key(struct gcm_aes128_ctx *ctx, const uint8_t *key)
{
  GCM_SET_KEY(ctx, aes128_set_encrypt_key, aes128_encrypt, key);
}

void
gcm_aes128_set_iv (struct gcm_aes128_ctx *ctx,
		      size_t length, const uint8_t *iv)
{
  GCM_SET_IV (ctx, length, iv);
}

void
gcm_aes128_update (struct gcm_aes128_ctx *ctx,
		   size_t length, const uint8_t *data)
{
  GCM_UPDATE (ctx, length, data);
}

void
gcm_aes128_encrypt(struct gcm_aes128_ctx *ctx,
		   size_t length, uint8_t *dst, const uint8_t *src)
{
  size_t done = _gcm_aes_encrypt (&ctx->key, _AES128_ROUNDS, length, dst, src);
  GCM_ENCRYPT(ctx, aes128_encrypt, length - done, dst + done, src + done);
}

void
gcm_aes128_decrypt(struct gcm_aes128_ctx *ctx,
		   size_t length, uint8_t *dst, const uint8_t *src)
{
  GCM_DECRYPT(ctx, aes128_encrypt, length, dst, src);
}

void
gcm_aes128_digest(struct gcm_aes128_ctx *ctx,
		  size_t length, uint8_t *digest)
{
  GCM_DIGEST(ctx, aes128_encrypt, length, digest);
}
