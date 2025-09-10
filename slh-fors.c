/* slh-fors.c

   Forest of Random Subsets, part of SLH-DSA (FIPS 205)

   Copyright (C) 2025 Niels Möller

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

#include "bswap-internal.h"
#include "sha3.h"
#include "slh-dsa-internal.h"

/* TODO: Like wots_gen, take hash ctx, secret seed (+ keypair) as separate arguments? */
void
_fors_gen (const struct slh_merkle_ctx_secret *ctx,
	   unsigned idx, uint8_t *sk, uint8_t *leaf)
{
  struct slh_address_hash ah =
    {
      bswap32_if_le (SLH_FORS_PRF),
      bswap32_if_le (ctx->pub.keypair),
      0,
      bswap32_if_le (idx),
    };

  ctx->pub.ctx.hash->secret (ctx->pub.ctx.tree, &ah, ctx->secret_seed, sk);

  ah.type = bswap32_if_le (SLH_FORS_TREE);
  ctx->pub.ctx.hash->secret (ctx->pub.ctx.tree, &ah, ctx->secret_seed, leaf);
}

static void
fors_leaf (const struct slh_merkle_ctx_secret *ctx, unsigned idx, uint8_t *out)
{
  _fors_gen (ctx, idx, out, out);
}

static void
fors_node (const struct slh_merkle_ctx_public *ctx, unsigned height, unsigned index,
	   const uint8_t *left, const uint8_t *right, uint8_t *out)
{
  struct slh_address_hash ah =
    {
      bswap32_if_le (SLH_FORS_TREE),
      bswap32_if_le (ctx->keypair),
      bswap32_if_le (height),
      bswap32_if_le (index),
    };
  ctx->ctx.hash->node (ctx->ctx.tree, &ah, left, right, out);
}

static void
fors_sign_one (const struct slh_merkle_ctx_secret *ctx, unsigned a,
	       unsigned idx, uint8_t *signature)
{
  uint8_t hash[_SLH_DSA_128_SIZE];

  _fors_gen (ctx, idx, signature, hash);

  _merkle_sign (ctx, fors_leaf, fors_node, a, idx,
		signature + _SLH_DSA_128_SIZE);
  _merkle_verify (&ctx->pub, fors_node, a, idx, signature + _SLH_DSA_128_SIZE, hash);

  ctx->pub.ctx.hash->update (ctx->pub.ctx.scratch, _SLH_DSA_128_SIZE, hash);
}

void
_fors_sign (const struct slh_merkle_ctx_secret *ctx,
	    const struct slh_fors_params *fors,
	    const uint8_t *msg, uint8_t *signature, uint8_t *pub)
{
  struct slh_address_hash ah =
    {
      bswap32_if_le (SLH_FORS_ROOTS),
      bswap32_if_le (ctx->pub.keypair),
      0, 0,
    };
  unsigned i, w, bits;
  unsigned mask = (1 << fors->a) - 1;

  ctx->pub.ctx.hash->start (ctx->pub.ctx.tree, ctx->pub.ctx.scratch, &ah);

  for (i = w = bits = 0; i < fors->k; i++, signature += (fors->a + 1) * _SLH_DSA_128_SIZE)
    {
      for (; bits < fors->a; bits += 8)
	w = (w << 8) | *msg++;
      bits -= fors->a;

      fors_sign_one (ctx, fors->a, (i << fors->a) + ((w >> bits) & mask), signature);
     }

  ctx->pub.ctx.hash->digest (ctx->pub.ctx.scratch, pub);
}

static void
fors_verify_one (const struct slh_merkle_ctx_public *ctx, unsigned a,
		 unsigned idx, const uint8_t *signature)
{
  uint8_t root[_SLH_DSA_128_SIZE];
  struct slh_address_hash ah =
    {
      bswap32_if_le (SLH_FORS_TREE),
      bswap32_if_le (ctx->keypair),
      0,
      bswap32_if_le (idx),
    };

  ctx->ctx.hash->secret (ctx->ctx.tree, &ah, signature, root);
  _merkle_verify (ctx, fors_node, a, idx, signature + _SLH_DSA_128_SIZE, root);

  ctx->ctx.hash->update (ctx->ctx.scratch, _SLH_DSA_128_SIZE, root);
}

void
_fors_verify (const struct slh_merkle_ctx_public *ctx,
	      const struct slh_fors_params *fors,
	      const uint8_t *msg, const uint8_t *signature, uint8_t *pub)
{
  struct slh_address_hash ah =
    {
      bswap32_if_le (SLH_FORS_ROOTS),
      bswap32_if_le (ctx->keypair),
      0, 0,
    };
  unsigned i, w, bits;
  unsigned mask = (1 << fors->a) - 1;

  ctx->ctx.hash->start (ctx->ctx.tree, ctx->ctx.scratch, &ah);

  for (i = w = bits = 0; i < fors->k; i++, signature += (fors->a + 1) * _SLH_DSA_128_SIZE)
    {
      for (; bits < fors->a; bits += 8)
	w = (w << 8) | *msg++;
      bits -= fors->a;

      fors_verify_one (ctx, fors->a, (i << fors->a) + ((w >> bits) & mask), signature);
    }
  ctx->ctx.hash->digest (ctx->ctx.scratch, pub);
}
