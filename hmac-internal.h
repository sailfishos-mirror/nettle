/* hmac-internal.h

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

#ifndef NETTLE_HMAC_INTERNAL_H_INCLUDED
#define NETTLE_HMAC_INTERNAL_H_INCLUDED

#include "nettle-types.h"
#include "nettle-meta.h"

#define IPAD 0x36
#define OPAD 0x5c

/* Initialize BLOCK from KEY, with KEY_SIZE <= BLOCK_SIZE. If KEY ==
   NULL, key is already written at the start of the block. */
void _nettle_hmac_outer_block (size_t block_size, uint8_t *block, size_t key_size, const uint8_t *key);

void
_nettle_hmac_outer_block_digest (size_t block_size, uint8_t *block, size_t key_size);

void _nettle_hmac_inner_block (size_t block_size, uint8_t *block);

typedef void compress_func (void *state, const uint8_t *block);

void
_nettle_hmac_set_key(size_t state_size, void *outer, void *inner,
		     void *ctx, uint8_t *block,
		     const struct nettle_hash *hash,
		     compress_func *compress,
		     size_t key_length, const uint8_t *key);

#endif /* NETTLE_HMAC_INTERNAL_H_INCLUDED */
