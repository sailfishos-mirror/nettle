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

#include <string.h>

#include "nettle-types.h"
#include "nettle-meta.h"

#define IPAD 0x36
#define OPAD 0x5c

void
_nettle_hmac_set_key (size_t state_size, void *outer, void *inner,
		      void *ctx, uint8_t *block,
		      const struct nettle_hash *hash,
		      size_t key_size, const uint8_t *key);

#define _NETTLE_HMAC_DIGEST(outer, inner, ctx, f, length, digest) do {	\
    memcpy ((ctx), (outer), sizeof (outer));				\
    f ((ctx), (length), (digest));					\
    memcpy ((ctx), (inner), sizeof ((inner)));				\
  } while (0)

#endif /* NETTLE_HMAC_INTERNAL_H_INCLUDED */
