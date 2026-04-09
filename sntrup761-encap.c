/* sntrup761-encap.c

   Copyright (C) 2023 Simon Josefsson
   Copyright (C) 2026 Niels Möller

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

/*
 * Derived from public domain source, written by (in alphabetical order):
 * - Daniel J. Bernstein
 * - Chitchanok Chuengsatiansup
 * - Tanja Lange
 * - Christine van Vredendaal
 */

#if HAVE_CONFIG_H
#include "config.h"
#endif

#include "sntrup.h"
#include "sntrup-internal.h"

static void
Round (sntrup761_Rq_t out, const sntrup761_Rq_t a)
{
  int i;
  for (i = 0; i < SNTRUP761_P; ++i)
    out[i] = a[i] - _sntrup_mod_3 (a[i]);
}

static void
Rq_decode (sntrup761_Rq_t r, const uint8_t *s)
{
  uint16_t R[SNTRUP761_P], M[SNTRUP761_P];
  int i;

  for (i = 0; i < SNTRUP761_P; ++i)
    M[i] = SNTRUP761_Q;
  _sntrup_decode (R, s, M, SNTRUP761_P);
  for (i = 0; i < SNTRUP761_P; ++i)
    r[i] = ((int16_t) R[i]) - SNTRUP761_Q12;
}

static void
Rounded_encode (uint8_t *s, const sntrup761_Rq_t r)
{
  uint16_t R[SNTRUP761_P];
  uint16_t M = (SNTRUP761_Q + 2) / 3;
  int i;

  for (i = 0; i < SNTRUP761_P; ++i)
    R[i] = ((r[i] + SNTRUP761_Q12) * 10923) >> 15;
  _sntrup_encode (s, R, M, M, SNTRUP761_P);
}

/* C = ZEncrypt(r,pk) */
static void
ZEncrypt (uint8_t *c_enc, const sntrup761_R3_t r, const uint8_t *pk)
{
  sntrup761_Rq_t hr;
  sntrup761_Rq_t h, c;
  Rq_decode (h, pk);
  _sntrup761_Rq_mult_small (hr, h, r);
  /* FIXME: Both rounding and encoding includes a division by 3.
     Merge, to divide only once. */
  Round (c, hr);
  Rounded_encode (c_enc, c);
}

/* c,r_enc = Hide(r,pk,cache); cache is Hash4(pk) */
void
_sntrup761_encap_internal (uint8_t *c, uint8_t *r_enc, const sntrup761_R3_t r,
			   const uint8_t *pk, const uint8_t *cache)
{
  _sntrup761_small_encode (r_enc, r);
  ZEncrypt (c, r, pk);
  _sntrup_hash_confirm (c + SNTRUP761_CIPHER_SIZE - SNTRUP_HASH_SIZE, r_enc, cache);
}

/* c,k = Encap(pk) */
void
sntrup761_encap (uint8_t *c, uint8_t *k, const uint8_t *pk,
		 void *random_ctx, nettle_random_func * random)
{
  sntrup761_R3_t r;
  uint8_t r_enc[SNTRUP761_R3_SIZE];
  uint8_t cache[SNTRUP_HASH_SIZE];

  _sntrup_hash_prefix (cache, 4, pk, SNTRUP761_PUBLIC_KEY_SIZE);
  _sntrup761_short_random (r, random_ctx, random);
  _sntrup761_encap_internal (c, r_enc, r, pk, cache);
  _sntrup_hash_session (k, 1, r_enc, c);
}
