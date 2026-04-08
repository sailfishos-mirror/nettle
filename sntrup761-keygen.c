/* sntrup761-keygen.c

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
Small_random (sntrup761_R3_t out, void *random_ctx, nettle_random_func * random)
{
  int i;

  for (i = 0; i < SNTRUP761_P; ++i)
    out[i] = (((_sntrup_urandom32 (random_ctx, random) & 0x3fffffff) * 3) >> 30) - 1;
}

static int16_t
Fq_recip (int16_t a1)
{
  int i = 1;
  int16_t ai = a1;

  while (i < SNTRUP761_Q - 2)
    {
      ai = _sntrup761_mod_q (a1 * (int32_t) ai);
      i += 1;
    }
  return ai;
}

/* return -1 if x<0; otherwise return 0 */
static int
int16_t_negative_mask (int16_t x)
{
  uint16_t u = x;
  u >>= 15;
  return -(int) u;
  /* alternative with gcc -fwrapv: */
  /* x>>15 compiles to CPU's arithmetic right shift */
}

/* returns 0 if recip succeeded; else -1 */
static int
R3_recip (sntrup761_R3_t out, const sntrup761_R3_t in)
{
  int8_t f[SNTRUP761_P + 1], g[SNTRUP761_P + 1], v[SNTRUP761_P + 1], r[SNTRUP761_P + 1];
  int i, loop, delta;
  int sign, swap, t;

  for (i = 0; i < SNTRUP761_P + 1; ++i)
    v[i] = 0;
  for (i = 0; i < SNTRUP761_P + 1; ++i)
    r[i] = 0;
  r[0] = 1;
  for (i = 0; i < SNTRUP761_P; ++i)
    f[i] = 0;
  f[0] = 1;
  f[SNTRUP761_P - 1] = f[SNTRUP761_P] = -1;
  for (i = 0; i < SNTRUP761_P; ++i)
    g[SNTRUP761_P - 1 - i] = in[i];
  g[SNTRUP761_P] = 0;

  delta = 1;

  for (loop = 0; loop < 2 * SNTRUP761_P - 1; ++loop)
    {
      for (i = SNTRUP761_P; i > 0; --i)
	v[i] = v[i - 1];
      v[0] = 0;

      sign = -g[0] * f[0];
      swap = int16_t_negative_mask (-delta) & int16_t_nonzero_mask (g[0]);
      delta ^= swap & (delta ^ -delta);
      delta += 1;

      for (i = 0; i < SNTRUP761_P + 1; ++i)
	{
	  t = swap & (f[i] ^ g[i]);
	  f[i] ^= t;
	  g[i] ^= t;
	  t = swap & (v[i] ^ r[i]);
	  v[i] ^= t;
	  r[i] ^= t;
	}

      for (i = 0; i < SNTRUP761_P + 1; ++i)
	g[i] = _sntrup_mod_3 (g[i] + sign * f[i]);
      for (i = 0; i < SNTRUP761_P + 1; ++i)
	r[i] = _sntrup_mod_3 (r[i] + sign * v[i]);

      for (i = 0; i < SNTRUP761_P; ++i)
	g[i] = g[i + 1];
      g[SNTRUP761_P] = 0;
    }

  sign = f[0];
  for (i = 0; i < SNTRUP761_P; ++i)
    out[i] = sign * v[SNTRUP761_P - 1 - i];

  return int16_t_nonzero_mask (delta);
}

/* out = 1/(3*in) in Rq */
/* returns 0 if recip succeeded; else -1 */
static int
Rq_recip3 (sntrup761_Rq_t out, const sntrup761_R3_t in)
{
  int16_t f[SNTRUP761_P + 1], g[SNTRUP761_P + 1], v[SNTRUP761_P + 1], r[SNTRUP761_P + 1];
  int i, loop, delta;
  int swap, t;
  int32_t f0, g0;
  int16_t scale;

  for (i = 0; i < SNTRUP761_P + 1; ++i)
    v[i] = 0;
  for (i = 0; i < SNTRUP761_P + 1; ++i)
    r[i] = 0;
  r[0] = Fq_recip (3);
  for (i = 0; i < SNTRUP761_P; ++i)
    f[i] = 0;
  f[0] = 1;
  f[SNTRUP761_P - 1] = f[SNTRUP761_P] = -1;
  for (i = 0; i < SNTRUP761_P; ++i)
    g[SNTRUP761_P - 1 - i] = in[i];
  g[SNTRUP761_P] = 0;

  delta = 1;

  for (loop = 0; loop < 2 * SNTRUP761_P - 1; ++loop)
    {
      for (i = SNTRUP761_P; i > 0; --i)
	v[i] = v[i - 1];
      v[0] = 0;

      swap = int16_t_negative_mask (-delta) & int16_t_nonzero_mask (g[0]);
      delta ^= swap & (delta ^ -delta);
      delta += 1;

      for (i = 0; i < SNTRUP761_P + 1; ++i)
	{
	  t = swap & (f[i] ^ g[i]);
	  f[i] ^= t;
	  g[i] ^= t;
	  t = swap & (v[i] ^ r[i]);
	  v[i] ^= t;
	  r[i] ^= t;
	}

      f0 = f[0];
      g0 = g[0];
      for (i = 0; i < SNTRUP761_P + 1; ++i)
	g[i] = _sntrup761_mod_q (f0 * g[i] - g0 * f[i]);
      for (i = 0; i < SNTRUP761_P + 1; ++i)
	r[i] = _sntrup761_mod_q (f0 * r[i] - g0 * v[i]);

      for (i = 0; i < SNTRUP761_P; ++i)
	g[i] = g[i + 1];
      g[SNTRUP761_P] = 0;
    }

  scale = Fq_recip (f[0]);
  for (i = 0; i < SNTRUP761_P; ++i)
    out[i] = _sntrup761_mod_q (scale * (int32_t) v[SNTRUP761_P - 1 - i]);

  return int16_t_nonzero_mask (delta);
}

static void
Rq_encode (uint8_t *s, const sntrup761_Rq_t r)
{
  uint16_t R[SNTRUP761_P];
  uint16_t M = SNTRUP761_Q;
  int i;

  for (i = 0; i < SNTRUP761_P; ++i)
    R[i] = r[i] + SNTRUP761_Q12;
  _sntrup_encode (s, R, M, M, SNTRUP761_P);
}

/* h,(f,ginv) = KeyGen() */
static void
KeyGen (sntrup761_Rq_t h, sntrup761_R3_t f, sntrup761_R3_t ginv,
	void *random_ctx, nettle_random_func * random)
{
  sntrup761_R3_t g;
  sntrup761_Rq_t finv;

  for (;;)
    {
      Small_random (g, random_ctx, random);
      if (R3_recip (ginv, g) == 0)
	break;
    }
  _sntrup761_short_random (f, random_ctx, random);
  Rq_recip3 (finv, f);		/* always works */
  _sntrup761_Rq_mult_small (h, finv, g);
}

/* pk,sk = ZKeyGen() */
static void
ZKeyGen (uint8_t *pk, uint8_t *sk, void *random_ctx,
	 nettle_random_func * random)
{
  sntrup761_Rq_t h;
  sntrup761_R3_t f, v;

  KeyGen (h, f, v, random_ctx, random);
  Rq_encode (pk, h);
  _sntrup761_small_encode (sk, f);
  sk += SNTRUP761_R3_SIZE;
  _sntrup761_small_encode (sk, v);
}

/* pk,sk = KEM_KeyGen() */
void
sntrup761_generate_keypair (uint8_t *pk, uint8_t *sk, void *random_ctx,
			    nettle_random_func * random)
{
  int i;

  ZKeyGen (pk, sk, random_ctx, random);
  sk += 2*SNTRUP761_R3_SIZE;
  for (i = 0; i < SNTRUP761_PUBLIC_KEY_SIZE; ++i)
    *sk++ = pk[i];
  random (random_ctx, SNTRUP761_R3_SIZE, sk);
  sk += SNTRUP761_R3_SIZE;
  _sntrup_hash_prefix (sk, 4, pk, SNTRUP761_PUBLIC_KEY_SIZE);
}
