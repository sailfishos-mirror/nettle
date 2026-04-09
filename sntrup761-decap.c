/* sntrup761-decap.c

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

/* 0 if Weightw_is(r), else -1 */
static int
Weightw_mask (sntrup761_R3_t r)
{
  int weight = 0;
  int i;

  for (i = 0; i < SNTRUP761_P; ++i)
    weight += r[i] & 1;
  return uint16_nonzero_mask (weight - SNTRUP761_W);
}

/* R3_fromR(R_fromRq(r)) */
static void
R3_fromRq (sntrup761_R3_t out, const sntrup761_Rq_t r)
{
  int i;
  for (i = 0; i < SNTRUP761_P; ++i)
    out[i] = _sntrup_mod_3 (r[i]);
}

/* h = f*g in the ring R3. Allows non-canonical input, since decoding
   can produce coefficients with the value 2. */
static void
R3_mult (sntrup761_R3_t h, const sntrup761_R3_t f, const sntrup761_R3_t g)
{
  int16_t fg[SNTRUP761_P + SNTRUP761_P - 1];
  int i, j;

  for (i = 0; i < SNTRUP761_P; ++i)
    {
      int16_t result;
      for (result = 0, j = 0; j <= i; ++j)
	result += f[j] * g[i - j];
      fg[i] = result;
    }
  for (i = SNTRUP761_P; i < SNTRUP761_P + SNTRUP761_P - 1; ++i)
    {
      int16_t result;
      for (result = 0, j = i - SNTRUP761_P + 1; j < SNTRUP761_P; ++j)
	result += f[j] * g[i - j];
      fg[i] = result;
    }

  for (i = SNTRUP761_P + SNTRUP761_P - 2; i >= SNTRUP761_P; --i)
    {
      fg[i - SNTRUP761_P] += + fg[i];
      fg[i - SNTRUP761_P + 1] += fg[i];
    }

  for (i = 0; i < SNTRUP761_P; ++i)
    h[i] = _sntrup_mod_3(fg[i]);
}

/* h = 3f in Rq */
static void
Rq_mult3 (sntrup761_Rq_t h, const sntrup761_Rq_t f)
{
  int i;

  for (i = 0; i < SNTRUP761_P; ++i)
    h[i] = _sntrup761_mod_q (3 * f[i]);
}

/* r = Decrypt(c,(f,ginv)) */
static void
Decrypt (sntrup761_R3_t r, const sntrup761_Rq_t c,
	 const sntrup761_R3_t f, const sntrup761_R3_t ginv)
{
  sntrup761_Rq_t cf, cf3;
  sntrup761_R3_t e, ev;
  int mask;
  int i;

  _sntrup761_Rq_mult_small (cf, c, f);
  Rq_mult3 (cf3, cf);
  R3_fromRq (e, cf3);
  /* FIXME: Non-canonical values for the ginv coeffients will violate
     bounds for accumulation and reduction. */
  R3_mult (ev, e, ginv);

  mask = Weightw_mask (ev);	/* 0 if weight SNTRUP761_W, else -1 */
  for (i = 0; i < SNTRUP761_W; ++i)
    r[i] = ((ev[i] ^ 1) & ~mask) ^ 1;
  for (i = SNTRUP761_W; i < SNTRUP761_P; ++i)
    r[i] = ev[i] & ~mask;
}

/* Decodes a polynomial with coefficients supposedly all being in {-1,
   0, 1}. But no error handling, so for invalid inputs, resulting
   coefficients are in {-1, 0, 1, 2 }. */
static void
Small_decode (sntrup761_R3_t f, const uint8_t *s)
{
  int8_t *p;
  int i;

  for (i = 0, p = f; i < SNTRUP761_P / 4; ++i)
    {
      uint8_t x = *s++;
      *p++ = ((int8_t) (x & 3)) - 1;
      x >>= 2;
      *p++ = ((int8_t) (x & 3)) - 1;
      x >>= 2;
      *p++ = ((int8_t) (x & 3)) - 1;
      x >>= 2;
      *p++ = ((int8_t) (x & 3)) - 1;
    }
  *p = ((int8_t) (*s & 3)) - 1;
}

static void
Rounded_decode (sntrup761_Rq_t r, const uint8_t *s)
{
  uint16_t R[SNTRUP761_P];
  uint32_t M = (SNTRUP761_Q + 2) / 3;
  int i;

  _sntrup_decode (R, s, M, M, SNTRUP761_P);
  for (i = 0; i < SNTRUP761_P; ++i)
    r[i] = R[i] * 3 - SNTRUP761_Q12;
}

/* r = ZDecrypt(C,sk) */
static void
ZDecrypt (sntrup761_R3_t r, const uint8_t *c_enc, const uint8_t *sk)
{
  sntrup761_R3_t f, v;
  sntrup761_Rq_t c;

  Small_decode (f, sk);
  sk += SNTRUP761_R3_SIZE;
  Small_decode (v, sk);
  Rounded_decode (c, c_enc);
  Decrypt (r, c, f, v);
}

static int
Ciphertexts_diff_mask (const uint8_t *c, const uint8_t *c2)
{
  uint16_t differentbits = 0;
  int len = SNTRUP761_CIPHER_SIZE;

  while (len-- > 0)
    differentbits |= (*c++) ^ (*c2++);
  return (1 & ((differentbits - 1) >> 8)) - 1;
}

/* k = Decap(c,sk) */
void
sntrup761_decap (uint8_t *k, const uint8_t *c, const uint8_t *sk)
{
  const uint8_t *pk = sk + 2*SNTRUP761_R3_SIZE;
  const uint8_t *rho = pk + SNTRUP761_PUBLIC_KEY_SIZE;
  const uint8_t *cache = rho + SNTRUP761_R3_SIZE;
  sntrup761_R3_t r;
  uint8_t r_enc[SNTRUP761_R3_SIZE];
  uint8_t cnew[SNTRUP761_CIPHER_SIZE];
  int mask;
  int i;

  ZDecrypt (r, c, sk);
  _sntrup761_encap_internal (cnew, r_enc, r, pk, cache);
  mask = Ciphertexts_diff_mask (c, cnew);
  for (i = 0; i < SNTRUP761_R3_SIZE; ++i)
    r_enc[i] ^= mask & (r_enc[i] ^ rho[i]);
  _sntrup_hash_session (k, 1 + mask, r_enc, c);
}
