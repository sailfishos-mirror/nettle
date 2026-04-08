/* sntrup761.c

   Copyright (C) 2023 Simon Josefsson

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

#if WITH_EXTRA_ASSERTS
# include <assert.h>
# define assert_maybe(x) assert(x)
#else
# define assert_maybe(x) ((void)(x))
#endif

#include <string.h>

#include "sntrup.h"
#include "sntrup-internal.h"

#define uint32_MINMAX(a,b) \
do { \
  uint64_t d = (uint64_t)b - (uint64_t)a; \
  uint32_t masked_d = (d >> 32) & d; \
  a += masked_d; \
  b -= masked_d; \
} while(0)

/* Based on supercop-20201130/crypto_sort/int32/portable4/sort.c, but
   using uint32_t rather than int32_t. */
static void
crypto_sort_uint32 (uint32_t *x, size_t n)
{
  size_t top, p, q, r, i, j;

  if (n < 2)
    return;
  top = 1;
  while (top < n - top)
    top += top;

  for (p = top; p >= 1; p >>= 1)
    {
      i = 0;
      while (i + 2 * p <= n)
	{
	  for (j = i; j < i + p; ++j)
	    uint32_MINMAX (x[j], x[j + p]);
	  i += 2 * p;
	}
      for (j = i; j < n - p; ++j)
	uint32_MINMAX (x[j], x[j + p]);

      i = 0;
      j = 0;
      for (q = top; q > p; q >>= 1)
	{
	  if (j != i)
	    for (;;)
	      {
		if (j == n - q)
		  goto done;
		uint32_t a = x[j + p];
		for (r = q; r > p; r >>= 1)
		  uint32_MINMAX (a, x[j + r]);
		x[j + p] = a;
		++j;
		if (j == i + p)
		  {
		    i += 2 * p;
		    break;
		  }
	      }
	  while (i + p <= n - q)
	    {
	      for (j = i; j < i + p; ++j)
		{
		  uint32_t a = x[j + p];
		  for (r = q; r > p; r >>= 1)
		    uint32_MINMAX (a, x[j + r]);
		  x[j + p] = a;
		}
	      i += 2 * p;
	    }
	  /* now i + p > n - q */
	  j = i;
	  while (j < n - q)
	    {
	      uint32_t a = x[j + p];
	      for (r = q; r > p; r >>= 1)
		uint32_MINMAX (a, x[j + r]);
	      x[j + p] = a;
	      ++j;
	    }

	done:;
	}
    }
}

/* from supercop-20201130/crypto_kem/sntrup761/ref/uint32.c */

/*
CPU division instruction typically takes time depending on x.
This software is designed to take time independent of x.
Time still varies depending on m; user must ensure that m is constant.
Time also varies on CPUs where multiplication is variable-time.
There could be more CPU issues.
There could also be compiler issues.
*/

static void
uint32_divmod_uint14 (uint32_t * q, uint16_t * r, uint32_t x, uint16_t m)
{
  uint32_t v = 0x80000000;
  uint32_t qpart;
  uint32_t mask;

  v /= m;

  /* caller guarantees m > 0 */
  /* caller guarantees m < 16384 */
  /* vm <= 2^31 <= vm+m-1 */
  /* xvm <= 2^31 x <= xvm+x(m-1) */

  *q = 0;

  qpart = (x * (uint64_t) v) >> 31;
  /* 2^31 qpart <= xv <= 2^31 qpart + 2^31-1 */
  /* 2^31 qpart m <= xvm <= 2^31 qpart m + (2^31-1)m */
  /* 2^31 qpart m <= 2^31 x <= 2^31 qpart m + (2^31-1)m + x(m-1) */
  /* 0 <= 2^31 newx <= (2^31-1)m + x(m-1) */
  /* 0 <= newx <= (1-1/2^31)m + x(m-1)/2^31 */
  /* 0 <= newx <= (1-1/2^31)(2^14-1) + (2^32-1)((2^14-1)-1)/2^31 */

  x -= qpart * m;
  *q += qpart;
  /* x <= 49146 */

  qpart = (x * (uint64_t) v) >> 31;
  /* 0 <= newx <= (1-1/2^31)m + x(m-1)/2^31 */
  /* 0 <= newx <= m + 49146(2^14-1)/2^31 */
  /* 0 <= newx <= m + 0.4 */
  /* 0 <= newx <= m */

  x -= qpart * m;
  *q += qpart;
  /* x <= m */

  x -= m;
  *q += 1;
  mask = -(x >> 31);
  x += mask & (uint32_t) m;
  *q += mask;
  /* x < m */

  *r = x;
}


static uint16_t
uint32_mod_uint14 (uint32_t x, uint16_t m)
{
  uint32_t q;
  uint16_t r;
  uint32_divmod_uint14 (&q, &r, x, m);
  return r;
}

/* from supercop-20201130/crypto_kem/sntrup761/ref/paramsmenu.h */
#define Rounded_bytes 1007

/* from supercop-20201130/crypto_kem/sntrup761/ref/Decode.h */

/* Decode(R,s,M,len) */
/* assumes 0 < M[i] < 16384 */
/* produces 0 <= R[i] < M[i] */

/* from supercop-20201130/crypto_kem/sntrup761/ref/Decode.c */

void
_sntrup_decode (uint16_t * out, const uint8_t *S, const uint16_t * M,
		size_t len)
{
  if (len == 1)
    {
      if (M[0] == 1)
	*out = 0;
      else if (M[0] <= 256)
	*out = uint32_mod_uint14 (S[0], M[0]);
      else
	*out = uint32_mod_uint14 (S[0] + (((uint16_t) S[1]) << 8), M[0]);
    }
  if (len > 1)
    {
      uint16_t R2[(len + 1) / 2];
      uint16_t M2[(len + 1) / 2];
      uint16_t bottomr[len / 2];
      uint32_t bottomt[len / 2];
      size_t i;
      for (i = 0; i < len - 1; i += 2)
	{
	  uint32_t m = M[i] * (uint32_t) M[i + 1];
	  if (m > 256 * 16383)
	    {
	      bottomt[i / 2] = 256 * 256;
	      bottomr[i / 2] = S[0] + 256 * S[1];
	      S += 2;
	      M2[i / 2] = (((m + 255) >> 8) + 255) >> 8;
	    }
	  else if (m >= 16384)
	    {
	      bottomt[i / 2] = 256;
	      bottomr[i / 2] = S[0];
	      S += 1;
	      M2[i / 2] = (m + 255) >> 8;
	    }
	  else
	    {
	      bottomt[i / 2] = 1;
	      bottomr[i / 2] = 0;
	      M2[i / 2] = m;
	    }
	}
      if (i < len)
	M2[i / 2] = M[i];
      _sntrup_decode (R2, S, M2, (len + 1) / 2);
      for (i = 0; i < len - 1; i += 2)
	{
	  uint32_t r = bottomr[i / 2];
	  uint32_t r1;
	  uint16_t r0;
	  r += bottomt[i / 2] * R2[i / 2];
	  uint32_divmod_uint14 (&r1, &r0, r, M[i]);
	  r1 = uint32_mod_uint14 (r1, M[i + 1]);	/* only needed for invalid inputs */
	  *out++ = r0;
	  *out++ = r1;
	}
      if (i < len)
	*out++ = R2[i / 2];
    }
}

/* from supercop-20201130/crypto_kem/sntrup761/ref/Encode.h */

/* Encode(s,R,M,len) */
/* assumes 0 <= R[i] < M[i] < 16384 */

/* from supercop-20201130/crypto_kem/sntrup761/ref/Encode.c */

/* 0 <= R[i] < M0 < 16384 for 0 <= i < len - 1,
   0 <= R[len -l] < M1 < 16384
 */
void
_sntrup_encode (uint8_t *out, const uint16_t * R, uint32_t M0, uint32_t M1,
		size_t len)
{
  if (len == 1)
    {
      uint16_t r = R[0];
      uint16_t m = M1;
      while (m > 1)
	{
	  *out++ = r;
	  r >>= 8;
	  m = (m + 255) >> 8;
	}
    }
  if (len > 1)
    {
      uint16_t R2[(len + 1) / 2];
      uint32_t M2;
      unsigned c0;
      size_t i;
      for (c0 = 0, M2 = M0 * M0; M2 >= 16384; M2 = (M2 + 255) >> 8)
	c0++;

      /* Process all but the last one or two elements, using M0, M0. */
      for (i = 0; i < len - 2; i += 2)
	{
	  uint32_t r = R[i] + R[i + 1] * M0;
	  unsigned j;
	  for (j = 0; j < c0; j++, r >>= 8)
	    *out++ = r;
	  R2[i / 2] = r;
	}
      /* Last two elements processed using M0, M1. */
      if (i == len - 2)
	{
	  uint32_t r = R[i] + R[i + 1] * M0;
	  for (M1 *= M0; M1 >= 16384; M1 = (M1 + 255) >> 8)
	    {
	      *out++ = r;
	      r >>= 8;
	    }
	  R2[i / 2] = r;
	}
      else
	R2[i / 2] = R[i];

      _sntrup_encode (out, R2, M2, M1, (len + 1) / 2);
    }
}

/* from supercop-20201130/crypto_kem/sntrup761/ref/kem.c */

/* ----- masks */


/* ----- arithmetic mod 3 */

/* F3 is always represented as -1,0,1 */
int8_t
_sntrup_mod_3 (int16_t x)
{
  uint16_t ux, a, r, p, mask;
  /* x is either an canonical representative of Fq, |x| <= (q-1) / 2,
     or result of polynomial multiplication in which case |x| <= 2p
     which is a smaller range. */
  assert_maybe (x <= SNTRUP761_Q12);
  assert_maybe (x >= -SNTRUP761_Q12);

  /* We want ((x + 1) mod q) - 1, but also add a multiple of 3 so we
     can use unsigned arithmetic. And (q-1)/2 happens to be a multiple
     of 3. */
  ux = x + 1 + SNTRUP761_Q12;
  /* Magic constant is ceil (2^16 / 3). */
  a = ((uint32_t) 21846 * ux) >> 16;
  p = 3 * a;
  mask = - (uint16_t) (p > ux);
  r = ux - p  + (mask & 3);
  assert_maybe (r < 3);
  return (int8_t) r - 1;
}
/* ----- arithmetic mod q */

/* always represented as -(q-1)/2...(q-1)/2 */
/* so ZZ_fromFq is a no-op */

int16_t
_sntrup761_mod_q (int32_t x)
{
  uint32_t ux, a, r, p, mask;
  /* When called from Rq_mult_small, inputs are limited to w*(q-1) (or
     p*(q-1) for overweight inputs), but for Fq_recip and Rq_recip3
     inputs may be up to 2 q^2, which is a larger range. */
  assert_maybe (x < 2*SNTRUP761_Q * SNTRUP761_Q);
  assert_maybe (x > -2*SNTRUP761_Q * SNTRUP761_Q);
  /* We want ((x + (q-1)/2) mod q) - (q-1)/2, but also add a multiple
     of q so we can use unsigned arithmetic. */
  ux = x + SNTRUP761_Q12 + 2*SNTRUP761_Q * SNTRUP761_Q;
  /* Magic constant is ceil (2^32 / q) */
  a = ((uint64_t) 935519 * ux) >> 32;
  p = SNTRUP761_Q * a;
  mask = - (uint32_t) (p > ux);
  r = ux - p  + (mask & SNTRUP761_Q);
  assert_maybe (r < SNTRUP761_Q);
  return (int32_t) r - SNTRUP761_Q12;
}

/* 0 if Weightw_is(r), else -1 */
static int
Weightw_mask (sntrup761_R3_t r)
{
  int weight = 0;
  int i;

  for (i = 0; i < SNTRUP761_P; ++i)
    weight += r[i] & 1;
  return int16_t_nonzero_mask (weight - SNTRUP761_W);
}

/* R3_fromR(R_fromRq(r)) */
static void
R3_fromRq (sntrup761_R3_t out, const sntrup761_Rq_t r)
{
  int i;
  for (i = 0; i < SNTRUP761_P; ++i)
    out[i] = _sntrup_mod_3 (r[i]);
}

/* h = f*g in the ring R3 */
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

/* ----- polynomials mod q */

/* h = f*g in the ring Rq */
void
_sntrup761_Rq_mult_small (sntrup761_Rq_t h, const sntrup761_Rq_t f, const sntrup761_R3_t g)
{
  int32_t fg[SNTRUP761_P + SNTRUP761_P - 1];
  int i, j;

  for (i = 0; i < SNTRUP761_P; ++i)
    {
      int32_t result;
      for (result = 0, j = 0; j <= i; ++j)
	result +=  f[j] * (int32_t) g[i - j];
      fg[i] = result;
    }
  for (i = SNTRUP761_P; i < SNTRUP761_P + SNTRUP761_P - 1; ++i)
    {
      int32_t result;
      for (result = 0, j = i - SNTRUP761_P + 1; j < SNTRUP761_P; ++j)
	result += f[j] * (int32_t) g[i - j];
      fg[i] = result;
    }

  for (i = SNTRUP761_P + SNTRUP761_P - 2; i >= SNTRUP761_P; --i)
    {
      fg[i - SNTRUP761_P] += fg[i];
      fg[i - SNTRUP761_P + 1] += fg[i];
    }

  for (i = 0; i < SNTRUP761_P; ++i)
    h[i] = _sntrup761_mod_q (fg[i]);
}

/* h = 3f in Rq */
static void
Rq_mult3 (sntrup761_Rq_t h, const sntrup761_Rq_t f)
{
  int i;

  for (i = 0; i < SNTRUP761_P; ++i)
    h[i] = _sntrup761_mod_q (3 * f[i]);
}

/* ----- rounded polynomials mod q */

/* ----- sorting to generate short polynomial */

static void
Short_fromlist (sntrup761_R3_t out, const uint32_t *in)
{
  uint32_t L[SNTRUP761_P];
  int i;

  for (i = 0; i < SNTRUP761_W; ++i)
    L[i] = in[i] & (uint32_t) - 2;
  for (i = SNTRUP761_W; i < SNTRUP761_P; ++i)
    L[i] = (in[i] & (uint32_t) - 3) | 1;
  crypto_sort_uint32 (L, SNTRUP761_P);
  for (i = 0; i < SNTRUP761_P; ++i)
    out[i] = (L[i] & 3) - 1;
}

/* ----- underlying hash function */

void
_sntrup_hash_init (struct sha512_ctx *ctx, uint8_t b)
{
  sha512_init (ctx);
  sha512_update (ctx, 1, &b);
}

void
_sntrup_hash_digest (struct sha512_ctx *ctx, uint8_t *digest)
{
  uint8_t h[SHA512_DIGEST_SIZE];
  sha512_digest (ctx, h);
  memcpy (digest, h, SNTRUP_HASH_SIZE);
}

void
_sntrup_hash_prefix (uint8_t *out, uint8_t b, const uint8_t *in, int inlen)
{
  struct sha512_ctx ctx;
  _sntrup_hash_init (&ctx, b);
  _sntrup_hash_update (&ctx, inlen, in);
  _sntrup_hash_digest (&ctx, out);
}

/* ----- higher-level randomness */

uint32_t
_sntrup_urandom32 (void *random_ctx, nettle_random_func * random)
{
  uint8_t c[4];
  uint32_t out[4];

  random (random_ctx, 4, c);
  out[0] = (uint32_t) c[0];
  out[1] = ((uint32_t) c[1]) << 8;
  out[2] = ((uint32_t) c[2]) << 16;
  out[3] = ((uint32_t) c[3]) << 24;
  return out[0] + out[1] + out[2] + out[3];
}

void
_sntrup761_short_random (sntrup761_R3_t out, void *random_ctx, nettle_random_func * random)
{
  uint32_t L[SNTRUP761_P];
  int i;

  for (i = 0; i < SNTRUP761_P; ++i)
    L[i] = _sntrup_urandom32 (random_ctx, random);
  Short_fromlist (out, L);
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
  R3_mult (ev, e, ginv);

  mask = Weightw_mask (ev);	/* 0 if weight SNTRUP761_W, else -1 */
  for (i = 0; i < SNTRUP761_W; ++i)
    r[i] = ((ev[i] ^ 1) & ~mask) ^ 1;
  for (i = SNTRUP761_W; i < SNTRUP761_P; ++i)
    r[i] = ev[i] & ~mask;
}

/* ----- encoding small polynomials (including short polynomials) */

/* these are the only functions that rely on SNTRUP761_P mod 4 = 1 */

void
_sntrup761_small_encode (uint8_t *s, const sntrup761_R3_t f)
{
  const int8_t *p;
  int i;

  for (i = 0, p = f; i < SNTRUP761_P / 4; ++i)
    {
      int8_t x;
      x = *p++ + 1;
      x += (*p++ + 1) << 2;
      x += (*p++ + 1) << 4;
      x += (*p++ + 1) << 6;
      *s++ = x;
    }
  *s = *p + 1;
}

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

/* ----- encoding general polynomials */


/* ----- encoding rounded polynomials */

static void
Rounded_decode (sntrup761_Rq_t r, const uint8_t *s)
{
  uint16_t R[SNTRUP761_P], M[SNTRUP761_P];
  int i;

  for (i = 0; i < SNTRUP761_P; ++i)
    M[i] = (SNTRUP761_Q + 2) / 3;
  _sntrup_decode (R, s, M, SNTRUP761_P);
  for (i = 0; i < SNTRUP761_P; ++i)
    r[i] = R[i] * 3 - SNTRUP761_Q12;
}

/* ----- Streamlined NTRU Prime Core plus encoding */

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

/* ----- confirmation hash */

#define Confirm_bytes 32

void
_sntrup_hash_confirm (uint8_t *h, const uint8_t *r,
		      const uint8_t *cache)
{
  struct sha512_ctx ctx;
  uint8_t x[SNTRUP_HASH_SIZE];

  _sntrup_hash_prefix (x, 3, r, SNTRUP761_R3_SIZE);
  _sntrup_hash_init (&ctx, 2);
  _sntrup_hash_update (&ctx, sizeof (x), x);
  _sntrup_hash_update (&ctx, SNTRUP_HASH_SIZE, cache);
  _sntrup_hash_digest (&ctx, h);
}

/* ----- session-key hash */

/* k = HashSession(b,y,z) */
void
_sntrup_hash_session (uint8_t *k, uint8_t b, const uint8_t *y,
		      const uint8_t *z)
{
  struct sha512_ctx ctx;
  uint8_t x[SNTRUP_HASH_SIZE];

  _sntrup_hash_prefix (x, 3, y, SNTRUP761_R3_SIZE);
  _sntrup_hash_init (&ctx, b);
  _sntrup_hash_update (&ctx, sizeof (x), x);
  _sntrup_hash_update (&ctx, SNTRUP761_CIPHER_SIZE, z);
  _sntrup_hash_digest (&ctx, k);
}

/* ----- Streamlined NTRU Prime */


/* 0 if matching ciphertext+confirm, else -1 */
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
sntrup761_dec (uint8_t *k, const uint8_t *c, const uint8_t *sk)
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
  _sntrup761_encrypt_internal (cnew, r_enc, r, pk, cache);
  mask = Ciphertexts_diff_mask (c, cnew);
  for (i = 0; i < SNTRUP761_R3_SIZE; ++i)
    r_enc[i] ^= mask & (r_enc[i] ^ rho[i]);
  _sntrup_hash_session (k, 1 + mask, r_enc, c);
}
