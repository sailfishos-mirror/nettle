/* sha3.h

   The sha3 hash function (aka Keccak).

   Copyright (C) 2012 Niels Möller

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
 
#ifndef NETTLE_SHA3_H_INCLUDED
#define NETTLE_SHA3_H_INCLUDED

#include "nettle-types.h"

#ifdef __cplusplus
extern "C" {
#endif

/* Name mangling */
#define sha3_permute nettle_sha3_permute
#define sha3_init nettle_sha3_init
#define sha3_128_update nettle_sha3_128_update
#define sha3_128_shake nettle_sha3_128_shake
#define sha3_128_shake_output nettle_sha3_128_shake_output
#define sha3_224_update nettle_sha3_224_update
#define sha3_224_digest nettle_sha3_224_digest
#define sha3_256_update nettle_sha3_256_update
#define sha3_256_digest nettle_sha3_256_digest
#define sha3_256_shake nettle_sha3_256_shake
#define sha3_256_shake_output nettle_sha3_256_shake_output
#define sha3_384_update nettle_sha3_384_update
#define sha3_384_digest nettle_sha3_384_digest
#define sha3_512_update nettle_sha3_512_update
#define sha3_512_digest nettle_sha3_512_digest

/* Indicates that SHA3 is the NIST FIPS 202 version. */
#define NETTLE_SHA3_FIPS202 1

/* The sha3 state is a 5x5 matrix of 64-bit words. In the notation of
   Keccak description, S[x,y] is element x + 5*y, so if x is
   interpreted as the row index and y the column index, it is stored
   in column-major order. */
#define SHA3_STATE_LENGTH 25

/* The "width" is 1600 bits or 200 octets */
struct sha3_state
{
  uint64_t a[SHA3_STATE_LENGTH];
};

void
sha3_permute (struct sha3_state *state);

/* The "capacity" is set to 2*(digest size), 512 bits or 64 octets.
   The "rate" is the width - capacity, or width - 2 * (digest
   size). */

#define SHA3_128_DIGEST_SIZE 16
#define SHA3_128_BLOCK_SIZE 168

#define SHA3_224_DIGEST_SIZE 28
#define SHA3_224_BLOCK_SIZE 144

#define SHA3_256_DIGEST_SIZE 32
#define SHA3_256_BLOCK_SIZE 136

#define SHA3_384_DIGEST_SIZE 48
#define SHA3_384_BLOCK_SIZE 104

#define SHA3_512_DIGEST_SIZE 64
#define SHA3_512_BLOCK_SIZE 72

struct sha3_ctx
{
  struct sha3_state state;
  /* The position in current block of next input byte (for update) or
     next output byte (for shake). */
  unsigned index;
  /* Set when shake output has been initialized. */
  int shake_flag;
  /* Buffer for partial words; input and output from the state is
     handled one uint64_t at a time. */
  union nettle_block8 block;
};

void
sha3_init (struct sha3_ctx *ctx);

void
sha3_128_update (struct sha3_ctx *ctx, size_t length, const uint8_t *data);

void
sha3_128_shake (struct sha3_ctx *ctx, size_t length, uint8_t *digest);

void
sha3_128_shake_output (struct sha3_ctx *ctx, size_t length, uint8_t *digest);

void
sha3_224_update (struct sha3_ctx *ctx, size_t length, const uint8_t *data);

void
sha3_224_digest(struct sha3_ctx *ctx, uint8_t *digest);

void
sha3_256_update (struct sha3_ctx *ctx, size_t length, const uint8_t *data);

void
sha3_256_digest(struct sha3_ctx *ctx, uint8_t *digest);

/* Alternative digest function implementing shake256, with arbitrary
   digest size */
void
sha3_256_shake(struct sha3_ctx *ctx, size_t length, uint8_t *digest);

/* Unlike sha3_256_shake, this function can be called multiple times
   to retrieve output from shake256 in an incremental manner */
void
sha3_256_shake_output(struct sha3_ctx *ctx, size_t length, uint8_t *digest);

void
sha3_384_update (struct sha3_ctx *ctx, size_t length, const uint8_t *data);

void
sha3_384_digest(struct sha3_ctx *ctx, uint8_t *digest);

void
sha3_512_update (struct sha3_ctx *ctx, size_t length, const uint8_t *data);

void
sha3_512_digest(struct sha3_ctx *ctx, uint8_t *digest);

/* Old names, for compatibility with nettle-3. */
#define sha3_128_ctx sha3_ctx
#define sha3_224_ctx sha3_ctx
#define sha3_256_ctx sha3_ctx
#define sha3_384_ctx sha3_ctx
#define sha3_512_ctx sha3_ctx

#define sha3_128_init sha3_init
#define sha3_224_init sha3_init
#define sha3_256_init sha3_init
#define sha3_384_init sha3_init
#define sha3_512_init sha3_init

#ifdef __cplusplus
}
#endif

#endif /* NETTLE_SHA3_H_INCLUDED */
