/* ecc-secp521r1.c

   Compile time constant (but machine dependent) tables.

   Copyright (C) 2013, 2014 Niels Möller

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

/* Development of Nettle's ECC support was funded by the .SE Internet Fund. */

#if HAVE_CONFIG_H
# include "config.h"
#endif

#include "ecc-internal.h"

#define USE_REDC 0

#include "ecc-secp521r1.h"

#define B_SHIFT (521 % GMP_NUMB_BITS)

#if HAVE_NATIVE_ecc_secp521r1_modp
#define ecc_secp521r1_modp _nettle_ecc_secp521r1_modp
void
ecc_secp521r1_modp (const struct ecc_modulo *m, mp_limb_t *rp, mp_limb_t *xp);

#else

#define BMODP_SHIFT (GMP_NUMB_BITS - B_SHIFT)
#define BMODP ((mp_limb_t) 1 << BMODP_SHIFT)

/* Result may be *slightly* larger than 2^521 */
static void
ecc_secp521r1_modp (const struct ecc_modulo *m UNUSED, mp_limb_t *rp, mp_limb_t *xp)
{
  /* FIXME: Should use mpn_addlsh_n_ip1 */
  mp_limb_t hi;
  /* Reduce from 2*ECC_LIMB_SIZE to ECC_LIMB_SIZE + 1 */
  xp[ECC_LIMB_SIZE]
    = mpn_addmul_1 (xp, xp + ECC_LIMB_SIZE, ECC_LIMB_SIZE, BMODP);
  hi = mpn_addmul_1 (xp, xp + ECC_LIMB_SIZE, 1, BMODP);
  hi = sec_add_1 (xp + 1, xp + 1, ECC_LIMB_SIZE - 1, hi);

  /* Combine hi with top bits, and add in. */
  hi = (hi << BMODP_SHIFT) | (xp[ECC_LIMB_SIZE-1] >> B_SHIFT);
  rp[ECC_LIMB_SIZE-1] = (xp[ECC_LIMB_SIZE-1]
			 & (((mp_limb_t) 1 << B_SHIFT)-1))
    + sec_add_1 (rp, xp, ECC_LIMB_SIZE - 1, hi);
}
#endif

#define ECC_SECP521R1_SQRT_ITCH (2*ECC_LIMB_SIZE)

static int
ecc_secp521r1_sqrt (const struct ecc_modulo *m,
		    mp_limb_t *rp,
		    const mp_limb_t *cp,
		    mp_limb_t *scratch)
{
  mp_limb_t hi;

  /* This computes the square root modulo p256 using the identity:

     sqrt(c) = c^(2^519) (mod P-521)

     which can be seen as a special case of Tonelli-Shanks with e=1.
  */

  ecc_mod_pow_2k (m, rp, cp, 519, scratch);

  /* Check result. */
  ecc_mod_sqr (m, scratch, rp, scratch);
  ecc_mod_sub (m, scratch, scratch, cp);

  /* Reduce top bits, since ecc_mod_zero_p requires input < 2p */
  hi = scratch[ECC_LIMB_SIZE-1] >> B_SHIFT;
  scratch[ECC_LIMB_SIZE-1] = (scratch[ECC_LIMB_SIZE-1]
			      & (((mp_limb_t) 1 << B_SHIFT)-1))
    + sec_add_1 (scratch, scratch, ECC_LIMB_SIZE - 1, hi);

  return ecc_mod_zero_p (m, scratch);
}


const struct ecc_curve _nettle_secp_521r1 =
{
  {
    521,
    ECC_LIMB_SIZE,    
    ECC_BMODP_SIZE,
    ECC_REDC_SIZE,
    ECC_MOD_INV_ITCH(ECC_LIMB_SIZE),
    ECC_SECP521R1_SQRT_ITCH,
    0,
    ECC_INVP_COUNT,
    ECC_BINVP,

    ecc_p,
    ecc_Bmodp,
    ecc_Bmodp_shifted,
    ecc_Bm2p,
    ecc_redc_ppm1,
    NULL,

    ecc_secp521r1_modp,
    ecc_secp521r1_modp,
    ecc_mod_inv,
    ecc_secp521r1_sqrt,
    NULL,
  },
  {
    521,
    ECC_LIMB_SIZE,    
    ECC_BMODQ_SIZE,
    0,
    ECC_MOD_INV_ITCH (ECC_LIMB_SIZE),
    0,
    0,
    ECC_INVQ_COUNT,
    ECC_BINVQ,

    ecc_q,
    ecc_Bmodq,
    ecc_Bmodq_shifted,
    ecc_Bm2q,
    NULL,
    NULL,

    ecc_mod,
    ecc_mod,
    ecc_mod_inv,
    NULL,
    NULL,
  },
  
  USE_REDC,
  ECC_PIPPENGER_K,
  ECC_PIPPENGER_C,

  ECC_ADD_JJA_ITCH (ECC_LIMB_SIZE),
  ECC_ADD_JJJ_ITCH (ECC_LIMB_SIZE),
  ECC_DUP_JJ_ITCH (ECC_LIMB_SIZE),
  ECC_MUL_A_ITCH (ECC_LIMB_SIZE),
  ECC_MUL_G_ITCH (ECC_LIMB_SIZE),
#if 0
  ECC_J_TO_A_ITCH(ECC_LIMB_SIZE, ECC_SECP521R1_INV_ITCH),
#else
  ECC_J_TO_A_ITCH(ECC_LIMB_SIZE, ECC_MOD_INV_ITCH(ECC_LIMB_SIZE)),
#endif
  ecc_add_jja,
  ecc_add_jjj,
  ecc_dup_jj,
  ecc_mul_a,
  ecc_mul_g,
  ecc_j_to_a,

  ecc_b,
  ecc_unit,
  ecc_table
};

const struct ecc_curve *nettle_get_secp_521r1(void)
{
  return &_nettle_secp_521r1;
}
