/* der2dsa.c
 *
 * Decoding of DSA keys in OpenSSL and X509.1 format.
 */

/* nettle, low-level cryptographics library
 *
 * Copyright (C) 2005, 2009, 2014 Niels Möller, Magnus Holmgren
 *  
 * The nettle library is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation; either version 2.1 of the License, or (at your
 * option) any later version.
 * 
 * The nettle library is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser General Public
 * License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the nettle library; see the file COPYING.LIB.  If not, write to
 * the Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston,
 * MA 02111-1301, USA.
 */

#if HAVE_CONFIG_H
# include "config.h"
#endif

#include <assert.h>

#include "dsa.h"

#include "bignum.h"
#include "asn1.h"

#define GET(i, x, l)					\
(asn1_der_iterator_next((i)) == ASN1_ITERATOR_PRIMITIVE	\
 && (i)->type == ASN1_INTEGER				\
 && asn1_der_get_bignum((i), (x), (l))			\
 && mpz_sgn((x)) > 0)

/* If q_bits > 0, q is required to be of exactly this size. */
int
dsa_params_from_der_iterator(struct dsa_params *params,
			     unsigned max_bits, unsigned q_bits,
			     struct asn1_der_iterator *i)
{
  /* Dss-Parms ::= SEQUENCE {
	 p  INTEGER,
	 q  INTEGER,
	 g  INTEGER
     }
  */
  if (i->type == ASN1_INTEGER
      && asn1_der_get_bignum(i, params->p, max_bits)
      && mpz_sgn(params->p) > 0)
    {
      unsigned p_bits = mpz_sizeinbase (params->p, 2);
      return (GET(i, params->q, q_bits ? q_bits : p_bits)
	      && (q_bits == 0 || mpz_sizeinbase(params->q, 2) == q_bits)
	      && mpz_cmp (params->q, params->p) < 0
	      && GET(i, params->g, p_bits)
	      && mpz_cmp (params->g, params->p) < 0
	      && asn1_der_iterator_next(i) == ASN1_ITERATOR_END);
    }
  else
    return 0;
}

int
dsa_public_key_from_der_iterator(struct dsa_value *pub,
				 struct asn1_der_iterator *i)
{
  /* DSAPublicKey ::= INTEGER
  */

  return (i->type == ASN1_INTEGER
	  && asn1_der_get_bignum(i, pub->x,
				 mpz_sizeinbase (pub->params->p, 2))
	  && mpz_sgn(pub->x) > 0
	  && mpz_cmp(pub->x, pub->params->p) < 0);    
}

int
dsa_openssl_private_key_from_der_iterator(struct dsa_params *params,
					  struct dsa_value *pub,
					  struct dsa_value *priv,
					  unsigned p_max_bits,
					  struct asn1_der_iterator *i)
{
  /* DSAPrivateKey ::= SEQUENCE {
         version           Version,
	 p                 INTEGER,
	 q                 INTEGER,
	 g                 INTEGER,
	 pub_key           INTEGER,  -- y
	 priv_key          INTEGER,  -- x
    }
  */

  uint32_t version;

  assert (pub->params == params);
  assert (priv->params == params);
  if (i->type == ASN1_SEQUENCE
	  && asn1_der_decode_constructed_last(i) == ASN1_ITERATOR_PRIMITIVE
	  && i->type == ASN1_INTEGER
	  && asn1_der_get_uint32(i, &version)
	  && version == 0
      && GET(i, params->p, p_max_bits))
    {
      unsigned p_bits = mpz_sizeinbase (params->p, 2);
      return (GET(i, params->q, DSA_SHA1_Q_BITS)
	      && GET(i, params->g, p_bits)
	      && mpz_cmp (params->g, params->p) < 0
	      && GET(i, pub->x, p_bits)
	      && mpz_cmp (pub->x, params->p) < 0
	      && GET(i, priv->x, DSA_SHA1_Q_BITS)
	      && asn1_der_iterator_next(i) == ASN1_ITERATOR_END);
    }
  else
    return 0;
}

int
dsa_openssl_private_key_from_der(struct dsa_params *params,
				 struct dsa_value *pub,
				 struct dsa_value *priv,
				 unsigned p_max_bits,
				 size_t length, const uint8_t *data)
{
  struct asn1_der_iterator i;
  enum asn1_iterator_result res;

  res = asn1_der_iterator_first(&i, length, data);

  return (res == ASN1_ITERATOR_CONSTRUCTED
	  && dsa_openssl_private_key_from_der_iterator(params, pub, priv,
						       p_max_bits, &i));
}
