/* slh-dsa-test.c

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

#include "testutils.h"

#include "sha3.h"
#include "slh-dsa.h"
#include "slh-dsa-internal.h"
#include "bswap-internal.h"

static void
test_wots_gen (const struct tstring *public_seed, const struct tstring *secret_seed,
	       unsigned layer, uint64_t tree_idx, uint32_t keypair,
	       const struct tstring *exp_pub)
{
  struct slh_address_tree at = {0};
  uint8_t pub[_SLH_DSA_128_SIZE];
  ASSERT (public_seed->length == _SLH_DSA_128_SIZE);
  ASSERT (secret_seed->length == _SLH_DSA_128_SIZE);
  ASSERT (exp_pub->length == _SLH_DSA_128_SIZE);

  at.layer = bswap32_if_le (layer);
  at.tree_idx = bswap64_if_le (tree_idx);
  _wots_gen (public_seed->data, secret_seed->data, &at, keypair, pub);
  mark_bytes_defined (sizeof (pub), pub);
  ASSERT (MEMEQ (sizeof (pub), pub, exp_pub->data));
}

static void
test_wots_sign (const struct tstring *public_seed, const struct tstring *secret_seed,
		unsigned layer, uint64_t tree_idx, uint32_t keypair, const struct tstring *msg,
		const struct tstring *exp_pub, const struct tstring *exp_sig)
{
  struct slh_address_tree at = {0};
  uint8_t sig[WOTS_SIGNATURE_SIZE];
  uint8_t pub[_SLH_DSA_128_SIZE];
  ASSERT (public_seed->length == _SLH_DSA_128_SIZE);
  ASSERT (secret_seed->length == _SLH_DSA_128_SIZE);
  ASSERT (msg->length == _SLH_DSA_128_SIZE);
  ASSERT (exp_pub->length == _SLH_DSA_128_SIZE);
  ASSERT (exp_sig->length == WOTS_SIGNATURE_SIZE);

  at.layer = bswap32_if_le (layer);
  at.tree_idx = bswap64_if_le (tree_idx);

  _wots_sign (public_seed->data, secret_seed->data, &at, keypair,
	      msg->data, sig, pub);
  mark_bytes_defined (sizeof(sig), sig);
  mark_bytes_defined (sizeof(pub), pub);
  ASSERT (MEMEQ(sizeof(sig), sig, exp_sig->data));
  ASSERT (MEMEQ(sizeof(pub), pub, exp_pub->data));

  memset (pub, 0, sizeof(pub));
  _wots_verify (public_seed->data, &at, keypair, msg->data, sig, pub);
  ASSERT (MEMEQ(sizeof(pub), pub, exp_pub->data));
}

/* The xmss_leaf and xmss_node functions copied from slh-xmss.c */
static void
xmss_leaf (const struct slh_merkle_ctx_secret *ctx, unsigned idx, uint8_t *leaf)
{
  _wots_gen (ctx->pub.seed, ctx->secret_seed, &ctx->pub.at, idx, leaf);
  mark_bytes_defined (SLH_DSA_SHAKE_128_SEED_SIZE, leaf);
}

static void
xmss_node (const struct slh_merkle_ctx_public *ctx, unsigned height, unsigned index,
	   const uint8_t *left, const uint8_t *right, uint8_t *out)
{
  struct sha3_256_ctx sha3;
  struct slh_address_hash ah =
    {
      bswap32_if_le (SLH_XMSS_TREE),
      0,
      bswap32_if_le (height),
      bswap32_if_le (index),
    };

  _slh_shake_init (&sha3, ctx->seed, &ctx->at, &ah);
  sha3_256_update (&sha3, _SLH_DSA_128_SIZE, left);
  sha3_256_update (&sha3, _SLH_DSA_128_SIZE, right);
  sha3_256_shake (&sha3, _SLH_DSA_128_SIZE, out);
}

static void
test_merkle (const struct tstring *public_seed, const struct tstring *secret_seed,
	     unsigned h,
	     unsigned layer, uint64_t tree_idx, uint32_t idx, const struct tstring *msg,
	     const struct tstring *exp_pub, const struct tstring *exp_sig)
{
  struct slh_merkle_ctx_secret ctx =
    {
      {
	public_seed->data,
	{ bswap32_if_le(layer), 0, bswap64_if_le(tree_idx) },
	0,
      },
      secret_seed->data,
    };

  uint8_t *sig = xalloc(XMSS_AUTH_SIZE(h));
  uint8_t pub[_SLH_DSA_128_SIZE];
  ASSERT (public_seed->length == _SLH_DSA_128_SIZE);
  ASSERT (secret_seed->length == _SLH_DSA_128_SIZE);
  ASSERT (msg->length == _SLH_DSA_128_SIZE);
  ASSERT (exp_pub->length == _SLH_DSA_128_SIZE);
  ASSERT (exp_sig->length == XMSS_AUTH_SIZE(h));

  _merkle_sign (&ctx, xmss_leaf, xmss_node, h, idx, sig);
  ASSERT (MEMEQ(exp_sig->length, sig, exp_sig->data));

  memcpy (pub, msg->data, sizeof(pub));
  _merkle_verify (&ctx.pub, xmss_node, h, idx, sig, pub);
  ASSERT (MEMEQ(sizeof(pub), pub, exp_pub->data));
  free (sig);
}

static void
test_fors_gen(const struct tstring *public_seed, const struct tstring *secret_seed,
	      unsigned layer, uint64_t tree_idx, unsigned keypair, unsigned idx,
	      const struct tstring *exp_sk, const struct tstring *exp_leaf)
{
  struct slh_merkle_ctx_secret ctx =
    {
      {
	public_seed->data,
	{ bswap32_if_le(layer), 0, bswap64_if_le(tree_idx) },
	keypair,
      },
      secret_seed->data,
    };
  uint8_t sk[_SLH_DSA_128_SIZE];
  uint8_t leaf[_SLH_DSA_128_SIZE];
  ASSERT (public_seed->length == _SLH_DSA_128_SIZE);
  ASSERT (secret_seed->length == _SLH_DSA_128_SIZE);
  ASSERT (exp_sk->length == _SLH_DSA_128_SIZE);
  ASSERT (exp_leaf->length == _SLH_DSA_128_SIZE);

  _fors_gen (&ctx, idx, sk, leaf);
  mark_bytes_defined (sizeof(sk), sk);
  mark_bytes_defined (sizeof(sk), leaf);
  ASSERT (MEMEQ(sizeof(sk), sk, exp_sk->data));
  ASSERT (MEMEQ(sizeof(leaf), leaf, exp_leaf->data));
}

static void
test_fors_sign (const struct tstring *public_seed, const struct tstring *secret_seed,
		const struct slh_fors_params *fors,
		unsigned layer, uint64_t tree_idx, unsigned keypair, const struct tstring *msg,
		const struct tstring *exp_pub, const struct tstring *exp_sig)
{
  struct slh_merkle_ctx_secret ctx =
    {
      {
	public_seed->data,
	{ bswap32_if_le(layer), 0, bswap64_if_le(tree_idx) },
	keypair,
      },
      secret_seed->data,
    };
  uint8_t pub[_SLH_DSA_128_SIZE];
  uint8_t *sig = xalloc (fors->signature_size);
  ASSERT (public_seed->length == _SLH_DSA_128_SIZE);
  ASSERT (secret_seed->length == _SLH_DSA_128_SIZE);
  ASSERT (msg->length == fors->msg_size);
  ASSERT (exp_pub->length == _SLH_DSA_128_SIZE);
  ASSERT (exp_sig->length == fors->signature_size);

  _fors_sign (&ctx, fors, msg->data, sig, pub);
  mark_bytes_defined (exp_sig->length, sig);
  mark_bytes_defined (sizeof(pub), pub);
  ASSERT (MEMEQ(exp_sig->length, sig, exp_sig->data));
  ASSERT (MEMEQ(sizeof(pub), pub, exp_pub->data));

  memset (pub, 0, sizeof(pub));
  _fors_verify (&ctx.pub, fors, msg->data, sig, pub);
  ASSERT (MEMEQ(sizeof(pub), pub, exp_pub->data));
  free (sig);
}

static void
test_xmss_sign (const struct tstring *public_seed, const struct tstring *secret_seed,
		unsigned xmss_h,
		unsigned layer, uint64_t tree_idx, uint32_t idx, const struct tstring *msg,
		const struct tstring *exp_pub, const struct tstring *exp_sig)
{
  struct slh_merkle_ctx_secret ctx =
    {
      {
	public_seed->data,
	{ bswap32_if_le(layer), 0, bswap64_if_le(tree_idx) },
	0,
      },
      secret_seed->data,
    };

  uint8_t *sig = xalloc(XMSS_SIGNATURE_SIZE(xmss_h));
  uint8_t pub[_SLH_DSA_128_SIZE];
  ASSERT (public_seed->length == _SLH_DSA_128_SIZE);
  ASSERT (secret_seed->length == _SLH_DSA_128_SIZE);
  ASSERT (msg->length == _SLH_DSA_128_SIZE);
  ASSERT (exp_pub->length == _SLH_DSA_128_SIZE);
  ASSERT (exp_sig->length == XMSS_SIGNATURE_SIZE(xmss_h));

  _xmss_sign (&ctx, xmss_h, idx, msg->data, sig, pub);
  mark_bytes_defined (sizeof(pub), pub);
  mark_bytes_defined (exp_sig->length, sig);
  ASSERT (MEMEQ(exp_sig->length, sig, exp_sig->data));
  ASSERT (MEMEQ(sizeof(pub), pub, exp_pub->data));

  memset (pub, 0, sizeof(pub));
  _xmss_verify (&ctx.pub, xmss_h, idx, msg->data, sig, pub);
  ASSERT (MEMEQ(sizeof(pub), pub, exp_pub->data));
  free (sig);
}

static void
test_slh_dsa_shake_128s_root (const struct tstring *public_seed, const struct tstring *secret_seed,
			      const struct tstring *exp_pub)
{
  uint8_t pub[_SLH_DSA_128_SIZE];
  ASSERT (public_seed->length == _SLH_DSA_128_SIZE);
  ASSERT (secret_seed->length == _SLH_DSA_128_SIZE);
  ASSERT (exp_pub->length == _SLH_DSA_128_SIZE);

  slh_dsa_shake_128s_root (public_seed->data, secret_seed->data, pub);
  mark_bytes_defined (sizeof(pub), pub);
  ASSERT (MEMEQ(sizeof(pub), pub, exp_pub->data));
}

static void
test_slh_dsa_shake_128s(const struct tstring *pub, const struct tstring *priv,
			const struct tstring *msg, const struct tstring *exp_sig)
{
  uint8_t sig[SLH_DSA_SHAKE_128S_SIGNATURE_SIZE];
  ASSERT (pub->length == SLH_DSA_SHAKE_128_KEY_SIZE);
  ASSERT (priv->length == SLH_DSA_SHAKE_128_KEY_SIZE);
  ASSERT (exp_sig->length == SLH_DSA_SHAKE_128S_SIGNATURE_SIZE);

  slh_dsa_shake_128s_sign (pub->data, priv->data, msg->length, msg->data, sig);
  if (! MEMEQ(sizeof(sig), sig, exp_sig->data))
    {
      size_t i;
      for (i = 0; i < sizeof(sig); i++)
	if (sig[i] != exp_sig->data[i])
	  break;

      fprintf (stderr, "failed slh_dsa_shake_128s_sign, first diff at %zd\n", i);
      abort ();
    }
  ASSERT (slh_dsa_shake_128s_verify (pub->data, msg->length, msg->data, sig));

  if (msg->length > 0)
    ASSERT (!slh_dsa_shake_128s_verify (pub->data, msg->length-1, msg->data, sig));
  sig[SLH_DSA_SHAKE_128S_SIGNATURE_SIZE-1] ^= 1;
  ASSERT (!slh_dsa_shake_128s_verify (pub->data, msg->length, msg->data, sig));
}

static void
test_slh_dsa_shake_128f(const struct tstring *pub, const struct tstring *priv,
			const struct tstring *msg, const struct tstring *exp_sig)
{
  uint8_t sig[SLH_DSA_SHAKE_128F_SIGNATURE_SIZE];
  ASSERT (pub->length == SLH_DSA_SHAKE_128_KEY_SIZE);
  ASSERT (priv->length == SLH_DSA_SHAKE_128_KEY_SIZE);
  ASSERT (exp_sig->length == SLH_DSA_SHAKE_128F_SIGNATURE_SIZE);

  slh_dsa_shake_128f_sign (pub->data, priv->data, msg->length, msg->data, sig);
  if (! MEMEQ(sizeof(sig), sig, exp_sig->data))
    {
      size_t i;
      for (i = 0; i < sizeof(sig); i++)
	if (sig[i] != exp_sig->data[i])
	  break;

      fprintf (stderr, "failed slh_dsa_shake_128f_sign, first diff at %zd\n", i);
      abort ();
    }
  ASSERT (slh_dsa_shake_128f_verify (pub->data, msg->length, msg->data, sig));

  if (msg->length > 0)
    ASSERT (!slh_dsa_shake_128f_verify (pub->data, msg->length-1, msg->data, sig));
  sig[SLH_DSA_SHAKE_128F_SIGNATURE_SIZE-1] ^= 1;
  ASSERT (!slh_dsa_shake_128f_verify (pub->data, msg->length, msg->data, sig));
}

void
test_main(void)
{
  const struct tstring *public_seed =
    SHEX("b505d7cfad1b497499323c8686325e47");

  const struct tstring *secret_seed =
    SHEX("7c9935a0b07694aa0c6d10e4db6b1add");

  mark_bytes_undefined (2*SLH_DSA_SHAKE_128_SEED_SIZE, secret_seed->data);

  test_wots_gen (public_seed, secret_seed, 6, 0, 0,
		 SHEX("38c9077d76d1e32933fb58a53e769ed7"));
  test_wots_gen (public_seed, secret_seed, 6, 0, 1,
		 SHEX("a026afacc77c7d97eebe6f88c70fec2d"));
  test_wots_gen (public_seed, secret_seed, 0, UINT64_C(0x29877722d7c079), 0x156,
		 SHEX("99747c3547770fa288a628ed15122d3e"));

  test_wots_sign (public_seed, secret_seed, 0, UINT64_C(0x29877722d7c079), 0x156,
		  SHEX("3961b2cab15e08c633be827744a07f01"),
		  SHEX("99747c3547770fa288a628ed15122d3e"),
		  SHEX("e1933de10e3fface 5fb8f8707c35ac13 74dc14ee8518481c 7e63d936ecc62f50"
		       "c7f951b87bc716dc 45e9bcfec6f6d97e 7fafdacb6db05ed3 778f21851f325e25"
		       "470da8dd81c41223 6d66cbee9ffa9c50 b86aa40baf213494 dfacca22aa0fb479"
		       "53928735ca4212cf 53a09ab0335d20a8 e62ede797c8e7493 54d636f15f3150c5"
		       "52797b76c091a41f 949f7fb57b42f744 1cca410264d6421f 4aa2c7e2ff4834a8"
		       "db0e6e7750b2e11f f1c89a42d1fbc271 8358e38325886ad1 2346cd694f9eab73"
		       "46c9a23b5ebe7637 bfd834a412318b01 188b0f29e3bd979f 8ae734acf1563af3"
		       "03d3c095e9eaeba3 5207b9df3acf9ee4 7da5c1e2652f3b86 41698f3d2260591b"
		       "07d00565e5d6be18 36033d2b7ef2c33b dc5cf3bba95b42df 6f73345b835341b2"
		       "50e2862c9f2f9cef 77cfa74cfb04c560 d8a0038c4e96cb0d a2b3e9b2cd3cecf5"
		       "22fda0d67e5f62b2 ee23bd42a61c7da4 8f0ea30b81af7ccb 6bb02cde272d2574"
		       "1325e9d91535615c 0184f2d7f226141d 79b42412721fd345 61d93663650b3c1b"
		       "6901872bc4c0bb15 bcd9038950b7717f 7f448b6126592076 a2bad2d63c55399c"
		       "243fdbdb0c8d676b 2ae455e7f0a9b18d 3fc889c43387f2cb c4dc73d7c85bfab6"
		       "b4b04463a3dd359c 3a8f61bfa6c4b042 4aeba4dd8a95ec12 43b2e36c29f82e1d"
		       "711281599b3e05e7 5492ae3425eaa7f1 4ff8c6a9630bba6e bd236f195269a481"
		       "e87eb3d444825ba4 424ee5b2d9efb595 d5a338f4c253f79d e9d04535206ca6db"
		       "c2d4c9a1ec20849b 0db3fbe10c1446d5"));

  test_merkle (public_seed, secret_seed, 9, 0, UINT64_C(0x29877722d7c079), 0x156,
	       /* The message signed is the wots public key. */
	       SHEX("99747c3547770fa288a628ed15122d3e"),
	       SHEX("1be9523f2c90cd553ef5be5aa1c5c4fa"),
	       SHEX("612d5bac915a3996 2cdbcacee0969dcf 8ecfb830cea2206c 37749c65b8f673db"
		    "090b1e2ade6c2a2f 349b5915103a3ac7 8482c39e99ffc462 6fb4cf4a116804ab"
		    "9d93d7104660fefa 0753cf875cb22fd6 0e55dc2f303de036 47712b12067a55f7"
		    "a467897bbed0d3a0 9d50e9deaadff78d e9ac65c1fd05d076 10a79c8c465141ad"
		    "65e60340531fab08 f1f433ef823283fe"));

  test_fors_gen (public_seed, secret_seed, 0, UINT64_C(0x29877722d7c079), 0x156, 0x203,
		 SHEX("1ba66d6f782bdd2485589ea15d2b8ff0"),
		 SHEX("4d9783fd544a53ee7a485ef229b35965"));
  test_fors_gen (public_seed, secret_seed, 0, UINT64_C(0x29877722d7c079), 0x156, 0,
		 SHEX("be19da5abd01818bbcae2fc2d728c83b"),
		 SHEX("40b0edc79104214adda356341b3950ab"));
  test_fors_gen (public_seed, secret_seed, 0, UINT64_C(0x29877722d7c079), 0x156, 1,
		 SHEX("ed98099d2fd9d94ac48cae4c142a4c78"),
		 SHEX("64fccb8a3cf088faeb39353aad5f624c"));
  test_fors_gen (public_seed, secret_seed, 0, UINT64_C(0x29877722d7c079), 0x156, 0x4e1e,
		 SHEX("17f55905e41a6dc6e5bab2c9f0c1d5d3"),
		 SHEX("15325ef3d2914cbd401327244cdb633d"));
  test_fors_sign (public_seed, secret_seed, &_slh_dsa_shake_128s_params.fors,
		  0, UINT64_C(0x29877722d7c079), 0x156,
		  SHEX("2033c1a4df6fc230c699522a21bed913"
		       "0dda231526"),
		  SHEX("3961b2cab15e08c633be827744a07f01"),
		  SHEX("1ba66d6f782bdd24 85589ea15d2b8ff0 a00c06eaedc8c22d cb86f3df8b52a3bd"
		       "144d4ed6f1167431 a95dc6018879b6b0 f9813797204ec2b0 558bad17b32e6dd9"
		       "88086a032c0acbcf 2c1349ffc16c4af7 59365ff74afe4b8d c3fac5b2cda7ba65"
		       "6c36c086e58468c0 1eddfc959fbdc853 2d75e79cf3374756 cc0491cfef555921"
		       "ec8567bff0b6f216 ac4a4f200da63b5c 6d3a5c3273aa7a42 66adf083d3126103"
		       "c73fe63a6e05e47e 8b9a520f00f32a69 7d0ff3a5ee840931 3773188f300b39e5"
		       "b4967febf77c0f23 226785ee9dce335c efb1ce84b0673058 1bcef4d45f24aee4"
		       "96a60bd4759b7b20 692241850eae1de7 0c7c4287b9f3b962 a66e0f23d1301b84"
		       "48bb3dc545be0ef8 d0ec0be045d33ae4 b2dc0c5d002c2699 e8f49bf3bcb13676"
		       "beefe11186a20a95 7027ac48ee6dd33b c0895df9847fd1c6 7a753777d21ac464"
		       "2751139061cca836 99822c13567833b9 41fe5954bff0969a 4b20e0829d77e24e"
		       "d0e02a00a2ce9f7e 64923fa61f0da1af dc5978dc063afeac b7108ee08aaa55b7"
		       "11df00bbf1c71d69 8b389e6ad0ee2af4 fad1d8f8c87d53ee ac1f82a162a95cd5"
		       "cce6dfc9908a1de3 3a2b26b41bbc4ffd a8e136879f10341a 713d62c107f3238c"
		       "38693aff2e1fe15a dd8380671b2fac8f db3a4ffacd143f5a 00e21caccbe7d95d"
		       "4c31c4daf7110529 de599fb6e8aa4f71 8c6172f4f10c4c1d d7310f8e44d18fb9"
		       "bb6b906ae7ce973d eadfc82d6704762e d61165f6ca118313 4b6c834bf6b4e4ce"
		       "19700bb54fb2d0f2 82b11ee5b7f68c72 cf32ff9e7d1356bd 53fdcce0d03c43d0"
		       "ebf6f7d8841a16dd b49944d01374ecb9 45e6c5f0659d5f51 de0b27a834e2e7be"
		       "a78a609da75d7f2c 6a40ba9110a2c331 9db7775bf6226b9a 8e324dc4411824a8"
		       "8db95cc2fd96e4bc 24f1ecb6ce2b9293 020c28deacec1eb3 313d4e3dfd24b403"
		       "686f16272cac3aca 95080257071a54f7 45ffb4708ff2d02d e94d7e9bf8d45f64"
		       "5917c7135d6bc0a1 ca0a99bc4e33a689 07aa65a58b586c56 e1d81af6cb57fa5d"
		       "56b3567687ecef53 2bb5aaaf2041b510 1538294296ae4c11 89a5100eb19b5531"
		       "2016c575cbbb688f 20ba186dd48e4161 64c29b2eb7b59979 814b5a8e76553997"
		       "99bf79eeab3ee76d 4c97df282265564f 2fa8971a1ecca0c4 6b59cc6ba253531c"
		       "17ab7125cf2aad60 a120c7d4b631b1ba f187182c7d7582da 3232251215ffd6a2"
		       "a55c627ba8d5cafe 761504d8341f293e 713987d6e0ca2eab 373c5131c2d38051"
		       "c35b17918937b9fe e98382c277640de0 ccec45ba22d9d189 eea505a21c8594dd"
		       "9b12e69a7faf58ed 269b718abeea4621 391d7fb4c6e0037b daf4a9ac73191674"
		       "9e2a17d704cf5616 8d97c17b257e2483 16aa9da15d822ee3 c325bc0519173641"
		       "7007ea82088618d7 531ffcef255b2de2 bf9fcaeb29d83e56 7a08dd3d3c229209"
		       "af96ba71d8274fda e324702878d99ac0 5e990e0d6f34c879 d19279f57541f294"
		       "96645cad4a636793 385b0a5dc21d5659 37fc36384dea4beb b5746c10748efcbd"
		       "6b1925a74e3ac467 d7af456e0ba1e47a 2fab24e8311c14d8 40b499c9140e99a4"
		       "993379b9b762b3ad c9499d5c86d07bc6 a159876a9962d8a4 43514e812f75c60d"
		       "c50028388c627329 6e7208a3fa618256 2d10d7142a99da06 86ef8f05e564446c"
		       "6bb32ffdee9edd13 aee58027d29e7195 48b67d75efe9581a 3374c66f65a1cd9e"
		       "f9e98e6b57c40321 2739df6fd2de6c8a 39decc7cd33e37db 3a0f43296cb987e8"
		       "756d4b29dc227733 bdee1d2f01679dab 92ce506e2fc77a70 798787b2e95be8e9"
		       "bf80d0b64af8eaa6 ceda80fe85a0ceaf 81f335b99a1899a3 d9d609e7ba606eb2"
		       "ababf2bbce1bc8f9 9eaf6074cf1c7e07 9896eb09827c16d0 cd4833377c46a337"
		       "a7950b31b6566624 02e8ba838668a315 ac531315a9a56af1 8729ee25f53711c0"
		       "9d25c173aa0e4d2b ec72db4b9cb4210d 52a8fb2f8b2671b1 ec711a4da8a357df"
		       "bb0d2ec9734a50e1 db92352ace0f26f5 0cfb76fd17a08dec bb19c2417a9dc719"
		       "f2ecac4a8e7c4827 5533def5c08788dc 4b47ec81960b25a5 7dba2762f5a07003"
		       "7c50a4883fe902eb cb1574998dd5e8b1 e34ea5aea20bbbef fdb5d6163688e4e1"
		       "bdc9619f12b78d20 e8c073f81da8bbe4 8bde8934bc7186da 9d29d1f670a322bf"
		       "9febca92915e393c 1878895c04b8c365 e4d399ac551a55c5 4264e3fc6176cbcd"
		       "101790863cdab395 74a4dd5c9edd69a0 1df20a10e5abff31 b4e204f5cf7e1dc9"
		       "a27626ec3bf06d28 fad08c10674830d7 abc54772d95ace66 765757340007a353"
		       "63d270f410a6bcf2 0f2ca54dfdb00d9b e8fa7ea5b79bf818 2f16b95f9850ce4c"
		       "acff1e66bec202b5 7b85b37cdd2c3900 1d2950666368afa2 1de5ce68f54833a8"
		       "8da17b49c4e66243 560ec61a6efd5d3a 2966a76df2dc08c4 e5f02f8b8cd71b90"
		       "4ddd4bfd73a5c848 9b7eb813ca3da6b8 dbea536354e01428 dd6dc42db23257a2"
		       "0e322f685bb82b20 f0edc48351c22b75 e0aa8adc567f172e 654360e094c19754"
		       "2f39965bd9004621 c9ee3297870ed818 f980a71ec4a8f818 1e9be5be1ef6a660"
		       "cbf68637e54b5afa bbc5f9dc61933014 cb52b4d2624a24ac a3c6f5ca80dd5aee"
		       "93d0155af703c0ac a4a9266cd9b56f3f 152fc4fca8e7dce3 21a188682fb36e6f"
		       "7a736fd4e9972a9f 71f11d50c351551e 3c455f1b051befcb c1fd83239b748951"
		       "f7e18c2027627339 712df2772dcd57de 9a15f218e25a4493 ce20d039e2880881"
		       "69445f244f14d56e 6efe9ed005094333 1a4ef297119cf5c0 e21e2bbc535daebf"
		       "3fce3caf9d86b62c 37a4c9bd8991b8ff 01e992f26a77e987 ca8ddf6cf47d47d5"
		       "439eb6622b241172 a8d5a251dcb5d4d2 26a68bef9d2e77df e4db3ebd4342f49b"
		       "ee82b28fc35063e9 36589f86f8ff2db0 f2a7fcbf0d461484 184f64bf18e5bff6"
		       "84545e6112f87662 60987bcfe76bed5a 17dfb88a9b7d7cac cb4283afb4ee21ef"
		       "b43d698c413de813 48309bc1ec10cdb3 3a7e2e4aaed41cfe bf808b08e7f64f8f"
		       "6f250960375c3a3e d0617000ac6e54a6 12727861daf4d893 7ae133a5e99c607e"
		       "09e8097f876ef8cd 75e244b78eaabf83 1db9efd0ba405b52 715825974579a627"
		       "9f7775ab87de6e26 9979530e3fff6d8f f6421ab3ba1ec61b 9ebc1a2a7aa59002"
		       "ac916c26f55bc369 b2e11030f3346548 28285930228ad081 2500c822bd41ead4"
		       "80b530331f8642f2 6d5454fe75cc3870 d807ef92496b27e0 45b3317f10e98533"
		       "59875ec041117f3b b37d88c526ef1a34 2b6ea289fa69bc91 4d8fef84a27329f3"
		       "0a7326c84710f972 5432a525f3bf9af3 d93f9faded5766f9 067a5b1b7a0dac92"
		       "75207b6776c404b1 7801a7372666f153 78cdf91bb4c29d6a cf79eed16918947c"
		       "769283e829ec1e97 cb90630473224d88 95f2a0219d309507 173f42594372696f"
		       "6ef8468b843d4ad5 81ad78c221bbb877 0ca2323858016dc6 f9c311bd451a5b68"
		       "ce23c6feb8c1f543 82a8512d286e6bd5 62ada1c6c8c7c46d 7a9722d7a909b7cc"
		       "fce3258bb37b78c0 d076e4bb587bfe05 95257c988543edeb d2f24f9e124dd0e3"
		       "35ea2add17201df7 f2e68fbcc02da7d4 3b7a9a8f83de7375 be2c61b4c2b872bb"
		       "de25ea659a59b1a6 3cbc9c5efb6c449d 9818245291c6c232 17ae6cb018cdf7a9"
		       "a49240f37a484361 b450ba8fccedd4f4 556ca8423fd1e907 6a876306958ee264"
		       "4646633c2777280a c7a82e441d79b556 c629d7c97b4c7895 4bae0e76cb4ab1b2"
		       "0b51126ac8f125e2 f01c266df31b2ae6 d50eb02f96b39044 81a32254799bc233"
		       "88f7d86b6b60876d 20cf9e8a4468fb3e be4883fb90765a50 5d6ae99827a0ff96"
		       "d5eb284ac7df815c 0fd5aa2bdffa560b dc37beb9a7a6a4e3 fc074a9f812132a8"
		       "6be3a1f73433a198 0a168bbe54910ff5 95a47b6747f43a67 8fe5a7c96e636b4b"
		       "874f348d24b79337 db4315cb10fd0e56 2431511c323353cf 1e59fd5a55357e5f"
		       "6b7cce60f1f8211f d1f5be68f7c8bd70 c29f03c0a6613c64 dd10a65db5e0c546"
		       "f5382403ff8ba36b ad49879231912a4b 219a08a19858b12c 2744fd65603775b5"
		       "6bf4459512e79188 92da55f87d7cc02c 6885c0ec02550b60 9e3fa7d9fb0d13ab"));

  test_xmss_sign(public_seed, secret_seed, 9, 0, UINT64_C(0x29877722d7c079), 0x156,
		 /* The message signed is a fors public key. */
		 SHEX("3961b2cab15e08c633be827744a07f01"),
		 SHEX("1be9523f2c90cd553ef5be5aa1c5c4fa"),
		 SHEX(/* Embedded wots signature. */
		      "e1933de10e3fface 5fb8f8707c35ac13 74dc14ee8518481c 7e63d936ecc62f50"
		      "c7f951b87bc716dc 45e9bcfec6f6d97e 7fafdacb6db05ed3 778f21851f325e25"
		      "470da8dd81c41223 6d66cbee9ffa9c50 b86aa40baf213494 dfacca22aa0fb479"
		      "53928735ca4212cf 53a09ab0335d20a8 e62ede797c8e7493 54d636f15f3150c5"
		      "52797b76c091a41f 949f7fb57b42f744 1cca410264d6421f 4aa2c7e2ff4834a8"
		      "db0e6e7750b2e11f f1c89a42d1fbc271 8358e38325886ad1 2346cd694f9eab73"
		      "46c9a23b5ebe7637 bfd834a412318b01 188b0f29e3bd979f 8ae734acf1563af3"
		      "03d3c095e9eaeba3 5207b9df3acf9ee4 7da5c1e2652f3b86 41698f3d2260591b"
		      "07d00565e5d6be18 36033d2b7ef2c33b dc5cf3bba95b42df 6f73345b835341b2"
		      "50e2862c9f2f9cef 77cfa74cfb04c560 d8a0038c4e96cb0d a2b3e9b2cd3cecf5"
		      "22fda0d67e5f62b2 ee23bd42a61c7da4 8f0ea30b81af7ccb 6bb02cde272d2574"
		      "1325e9d91535615c 0184f2d7f226141d 79b42412721fd345 61d93663650b3c1b"
		      "6901872bc4c0bb15 bcd9038950b7717f 7f448b6126592076 a2bad2d63c55399c"
		      "243fdbdb0c8d676b 2ae455e7f0a9b18d 3fc889c43387f2cb c4dc73d7c85bfab6"
		      "b4b04463a3dd359c 3a8f61bfa6c4b042 4aeba4dd8a95ec12 43b2e36c29f82e1d"
		      "711281599b3e05e7 5492ae3425eaa7f1 4ff8c6a9630bba6e bd236f195269a481"
		      "e87eb3d444825ba4 424ee5b2d9efb595 d5a338f4c253f79d e9d04535206ca6db"
		      "c2d4c9a1ec20849b 0db3fbe10c1446d5"
		      /* Auth path aka inclusion proof. */
		      "612d5bac915a3996 2cdbcacee0969dcf 8ecfb830cea2206c 37749c65b8f673db"
		      "090b1e2ade6c2a2f 349b5915103a3ac7 8482c39e99ffc462 6fb4cf4a116804ab"
		      "9d93d7104660fefa 0753cf875cb22fd6 0e55dc2f303de036 47712b12067a55f7"
		      "a467897bbed0d3a0 9d50e9deaadff78d e9ac65c1fd05d076 10a79c8c465141ad"
		      "65e60340531fab08 f1f433ef823283fe"));

  test_slh_dsa_shake_128s_root (public_seed, secret_seed,
				SHEX("ac524902fc81f503 2bc27b17d9261ebd"));


  /* If we mark the private key for the top-level
     slh_dsa_shake_128s_sign call as undefined, then we get valgrind
     errors from the branches in wots_chain, when signing the derived
     public keys. We'd need further instrumentation to make such a
     test work. */
  if (test_side_channel)
    return;

  /* Test vector from
     https://github.com/smuellerDD/leancrypto/blob/master/slh-dsa/tests/sphincs_tester_vectors_shake_128s.h */
  test_slh_dsa_shake_128s(SHEX("B505D7CFAD1B4974 99323C8686325E47"
			       "AC524902FC81F503 2BC27B17D9261EBD"),
			  SHEX("7C9935A0B07694AA 0C6D10E4DB6B1ADD"
			       "2FD81A25CCB14803 2DCD739936737F2D"),
			  SHEX("D81C4D8D734FCBFB EADE3D3F8A039FAA"
			       "2A2C9957E835AD55 B22E75BF57BB556A"
			       "C8"),
			  SHEX("373c73945bffbe75 0f03acb9e5c6bfc4 6a18de32418675a0 b92e0309a54f6cd4"
			       "671db880b257ac96 f4af40eb80575aa2 f4fbcbaa9578a6f2 60882cf0ad94f907"
			       "310bfc029afeba08 10dd859c275b5b28 ed08b97031cce361 ce4888fede45215f"
			       "c2b59b75bfb82df7 0b21fe09f2a21ccc 2bfce1ceef91ff77 da219eedefc16f3a"
			       "4b94fb931062b24c c1c7517d29756e81 148f9071a81b1980 5694fcc93edf05f4"
			       "c804d3d99c5b9d3e d25e9999003d36db 32153553a81f9d0c 80b78cb4a0003998"
			       "5e5e2ee71bf4b8e9 e4abd07a9c49d0b5 310ac46f2a4af89f c52d4eb41cfff58d"
			       "5369c6517fa11745 1eb4439a874fbb96 daffd185ef27cc65 d3d67f06e7a5eed2"
			       "32913e61ecce42b5 623a156cbf16ed9f 7a280403a247b098 380567ab9309b0fa"
			       "8d4c3ed2d646344f c6a4bf1bdc68d161 9f29737a4d2597e2 b421f611b7bf464a"
			       "6824045f9c058b5e 39a591a40af4da11 75874e7ee287fd4b 1cf29d35a2652c42"
			       "663be06b06df5b22 c484989916feb133 3ccaa2e20d389baa f62de05537cb4f63"
			       "e1bc00e1d827d01b 6358c19f677126b5 1a7e5e6be0180009 deec05f4d66ebdd7"
			       "8e576912c869b592 0ffbcf25e37f8eb6 dbcae3e8a2c97e73 1860190a2f7ef9a7"
			       "8bbd5a36d7516882 7b299ef7580eac6f 90c6cc1ea68f27c3 d2835622d7677618"
			       "75d9f385c4d6fd43 48436cbea77f39b8 0f16196dab3030e9 cb61e15511b65016"
			       "f4115fa3921385fe 203ec3127531e2ca 26616e278e4f5f70 e621fe5a18353fac"
			       "ce683794004557d5 732391afc53cce77 44ca92811baeb824 e5e46dea2720d68b"
			       "1910307b967059be 7583adc9ac8d425f 998861e765cd8ec1 c474fb3f631cafc0"
			       "90b202f9b9c1596c 5ef21a2985642bcb 36056aea784226a8 a490a4e4ef9783a8"
			       "fb77eb2f4e10e3f6 d0a62a6a6062f6a8 991d5ecbddb74f86 a02c54258e29d10a"
			       "86b756885721175d ecf0077a66f4b3fc 592ba9fa5e3a0fa7 1eb808e5e944ffa2"
			       "5e377cfb8782b2fb f93c5abc88fe8b83 1148088836aad27c ccb8aff0bb9e4308"
			       "f485c3473824ffb0 30e51cf613671dec 7bcb4dbb62c7224f 2dc63fc2157bc59a"
			       "b1242f460f8ad6a2 3c20fd27e280776f a180b31baf6e204a bad44cf1a645ab8a"
			       "cb811c0f08a0b019 45116e05a5bda4e2 de18d7047157d2b4 b76805ac222a8e75"
			       "745dc2443d14a43e 21dfb39ebb6c14fe 42b002b62cfe4808 ce0a6c3ff2401fd4"
			       "8c047e654ac98dba a5e0f621620c34af 63cdfeed579b7c04 dc2e3288ca684081"
			       "4ed30399c25c840a 0dd471d46760e40e 8448529112e68c54 65084b1be7eb3818"
			       "c00c3fb3365b094d f1b03d4f11887868 6bd49fa6618a0a42 bace7865caafa963"
			       "34afbd686ae8e957 ec206aa03de1b2ab e0ef1e933eb8cf15 7a64c52b285e97af"
			       "9722ef435dc8f982 b44194937d6826f0 a1ade35632e03bdf eb1bfad881a34fbc"
			       "809354630edc6437 e947c965b128893c 7fb7e2e2e2db7ce2 7b8a54fb95b56ccf"
			       "96f901544d056960 ec9c8bab5ffac52c b6f98b9431a3770f 7053457993351c19"
			       "cce355ab749e32d2 a2c56910e9475811 8835465f31eae203 4d3728e376f193ab"
			       "b567ed28dfea4cd7 efdb1f35847473db 9483c8344904fe50 95154c9f56446440"
			       "815e6669c7fb8ac3 87af71803ef5a616 74112b8d4ea8137b aba080b98956dcf1"
			       "9d19558acd69c715 04bbd291410ea1cc 5a8b62f025bbdef1 39f8cb7f65594cd7"
			       "80f6ba44c839bda6 755fc4a2ba3c925d 7fa1f05b954171b1 6d5ffb607c643081"
			       "0be371dd52f3d888 aba9038f2320732f 7403bd541a7eb7af 93703dea45e02946"
			       "8f57ee3bfd74a67c 4feaecae0c1786b9 266e52674de811f5 6f657b1bdcd5aefb"
			       "30f924c2495357bb 70037725e821a5f7 7690d21eecc5b77a 1777123cff4c0b15"
			       "52f1dbe08260bbed 0d5ac3cfa1450030 6b9564de6135d1d4 1c52866d0acabb22"
			       "157c712a37972b47 15a5459c4f30fef5 5a2a396a9d78dbfc c06ad406f4cfe1b1"
			       "120537abc51241b4 59153167bea44afc 9d7efd91341c7fd5 5017effa7c687f67"
			       "ef4ad278c1829b7c 073784ddd0d64fbd 90869a3724ba1d1c a05bde1c669fca54"
			       "8b85d8bd574d0703 c42fc2c1180aa171 93faf9e55482558f 54905b9c9b98d99c"
			       "001842df9c942d4c 36bbd4e60d571b19 84421b90931b916e 6f57a17781b30db7"
			       "f09a6105fab7f1f0 d6dfc72eebc30a1c 26d7387f404e0c12 9168e7e246a73940"
			       "8c0eb2ceaa07c48a 0a3cef36ee60535d 2ad119dc24285323 00ff025fd956e621"
			       "9ca1e2df05bb00f2 75477db356190d84 b14f3e77e9c669df 825885acee76ab11"
			       "518bea9753fa0504 7f1828cc1ebc207a 796d40490ebb4934 06acb8a8f90081dc"
			       "d28c5bcf4f7d0a22 38eb1f6ebbbe02ec 17808173042fd209 bd81ce50cc245c25"
			       "e7ae1990db628667 c02599acf12085d8 484dbc84ed0f8908 13e4e9232db6cc1d"
			       "6d028881abc8ccae 1a7216a5e97cd4fd 848ea80984e0bd4a 8e5ad4e23e37b61b"
			       "626dad1d36ba7cb1 79b17b1f417f1b04 a16e315f2405526b 04b40c9375acbd27"
			       "1ce0a02dcb480adb 1fdbfa1accc079c2 51dbdd354e0b405e daaa87d0a2bb6902"
			       "d12f3ade5f8588e2 02218b859ad5eadc 5f186f15a87cff3a 461692ffe0921073"
			       "6ee053b200fadf4e d6c5d2ec302a86e8 935afb31780b035c e49154dd9decc7e1"
			       "55b8b27a8046caf9 3cda59190128fd74 d5cc56046682b4dd 3824ed44c91accb9"
			       "67ac2304b682c477 0d8bfa0cce4b791a 04b7b53c3369e463 636d6908bacc2e40"
			       "3a0422e3cde7374d 1c5a6afe599b341a 7db6bd2dbddbfb5c f9c85ab10637f32d"
			       "26620bbee639fc57 6819baa7a0552436 99a9294917af1a5f cc14ac5d04229b6b"
			       "0b115d1f9dd983a4 a5117f9549ecd7e4 2db3b8cc33d767c0 9283f258fa845c43"
			       "419bf7b437cb0ac0 3d0b255dce3ac86f 495b2e1c8deb916c 9afe1564181a201f"
			       "dfc5495585ab00f3 f344cf5e1e510a53 b183d1100b347a15 e6df9a57d9702de8"
			       "46c5a5cb55410139 433ef287786cb596 d6738995f23b6332 1b07e8f7848f5315"
			       "8e5f2b260e797dc6 cff9812e5b8d39ae 2233d87bf240dbeb 54c137b21ab8f51a"
			       "859dd2f8187e04d7 6612f743a1a8d3a2 409e6375e30e8a28 7a07f65415b82588"
			       "10f27f7c2bb5cf65 1860fb1b26a4f35c e4870226d3dbcd5f 54f603e7c927c73c"
			       "2604fab51c6c2272 0315f70c4cd14f74 44a1a4c9be0511e6 8c2247f22e0051bc"
			       "132f0dcb0cc387e4 966bdc386cc7623e 8a384b82c7e6406d 61e4bf3532c7a755"
			       "cb58a80d8ef30412 f8691a8ac779ae54 81daafc0e26b4bfc 7eee57c75c52b8f3"
			       "8ca6d97bdcdbb366 3a80a5ecb4e5f5a1 4b5aff54897f09c7 0e926c264bd72851"
			       "826c3772c2a24206 4a0a0b4b38792890 62efdc6fbb20984e 7297e779298c7dff"
			       "91898d646083325e 9cb981eba5a3515c 4aa26069979e3cfd d5da15be8e8615dd"
			       "0410d914312a6b1f 6844d42c43b9f65b a93746903f52cd27 c0d4482c920a0bd1"
			       "942189359c6cc639 b9e899084962fd78 f219ab8dc39a226e 4701ceee6a689343"
			       "836a7a4b2b72a874 2cbc7a10e34860c5 aa8b5936db7ec269 b57208cf47f02f2e"
			       "5d06b978b3445ae0 71d9fd313375199c 618efcdd1f66dc29 9c781efee5caf209"
			       "89f3ae515824f77d edc21edfaf4cafef 79e83523cdbd118b 04ee628dd0eedff0"
			       "f771c09ea8930dc4 d4abfa4748a568ba 5d9ba5ec63991e9a 5cd0fdd560a2c99e"
			       "cf5d44fe62aef6c7 1c07ce5e8dc72caf 653817bc4819ba54 4d713e2be7028fea"
			       "afc3455fab2bde23 52b8ae6417a3b131 b1fc0922d5751498 48b62a4a1a9b26f5"
			       "c12d7c68e004e445 73ef48ab562d0072 e04202ea1f56eb1a 0cb8e2306b87fbed"
			       "bd5ac23cf212c620 68afa2fd30358774 99309658594e947f 26d81a8edad1413b"
			       "792a5c35d5680ccd 6f2eb81e412dbba1 c750ad2ff6ab3f93 5c8d18e8759c0594"
			       "39d9efb1a6f1d011 6ec5e35e83c4f4e7 7d3cf696ffc74e0d 07e8d6347369b63c"
			       "81cdbed36dcb07ef 77f737657e278a73 39e55cb7274a019d 39d92b651e09c0d5"
			       "d654d4ad44291a36 b42e0908505c4de8 7d640a00c56d5abc 2a994701b2f0d2e9"
			       "a4b1a030476e3506 8850326022e5edc4 d621de04dee0eac6 de4e51e2b2f6fe7e"
			       "07b464baad97a19b ceaf083ec5152e9f a0da7ecfb82caaf2 f163c3709f6c86e7"
			       "cbd5d338b56a284d c8c8497e5b5d9206 beb8664c88f84280 8f19f6425c86d32f"
			       "1af3277e9783c5e9 ca0ba31e0efa3017 5ee4422efb4acc82 0998a4e19e0f124d"
			       "04529a95a7c4c880 a1b468e5ee8541d9 9d07cb2a46c5f21e f67dcfa5858d41e1"
			       "b140749b04db5433 4e95a4c3a9385d2b fd53685c859e31a1 904f4b3fbbc5a74a"
			       "d0d5e222d4a5224c 4f5605851603911d 2f908d20d40d8b37 106ae45c381f6aa2"
			       "d5c89c7148d80943 1fd29e6a85ce6be9 eee6602372e504aa 4487d1c6023d6b3d"
			       "2f79718dd86ffb8a d2edff96f28b4a95 d5107430372d59e1 afdf7b32bcab8648"
			       "ea8c2f4addb40d95 91cf58fd95d04c01 557e6d8b526efed0 cb5607f5b334529f"
			       "acc4c52bc7e4f238 c9a0461ca9580df2 a46c91a74bdb2149 aa207f60d28abab0"
			       "d18970af2fb6b3c1 64af229faa6884a2 1f645eae16091f48 f859f96ffb169886"
			       "ab7c3b8f73543dbd b09ed00db65dd6ad c06c242a5d8373cd f0a93be9bbbd63e2"
			       "99084a5cd3ad6a77 f7bfa5b09136abe6 934420b5fa5f7bbb 165ed99c472c136c"
			       "1d679150a9623626 1a3b9bb8e581724a ea2208ac72a8160e 672510b73d9b386c"
			       "ec83dc2cba9c29f7 fa997748de75bd9d 0c21e2256175381a 45b03b3dacbc29b7"
			       "d5494fdb921ae780 4d18dd023b78e8f7 df965b1fe3f36033 e8d20f3a436adc1c"
			       "5860951da02481f9 c8fa05bebd131b3a 4207be917e217660 ba91ae83a35d7741"
			       "0b1c0a3cc8652329 4929924b95e8021a 0d8bb5af959a54c6 63b9b6d5149ccb6b"
			       "b0e5280adecdce1b 7229e817ad6ba08c 467bd3f9ed6537f5 e7e8c949d2d4bb7e"
			       "3f0d4b42adf32c67 42b7666bf0876e18 51dbf5dae1eb4210 f115e6a5afb2e5b0"
			       "5db56aa0fd56f752 4f1da655a7851734 2d55900dae39c326 1e400de0abd76eb3"
			       "c173406514da6fa5 4d81838a0e1761cc db1a7d02416dde89 10492551d64fc331"
			       "0f89627657b88159 2a3a26b466f6dcc6 6ceed88dddb3ba60 3ebb4055f6743887"
			       "7c0bb6b011975c6d b15a896b13d91f53 d2fad4eb9eea5c21 2e2784fc30992d45"
			       "d9e43e2201814159 c87058d35d76137e 3ab78d93be20e655 d6061d504f9670f4"
			       "2da359d408f7b791 bbe6bd509cfd7b53 9b382ce7a356e8f0 fe54a907560f75d2"
			       "ad1f59b83fbda0db 4a1cc4d18ea6cfeb ae7bd14fb6c7f8a7 72125032f9c3eaa1"
			       "ba175042ca35ea0b d483992479450e37 b52454e44a85af85 3907c50f1ebbd69f"
			       "2caacf912fecd431 7ce04b5a28664721 6686c9318c2278fa 45343eeef2cf4dfb"
			       "5eaecb0aa20422b9 715960b9c7ea0b13 3330c62ef1f615d9 2d283c95102a79ef"
			       "09d152924ce15c5b 1aa893b9be2d8427 89b1b29e2d05fb4d d5a2b486d0be0696"
			       "d73b6925107ea8ab d2a71d0dad3d7a76 71579004a46afdda eb08a357271405d4"
			       "e183e790d5d2f854 8d8da51e28243c25 4e0e460079dea68f d4410d50cbf0e9bb"
			       "f96d3532baab2bad 5e81f359c5839526 71e90601e0bdc325 740a42f666c6ee86"
			       "8b68e1298e625f68 6ef0eeee17c45a81 59ab13c794cf224f 4a2cd0efc5ea1a3a"
			       "368a4e6cc80ad464 6cb3f6dcf45ecd23 7a6ba15df7193b91 41d2520d77bae9d7"
			       "d8507c3694463456 8005bb5df947096e 548f88ce8515a0d5 f3070a9ad32dd656"
			       "36e1a4e91caffc00 8bed45094e6f664c 3b14461277653538 ece57b5705d66437"
			       "67bb2b0c49530cf7 d142d0d14f00c6de e3e134292dc0ab81 a4d675a041fd9d0d"
			       "41dbcfd9d234a145 7a7fe343a6bdefb4 cb1a48fc1aaad3bb adf0661b6f15a291"
			       "ff11666a95be8b7e c55a5be147dfd7ea 639e95353097ad58 df3611890367b580"
			       "96a2ffa5bc5a2bab da709fbf59f110e1 1573c6ebb9c68359 5ea71f53901ded68"
			       "1517d7acd58db8d1 417d615313a32daf 4dda30f5f0257b37 29afb59c8f95e3a9"
			       "7c8d35b09d212bbd 94b49abdf6e50b6a 57d6a488e4f9446b 96a67b0357764b01"
			       "ff38be4744f692ab 9fba6f8bb24c5318 75d7f146fb46b46e 0d6021a0f9ee1940"
			       "928d05dccdb48f79 26ed0d0b01749ddd 301958d08524f924 5f7951665627ee19"
			       "fe9ef4a1f884a311 fa7d3b398a0d0faa c9e18caf850f20f9 3a1f1c6288477192"
			       "1ef22596705aa9e3 b86df8e0b1ce071a 79cb80f8674fd162 bbf128d897892820"
			       "9d02c68998669edb 100131822dd455fc ff708ace30e3dc80 4efbd9d2a001da20"
			       "e4d17cfe3206b92d 25edda5fcaa37395 a4dbb15383bccba1 0ba80f8fd66c14da"
			       "2fbfd1850ccca1c6 617b0553634a6e9e 7094d18f385bcce2 16fee3e2f4d827e4"
			       "563393018fa1b350 341016e7ba78a6b1 5ae5b0685417af24 22a5efe51d46dccb"
			       "236dbab0dd0e13d6 21231632396abae7 b737106146a00d50 965db987fa75371b"
			       "e865134504c7f64d af9b188eb4ac894f 29c4e5568688913f 362aefe8fbcf2dd2"
			       "ea12f3ea4e1de149 55d2dacc6ad5b4e5 d00f78161a67898f 96b64cf5f21a1713"
			       "38a94284a2b180cc 5e2b2b03ee6e6d58 bf3a49558aa87a9b af0696bb28c96fca"
			       "9e4a4321e13b1ecd 7b172d27d2e1007f 3aefc189d51b23e7 573ec280c5131542"
			       "071c27aa22f57034 5f3292be4dab04b1 a9c5dab11bee3e65 78768b6f1fadd532"
			       "7cc09cbb4cd36063 aecb4fe42f3b4a84 de7ad0d2b1d72ee6 245e82ab60cefab2"
			       "0e779148280502df bf6748d72adb725e 4836c68f08cd83ec 0573078320c936d5"
			       "6b0edf049dfa8d2d 684078a41e80a3ba 5246293063c86a2e 4c32963199c056b4"
			       "f7780079208306e3 7c6b4dbb70b1e186 be3517a797869e09 577c1449412d87fc"
			       "31f901ff65ea3400 99d7a8bbfdc8c441 78a113177a135c10 6dc898a7b0a88335"
			       "dcd1019360095b8e 9239bea63ca9b9e4 f097200e23d86064 99f7748eebb4b598"
			       "4a3a872f154ad47b 04c480c14d46e5fe 01e75a53329cb6a0 2b973fbd5b0dfb92"
			       "fd3572825cb170ce ab96955a7df816b8 fbe549572a5ef399 26c207d78deb6ab7"
			       "2a5ca66e77ccbb5f 758f29b038ab1909 5ca572dc1a13101e 633819b29f8b6a4b"
			       "bafffcd390fb8ef2 351522e72c9f09b8 2df20d11435996df dcf2f3a5595217b5"
			       "f02721c9d515bdd4 d71abadca7428f12 cccaa766255da4df 18c9dcbaa4dc4150"
			       "cf6c45a41664a642 74fc66929bd1ce07 058520c295ad5db1 1ebe965aea245b56"
			       "74fa1390a4acdca4 507f4f509c0899f1 bd46fc3aa1f7f43e 882385437c2d92e6"
			       "43b222f1de3733d2 ff5b246aa379cb7b 2309ff16d53aea18 435accd18c86c740"
			       "9ab1fa1d20a62bc0 73e47aa944f63175 5deac3cd3fc3f552 a7d043e07a337e21"
			       "ac1343a0100d8e74 386927b6335125ba c5809e09fc25810d 949d5bf4e6ef4af0"
			       "08a33c4aa136f700 bbc39b7e7130e73b 4aab82f0f8e2cd4a 4160882684ddec0e"
			       "1d2697bb8bd999ec 04bf7eede896d4a0 89179356adaee823 398aa1af27c65e61"
			       "dd5a47c1aa7778c3 3ed0726710eb053e 583988d8c1347b30 358f7df216c692fb"
			       "e67ec05087840869 7d37e0ed298f357b 33f0dae67e665bcd a85fc71cf91e155e"
			       "f412378d81fc6a77 2a382318af8964c3 2a3337de70b4ae7e 8fa50f2246f79de3"
			       "4401e734750ca311 091a621abc1f7819 f74e16dcfb5aa398 248f2f4b5795eee8"
			       "8fd6757314d79b76 b85685448e6ac531 2a321752ddbaa0d6 e33b7bd9c6190df2"
			       "c0495a632a364655 5faeaa9d2bd04d66 bee9a700af0b75fd 3b7fa4944ad43d9d"
			       "cc291e493297cb01 6ab1ee25e1613165 1106f954f576d47b a14d6239d8699882"
			       "e222956a2b53f470 4d38de97acaa75c9 2c6097384d8a70d0 b17dc04659ed206c"
			       "604d60f0463f4714 a43a53f0b5a02685 f1751faf492a48a7 e07e6b9946ad28b4"
			       "15502949ac793aab ba8f41e060390732 63878d212a262d49 ec51ff8536aa1c02"
			       "16c54ce2c4f1f7b5 c88bafe62874e4d7 e54b0bf068b714a4 453a509d8909a338"
			       "24425567871a6328 9a418b6f12a7db7a b11d3f98fc4eb2b3 a4b7cb059f8c5140"
			       "d3169fef3f4a8591 398a46db9a246ab8 73ca741436ec0bf7 e84940c594c15c12"
			       "f048e9e22289ab82 808a4d4ab459254c ee928e01502b1f30 872ef8bcc0d28f35"
			       "c62460fb2cf5840b a160dcf1dcc87282 292cf70f662f9682 2efe7794181d67c1"
			       "86fc38145c7e8170 eebdfa9856483b73 417c6ae5e035972f 6aee1dcad230d14f"
			       "d311e68a931d9202 f52ea2bcf2d85f61 8ee90e1bad0df934 b4ee13faef044493"
			       "8684f7ecca17c19b b17787e88f7db0f9 bc00bc22f4aa8a02 358d46ead5ae4f5c"
			       "06d1815662f7adf2 dd598acd1d52d83e e995d6273fae0c34 3388199eefe80fb6"
			       "9689f4ccea58044c a02702fa6c188e6f 572f699a067d1ef8 2e41386f54d90b9c"
			       "94a6586fde4df772 2e04de90c10c2dd1 09d5f2583c42eaaa 123e8b47b9513845"
			       "48407df213b95965 6bb00b50b71cf2f7 eecfa6a00d3e364f f3e08a765024b54b"
			       "c12491bbc6bc825f 8530528a11209560 e5bd3edb5499009d 869d086123c2f05f"
			       "40eac28946d0dfb7 68f5e01cbf42dca4 cccad733c444f533 902019c33af6d535"
			       "6690c6bbb4116db5 d25576cb2ff56289 f5b238b5ba738b38 498b5cd67c5394f7"
			       "4fc9fdb77b71b0ae 322bed1fc8687d1d f7e987e2154615e2 c26c2d94d337bb9f"
			       "77cc9772343f480a 07f13b455392dc26 436efe56ac1ad226 a98ec9b4fd2f5e37"
			       "e42c93c0da8c6911 7b67627c0fef6fe4 131186e7a517289e 2b46e7b2405e9c9f"
			       "d47cb9f4d6772722 5206a133aa154762 918618dbc8016c5f 89d723800c01c5d9"
			       "98b7fb5779a687ba 0511432eae24d16a f333e88f7f18b173 af80567847a609d8"
			       "68967df6b1e68f64 9fdde21a141235ea e6905787c0ee5c79 ff52bd6259f055a5"
			       "cc457b5624094d20 4b3240a56040b9b6 14145f43d467d26e 5f74b85d8986b169"
			       "4dc8e20d2ddd600e 60e576d148af560a 4a72ce4b968672e7 1373abf6c0f47569"
			       "0c3446f9109b3109 501b5776e4df13a2 48b344fb9f416d4c b5e38cd44315011b"
			       "fa0a96eb86537a4f 0634dbbe42050cd7 430f630f87bbb958 beffe476ad2dda10"
			       "5856c24befa48154 36d46395faa2797c c3ed908dbd2c9dd1 053d2f7926d26d67"
			       "a09e0147e261e2b0 3864350945652e0d 960631d360916e6a b61a5c9d3459dbb3"
			       "820212e5ef3241ab 5de63ea4150e4d7c bdfdf071addda34a 4bc53a7fcd169821"
			       "0f9c18c4fa4a36b0 e6b61cb3720d3fab b913c337f9294afd 2bf279322f15344b"
			       "2365893fdc31cc4e a8b87fa582d5a074 34f7fb57df95c706 f508826d90fa3bcd"
			       "af75ff59a7fff497 432c32f16225319a abdcf1f6d174fe58 4ad2697a8d070423"
			       "adaa1f5662b97a08 001cd48c33e34e8d 48a2779df70902cd ad2ecfa26d94d3f4"
			       "1f9e937f71f6f2ce ab1fa5aefe5813b1 1a81df48971c7e0f 23e68437008ba0c4"
			       "eec536d4a090e3a2 2cc15a726299b01c 236a1293084a3ccd 22bc2f2f46f45817"
			       "29e55d822b34b7c9 b7a0d4714ad72209 f1f81af845683a04 2c6e977e45e9cf5f"
			       "1030262aebfb7c76 04d3eae79300fc18 eb9bae0c1db704e8 736c225c03a4db78"
			       "b346a1d016d658a6 98291dc838142838 6cb4e164a4ad7493 b2a76b436cf48e07"
			       "1c637107300e294f c61b660791a6ce2e 99fedde9cfa1ac62 91c9bcb9f14e8aba"
			       "85e898b532a3593e 555395011e8876d2 38caa1848e232ff5 74e50c7c55f6a643"
			       "3a0f9eac55f3f93f 4ac293109f3c1691 faad822a2ad13c4c 8d4817280df581d7"
			       "7b75ff33a8157c8f 6804c3156bf2898e 881a4733a695f622 24865f354a3cb960"
			       "e27cbe33b355c770 650df31567e58fc5 f2fdcca4dd6baba1 1b9fce458156cefc"
			       "bbfe83192484a292 7a41835cb120d779 fb9ddd676a6f3071 0ae18443b759c8ed"
			       "4977675b90e465b3 3eb76d9db8d5dc1f fd1e6f1ea0474e25 13be36a5bf36b4c4"
			       "690e16fea2a89981 68e3b6473fc5d078 700d3dcfea0612ea 8802d6d214f03d69"
			       "ecad474084721d08 96008adb378d9a4f 09a895e4e2062ef4 571c8f88b6b0167a"
			       "3577652a9c5117c9 0dbbb81512ae7586 c660034831dacc7e 6d807af3a397a442"
			       "e2d61faafd2eda60 61b9506cf0252fa4 36f1eb5d35e96f4e ae80376a42073e1d"
			       "1a85dfdf086a4bf7 62b74d3d4e667402 ee5f59d36c7ac624 87a65de64502751c"
			       "f6fe941e20ac694d 70a853f9869b41cf b46b2869878fd260 498f6a3ff2156144"
			       "c63585772e402fde 2eef7466931514ac 22d707bf6b4f118e 7bd9fe13e8b90363"
			       "96ecc3127623e13f b612f9c4d60700c2 9b802fd741bb99c6 357f15f760826fb8"
			       "226f51a3f2278147 2def7d6f707e753b 171a496e6ce99c64 da1ee01ae949394d"
			       "eda4f3dbe8980338 bcf150c839ffb4df 3043d1392f53f9d5 e9d571774b0efbc6"
			       "09ea772fd481dfa3 93b73e1035532801 455da7d830901a1d 2502885cd6d74b9a"
			       "2c2dedaf9a9edd43 a021def1aa51333a 02e837c01da65f6b fa45dc2abcd2c0bd"
			       "84db2d91b6d6e6c5 673f09175050cf70 60b505a03db18f49 29c1d4eba35e9694"
			       "641cbcf58050709f 13272565113f1e8c d904aa967f0f7855 0dde0cf6db44fcf6"
			       "87bbac7b39a4e21f 36513c12d761bb7c e663362b60f4bb4a 5e9a1ebb5d057224"
			       "5c563f7528aa5d86 f6eadbf5f62ef61a 349125587bb444fb 98dcfeb5e54981ce"
			       "4bf11f1b55be0bbd b609e57f0a5b1a78 2ac830f31db648c0 d632d20daaf84fb7"
			       "1a02467612630d26 3dc0dfd65943f7ce 95c3f781c959485a 0ff28a4810ba87d0"
			       "b85be2499ca35f7c 099f23f2300b0f26 eaa0894510d28bd6 7beb619086cb61b6"
			       "ef0eea3cc71e6ed0 743b7ac3f9d219de 6886f209d134355d d1f7125e88c25972"
			       "9d0a0b3f633707bc 02843a8e259fa9c4 e6ab58d9c9bc8e8c 0504010d5e2ac224"
			       "0bc4c1e5eb15ecb4 2875fff48bbf182e a8ff1041cdc59c8a 506471f66ca8a713"
			       "a27a8aff707361b7 632b4250ca3b32e0 69def84ada576a1b cea10c1398a66361"
			       "cb4f96de45be2454 db7ee6975e47ae95 222dba6a40683225 4e1f05a4d3db0a7e"
			       "17061b18213d6bbd c66bd61b29d1ea53"));
  /* Test vector from
     https://github.com/smuellerDD/leancrypto/blob/master/slh-dsa/tests/sphincs_tester_vectors_shake_128f.h */
  test_slh_dsa_shake_128f(SHEX("B505D7CFAD1B4974 99323C8686325E47"
			       "AFBC007BA1E2B4A1 38F03AA9A6195AC8"),
			  SHEX("7C9935A0B07694AA 0C6D10E4DB6B1ADD"
			       "2FD81A25CCB14803 2DCD739936737F2D"),
			  SHEX("D81C4D8D734FCBFB EADE3D3F8A039FAA"
			       "2A2C9957E835AD55 B22E75BF57BB556A"
			       "C8"),
			  SHEX("373c73945bffbe75 0f03acb9e5c6bfc4 6d797df8895e06ed e918aa6c036d4318"
			       "37a89af35fa93b1d 174d1a2a580ebf09 bce3ce5fc3d9b7e7 ea978266a5ed558d"
			       "b88812db900001f0 54ca435f84e66c7d 266c9f7573081488 638b3187d11cce09"
			       "ad1643b08dadc8a5 94093e9942b788d2 ec9877c43783e47c a6f82f63764b7559"
			       "ae96d4fb8afac807 b29f61fef83efc5c 986b100de9f380e6 8e927530f6df7e99"
			       "f0dd7f805c32ecb3 01e396328a4bb913 af856bfcbb7e685f 5e8237e9a2c3c8a9"
			       "550afa9171705ef9 7239f1e5ed9ca259 db5a807f5a662212 aeb7c6c255a4b4a4"
			       "daa30596bdf3a47b fec5ed2a1fc3b936 5e35f2f0c98cc290 4d9df60d117adc9a"
			       "3debdfaf9e2cf950 c8fcf81822bf0516 fa4e1d219b9350d7 01e1be5fc400eb9b"
			       "fc9618ad97b2e705 f13d25defbae8722 729df3fc9a85c252 b584a94215381e4d"
			       "04e35b5a476ee340 63496da221a67428 9b30957cc90912e0 9f116f931c58a0de"
			       "df0260e09a5be963 8f20573f7ecc8b1d 040f443f6079450d dd198f3a92ceb92b"
			       "7b389bfedeff041b ced0f72647add382 c8fa6dc3f4993129 c601393da193617b"
			       "35f32ded870c4ed6 3cd01ae1755d2787 86d3fda4958a010f 2a6e0dc2c8e90f33"
			       "678d0c0a957ffcea e196c221cb3d33a4 0bb6f3d4a3f23f10 33d8dbb2fc5658dd"
			       "88621b970aa50e05 68e01f844172ab78 a3a6d2ddda40a39c 53560ccabcaa0a83"
			       "0c1a72de0599750f da0a823a354c81e3 a883fcae221b89c5 a1d0f1ec79ec5b8e"
			       "8530fae3170267e7 6ff2500cbe04196a 8aa20e5061d68478 e2d4a0469782e8d9"
			       "a8555435e4edd8c8 f4b82432b7ff638d 9831d636f9e337e0 fbb8ac745aab7f38"
			       "5a56ee06891e3adf 98c6a470c0b65659 58a700bc6df02f3c d6c629c08210621d"
			       "a76e8d13129c5649 3abd6ca9133a6aa8 a07baaef3b468bc3 f6994ef9cb18dd95"
			       "787c92811495f1ab ae6eb713ad64a1cd b0cb0b6e6026c382 720c3233f58d17c8"
			       "e0959035dd82bcb6 cd9e812cd95ed268 33c50335ffc2d762 f6a486b6154158f2"
			       "58b58991a847c622 9688f45ecc9031a2 d6a06a3c898bcc54 8a4cdab2064e3083"
			       "a888024812555029 223106aad833e285 70d47aafb04f59cd 39d9cae3aeb6d8e0"
			       "79d1f3166dabf784 1fa27df0df53516f ee1529ea1dbd71e9 0aab3d8ad4fe8287"
			       "0f4c5b8e35b9cbc2 4e87791ec2c7bee3 2b3251ab68ab674a 77a78d1acea108b5"
			       "562231dfb6c50a1a 00d8fddccb5e83b5 61b3b5f598fd192e 3c2a130d631192f2"
			       "b931fdb086a41882 911166fd15ca8396 d95277fcfd22bef3 0a2452f31e17ee21"
			       "b0a27e6f63e288b5 b086166c5373a948 640abec8db6b6316 3a802dd30c2e84e8"
			       "c7d6f67eeaef4709 82fdbf75909b1139 b7544d72384ae29f 9ba5b15842ce7d9e"
			       "bacd1331b4b22897 5c615464357b0f90 9799c319e2b0f2fb 087587a600bb6dd0"
			       "185a45cfbcc5e05f 99d830941d5f9c68 91cd491f0efa32ba b6a475c9fdb25e0e"
			       "a5ff01ff795eafc6 cbb408f3d802c887 34030194c110d28d 0886abb0d29629b1"
			       "213e9fdc537c8143 632e2057be16fe0c b6e0c16ced62636b 5fb29fc0464c56e0"
			       "39845faaa1ef9149 629f5784a406aee1 965abb96cc92b1c5 d1b44ba6067e82b3"
			       "faee9a72425dba82 394c960819c866ad 5035375b7f020568 49596f1460954d58"
			       "b4af0362b606c328 149da26213550af7 ee9ce6b70dc62972 528b59a419a8ca33"
			       "162da0dddc90f33a 9f9e8606ff1a6350 5f9eb6aacf043894 ea07f3db1811fcef"
			       "2c4be5593104051b 3b483c070bbf1495 e9aa6103c0271e8d 906643cd5e11ea27"
			       "9f0f1deb96a62106 376c0492d4aa5fa6 1545f75545035691 a4c033fbfc42ba4b"
			       "3a8c67b0bbc4dfe0 1ee49aa8715f5d05 34d730d00cb4dd3b c7d23f1e32f01ae5"
			       "5c9e6f7d5a5fe1d6 e6dd8466ac989af5 2b76e35890c82c07 7a083f05cfc8810c"
			       "70dbd1a5b75edf70 6833edcaa9971b76 8e9b29ecaa1a5e09 ea61ee9ed84cdb13"
			       "5472564f31d69dfb 32d8f1f8702cb027 bf66175a7fa9ba78 1759f210d99c30bf"
			       "ec511abf3ecc6598 42122b55db6d3989 6c4359d7576e83ae ba097ce8c302b8ff"
			       "0638900638d842cf 370e3d6bf29e8157 32cbfb6d3b444ac0 74948d634481f96d"
			       "a8cac548d577e8e5 ad59ed5c93d86d25 0569b3827b354bfb ce07e83a0911e417"
			       "aed9c2fb94e0a9ab 23b826a5b690daf2 57ae14e0af3820c4 87e36322d7a5e310"
			       "46545e97953ef883 f2304f34c555fe4f 224a24698f9f56c3 0ce95597f8c68268"
			       "808de01884101001 95bc46e5ec2641ac a0315f2f72d43ffd 6e4f3803422dd2d4"
			       "8b3592da29de7d98 3539024309acaf6b fcecbc80aeed5ecc 4d8339e9a13be272"
			       "b6301cf593fe86ac d6ba94d87d596b24 4a7b875189486c39 08f344c83f24d701"
			       "2a1918890a3dde78 abbabbec63b97ce7 70311dc46b6b8503 a4bae496101b88cc"
			       "e76cb8d9df99cf45 f89b42716bb07491 34f1643f82485805 dc9c836a79de2682"
			       "4ea02046863a570d 22fef883fe218360 c3a7a597a7bea3b9 5b0ab45dfd9eee87"
			       "8f5c8b17c22b7996 02051193c7a270f9 729ec9ae13d51131 834e3126a6bfd6b2"
			       "11f2434a0bf2baaf 8d63e3fc47b07ca9 5e7f307b13ac7724 41f7a7277e6ea66e"
			       "41e46f543ac8f682 f80900cbbcb5a91f 47c08f88a027fbad 25c186eb8bbd8fd0"
			       "d939694e8c81e5fc fe475adf5868bba3 ada914a96cee5479 d2a5dd6d14fadabc"
			       "20a6b2763b790c03 9578bce010d306f5 89d1684b3f71fb16 e061624ecf094f7d"
			       "04378ca5a32fba8e 117bb733c21c3d4c b7efffdf29a144d2 e6156c09f58b8eed"
			       "de63733e110b0b36 a77c8393d9db84b7 100abb674c0c50f7 3569fdd3fcd0eba6"
			       "1924a93e867fc170 acb866be73ad14b3 42bd698ba5d1213f 2b4917491abf2ef6"
			       "a86d36ea9a87cc14 70de776e2f818332 dcd47f4440f7c818 2f14256df3dc707b"
			       "10b88c9e3d1c1513 d8d9c508072bd5da be232cf19f8c4719 261b2cfb5b3e7680"
			       "211a130afc6e1f8c d61ffa17857136ae 3c91bc273003e37b bbdc2b270842a73d"
			       "67f3e560d0a4277c df77c49997ebc8e5 e37c614ebbd3b97c cada3c3bcf87a38b"
			       "e9eacf31c7c820cc 7289d7f54427a8c0 e42c951988339a5f 90579642a1ecc091"
			       "d8c191526ae1140d d655851a7f01c4a9 78f41d6ade9a78cf 1363a964815ed086"
			       "48c0a5c8d86273b3 7e2935fd27761cfc feb5316fd4902849 acaa9a14bcb05363"
			       "1d97a7b73928300c c06abb288f555659 d283f0f30bd037a9 bcce81b31db323a7"
			       "90392ede4b07b5e8 93a65d8a02b2968a dc9ccfc7b7941dab 6310e997afc7adfb"
			       "c3486a5ff3c5dcbb 61d304950de7b30a 31fbb38e2ecc8560 07d9e3d4e1b234d8"
			       "18cccbbdb3af2015 b779ed69e0ecd8d0 d514c9f0265f250c d5f0c04015e20af7"
			       "161e35c4f094908b 4e340518ba793908 e713f002136b39c4 14a1bcb0b4d08643"
			       "4c9df712d2a4dabf 66a3ad279fb15055 57a4b6633f459290 3d2d110c93f85e18"
			       "b736964bb8292524 49c27419617469fd 91654af55c948948 880cbdfd5c841ba6"
			       "d517460bb07d27c2 3b799c4286c66564 289ff4ba52873912 6ad751f5b5e1ee4d"
			       "43871ec0d98d7a22 c468c7d1e4363b80 aec981364c34781b 709f61eceaa27e10"
			       "d46cfde958411a04 41b614c0170c90d9 382d391d91d78e3e 57d23de844b1f0e3"
			       "0a18f51e463c25c2 2478b61f56fc079f 38a63411b8850230 f6144cf7731cf295"
			       "9b2c142438abb34a d8f7d28e10259125 df9d71022c751729 8ea83bd068c59e33"
			       "16fdb53f402e8d1a 569ac5f073545e4b 972490fb27ba0697 1b273ab1e4a9ac5f"
			       "6cb9453eae431005 a5bdf34891f872f3 c3ea3927fd67f8a4 3f6dece355e67b26"
			       "c22913b657703cb5 0e0bddc604cc9bc1 7c1bf2a09481467d f712d0404cf44a16"
			       "00f77a68fad39460 6b52d5d8f07fa64d a0991fb7a0f7a7e3 d7cde7083f69a641"
			       "7018a10e9319b0db d1fbce53fc2269ca 504b6d2a6a6a8baf 4e85e4e56df2c52a"
			       "aed8dc36936dca55 359ce40d4f155747 cf311fe8a4e2e013 0b87899b3e48bab2"
			       "f56d67c774dde599 5f159c582110cbf6 8644d0cc51068e69 699a0381cc917dd6"
			       "433ef98575ad4662 bc38294685668e2f 74362572b268d31a 39087dc4d487da2e"
			       "65716029ae25274f 6088546882b86b51 2a7e958fd1c6f92a 9fdc44c6200c2c10"
			       "95b88ae0e0dc4d0d 08b417bf3aefc7d0 c7c5cab3066bfec9 07f17b08a81e8afa"
			       "ee34fcfdc5e301d4 4c4eda3e05af5d12 10f15b8de81f244c c468ab8506fb2980"
			       "37500091a52886e0 776928451270e3c9 83ed6f61b7c4f861 f689a72f52607860"
			       "92154f99ccbb5b82 65c7be15dab096e9 7693fe35b2f797e9 2936ec9a9e26fa86"
			       "abf49a2747301244 fb884e679dd970ba 34e3bc035186fb3b 619a60bf6a19bf6c"
			       "4c4c4e2b01c6fa70 c0dab8466c8f41bd 449fb372c52eaf71 b1445e315845cfbd"
			       "696cec5eb9bd4628 2b6ccf2cb43a3b25 1d2ad6249d76f1c9 a0963fda7c520635"
			       "1e57227263658b96 5592aad8ff4c66ec 59288af76e381b1b 9412250862ec3f24"
			       "718acc97c16c44a0 83924e5c9100dcd6 8c780d29c4e0ba42 1c265d0f8715f9da"
			       "3d7ce7645bbd2e47 51d1fe85d76fd522 d621624769fdada1 928f61fa9e5714ea"
			       "1ea5f8d50f6b753c f232045be399ca8c 04069596ba33cf26 92e64b124c74aa3a"
			       "4eab8170d1476d2a 8be18f6dc4352135 da13d3f02b97f7fb 5b90e89c359590ea"
			       "64253db7647a02ca fcfebe03c20a87b6 992e48361f6e514e 640e99449496000b"
			       "084e637d4fc5b948 590febecee89b455 9386f4c17b5f01ad 913e6dfcecce2cc1"
			       "943c231342136c06 39c7686bc6a1d22a 1cc655514800c1c1 80c30f59b5ae14ed"
			       "c614510ce7bb5aa7 9bb35e01889bf8af 804627e7980f3b4a 5bf84af4cdda0444"
			       "a2f82b07c67e9c0c d09ef2cfe8a831a9 9b94b9487a1658f8 cc1d237b2cb71256"
			       "8caa2f8916cc39d7 6ed5e4b2cdeae42a 50c674890384b47d 98fd11049677c984"
			       "8d544e7a03b54c8d a7a46a86ad77eb12 fb932a37dae72036 4d5d688b2eff4ffe"
			       "6467c0fda2003f31 d93fccd02a2db8bf 36c14d2bfe9c9626 19b198f9420aa606"
			       "cfa8bbe63ef333b4 9c89c283ce1ad568 59c5cd0758885f22 23e122e1939503b9"
			       "02bf8ff9625c4430 f9cf55e377258e86 2a7ec3903d84b3a8 cd51588435fc38b7"
			       "1667337792eea9d0 01e2f1f2562f3ef5 375c47f0d079780f 7dbe99b4e7939437"
			       "17564da171027fd8 6b1c9dac0819ae29 9eb53ef03e32a802 64cbedc10fdc2a40"
			       "e7a8ce56ee788b2b cdb676fad13d4b41 f227b47b41d198dc be8a662fcc64a718"
			       "20c8be1036138732 ce9454fd774b9041 0714bc940702f4e2 4faee4f2ffba35b2"
			       "9f8922dabd5e6d46 55758792f60bfe8c 50adb4765f5f3311 911ec61c3ebd1663"
			       "ce79e4262b487a7a 14ef3b21a854a022 177236416765c229 34a3e8234fba3b98"
			       "b36694a2efdb1a00 f56b82f92ddfd310 c2ee5bd148a4fc89 e760ae08cdecca0b"
			       "8b526fe62f5ec793 918b8125a7aa4718 22ce67c0fa1940df 95e004d7446e207b"
			       "75770d19675f4c61 30d87017b0e42570 8ff332430f196d10 c985a28ff17eb5fd"
			       "563cfc2281caa946 8018903630e912a4 4423beb2378655ac a7fded077af2a0f1"
			       "851d552bc6596f36 6dc49501bc082372 698fdc4cd6330a37 e2b4a29a4c191848"
			       "27248b2ca56a1ea9 9a619c886db41f19 928d134cdaa392b5 12aa149ca05fad3c"
			       "f8973185312c529f 9f585201ce8aeef0 6a3b76c548e1ff65 2d8e6de6bf4a4f31"
			       "acfb12aa6b8648cc b9e47a2bde555893 ba96d8a59251ebee 38ddb859808675f4"
			       "8993b354b44872b9 e39cf6e243bfa670 1e9266291cdc1741 f99844ebec232841"
			       "0363105a345e1b19 d04c0952b7d2344b f425dad14631e14f 6a595efdc8da63ec"
			       "66fe90643e85e411 8587534cd6fe9c2d cfc119e8f0c4013f e6a262fc5ce4418b"
			       "d872aff38511b0e5 b4cb452293161fe8 d9adfd9cab8da4bf d3f23027c75b0358"
			       "dacc903d3b4153a1 fd880f439ac1e02d 82ef3c4b06070c35 df253afc2b267a92"
			       "eea2d5111261e3c3 4529d2bcc5f5cc89 2d6596a4ee5b7208 cfb98c9405b94744"
			       "cc7c077a7e22ddc5 281fb0d9b69a0467 4b4f0d6c1a70ccac 0c8a89eb1d04b19c"
			       "074961006b132716 fd55f0b5c9b2303c c663a1235dac9773 073e5e20f9368cd2"
			       "1ad21baeeafa2b27 c35e95499252b339 d82f3142db10e1e6 7add6e0d7ce0372c"
			       "f439fd78904a7e7a c95a0a5c1496edf3 1e3ba67ff8600980 717d999e0ee9e7be"
			       "60a535a21ddd20ac d2eafcd448d82971 e61cffd82217e9f7 281b58a1b8e42ce0"
			       "60d4dee8ca438e46 26fa3f9298e438ae 8157dec5e5979c89 7911db73e85390b3"
			       "af4e5053b316890a 95fb92172c1d02eb 4dba03a26dfd23a6 d557e79e2fab9cf8"
			       "06fff00ac1a517bc 8f8760a93d6421f1 96608fa7107641b7 63ee06d3d097bc1f"
			       "5b86bbe6221fe0df 56efc71dbd7e5918 492ea597322d8b20 e104e821d8a82601"
			       "f2ac6577617411d1 64c8d76be898323a 89523a738276f4da 246b673fa2729568"
			       "ff6fc03328aa2a6e 66aea6fb70afa4f9 62f3c805fd3c66e9 e52afb0d9d7bd476"
			       "38ef68f2b12d6922 a1398cba69383dc9 a32906a0acd4727f bc91fa5456d14319"
			       "57a7f9060359d9f8 87611ee0a6a1eae6 c644240abfea9e02 774317f934d080c4"
			       "fcb98905ff5f9330 bbdde48a32877031 f36bfc66e7caac9a dd5c3d210ebd1382"
			       "97d59bddb605aae0 5310fd7ed728300c 8e3c8427800019c0 cdcf604c4a5f07c6"
			       "b01c39543ae68155 8082762a005b3680 81a248703f872c2a dd773a701418f645"
			       "4250663407c0dbec f336048721a72bb1 3a5076923b16437b 18a69065d1b38565"
			       "b95b181abf13be0d 7239fd3c39f083ed 186e3bbdd5441e1e 11fb70ce58a2a792"
			       "a66c2af6fad18a58 a9c56729901f9cec 45c3203932d5dacd 66e96d623e4701dc"
			       "1edb43f2267b5cb4 a438e3e47622ea7d a841c9ba6bc54b5e 83e7871ec89a828b"
			       "4d65d0f26a0e9b7d cf880f28ddc1d159 454559e1385565ca 3ab6633cb04ebe92"
			       "c484ce9278800449 7d74bebcfea361d2 f3286565b6e33591 79eef768c859379b"
			       "e5cc3903dfc9ed77 3f9973fae7cb311b b907726e02acca9e 51cd4f4de0caf25e"
			       "14c881899475354e 8678ac94f73aa3e1 1a27bd9367e531a7 dc0369ecc1b3e094"
			       "eaae23f342942ae0 9e39c0bbf088e260 e923d6489f6fb8f8 36fbdbd9db7d3adf"
			       "8a74407516a61cc4 998a6c14e54c556a 8995d630480e9cd4 d616626364444fd7"
			       "c6f059ca7312a61d 50716562239c9339 e224e2fe6999ffda 833cc486260685e8"
			       "4090cf59b8ca018c a0e3c4bf2d500716 40240d9ffd128619 ab62ae5cdb8bd9f4"
			       "728c877fedf63e12 d08d4759aa3a2d44 38aac1613fb2d5bb 0083f151073c5083"
			       "6b9e8ef95ce0182f ff4205c44b4678ba 5bee877246f3d6b5 85cf0c160f961b28"
			       "ee583488fd42d12d a487a88dcdd62ab2 a3cf84f5503df200 5db4a512ebeef9ae"
			       "2610f93d818d1b8e 61142cc89fd11a25 be8f364e39002486 47550d9835d8bfdc"
			       "f1476993cb1ac130 e35bd3dc9688840f b4f178c0180e3e5d 68dee6147dfe387d"
			       "3bce676bbb0043c9 40c5de76a270e9c2 32f373bdb54c78be 4b8b8c5e7843e4f6"
			       "9fbf5a6ed0133528 1e368720c9b59d1a 1940b25fce29b802 c5d6c5f24865c545"
			       "ae21ee34b3b6a530 0d4fa2dbc6b6aa89 aefd501e525e44c6 c6a6563369768bb7"
			       "7aba7b9d091ca135 636c5e12372e2527 fb4cddec2252d926 4d0b3be0bd218b10"
			       "b33a65a03f373946 1fd674bc2e0cfb68 e3ed70cbf3655344 0868f94fa81ec1a3"
			       "ca4c63a24d57e90a a4c475003f4ec1db e566132f352a65ea 464a019a565bdb20"
			       "5862028134dc9f0d cd4386ccc7858c3e 7d41bb8187a9d541 394f0b1b43a52765"
			       "d09a35f536458d69 b1a74284a5aeec9c 2bb6eb6a1e605f2e f04d8526eb5ddbfd"
			       "a0e2e4cbd36636c5 f7bf8b47ebb63776 bdeb6b3879ed5bba 56e02f074577032c"
			       "192efb8d2aaa1504 e52877923a064b20 86fb946b92d52efd 1ba0768d0df6205c"
			       "2996c0a539772f15 45648f0fef6d3367 bf6a9a0d1f1f8656 d37801f13909cb00"
			       "de7dcde257b8e40f 7c4b0b0088d78212 b9cbb3c05af420d7 0e10f900e79af787"
			       "62f3d917ac034e28 e7e477bc8c189d74 191de97d23f3ed2e 200c2ddf168666c2"
			       "9a61296d3d9ed6e6 fd40fa11da4135e5 b14f521a1b478975 7ff3bda98486a102"
			       "e81656a5a714a7d0 13f145e10d2b25e2 385c6a4c8b883114 79fb1c5219a5d325"
			       "b78e59ee1db88068 7a0fc2b7067c53ce 2b0b0e6d77b3b064 376e4c1b32ccbd7b"
			       "cc148b5bc0e7bd00 728c858842187d7f e1be370e305b2f43 af3176615b9f684a"
			       "c107bf87e20b080c 14d08e75306767fd 650244af3bb06fae ef9192429b947984"
			       "d138904cb96284c6 5c8c71720b2e8afd 708933434ba9fb4f 2d561497b9f275fe"
			       "68c1cbe982794ed5 aca3fc35c7aebf2b 1a1c953e6a093f13 9794faad63bd7e18"
			       "caf6066db0403e01 43410edbc4acfbfd 059adabcf07f6187 18cb6f20b240335f"
			       "77bff262ee4f0486 292f5b00a1f50d27 e44e4ba44d456db2 6280c4142f20d9e9"
			       "27b5e192d0f2d07a 5d43949e5c5684ac b4b2518739e77172 b13391d67ef5d181"
			       "b6477381886c2644 f5326b42d570f531 0e0cfebc61bb059f 862764a25650af8c"
			       "adfce093d19d5457 20213e934a0d7628 dcab66c4e1d73dff ec4c6eff3848f5e7"
			       "20e7111ef8b2acfd 3d9b1e50c07ed4ac 8081c3fc383b71f6 78113d5759085126"
			       "77c985a2ba519611 ec2af89121aafa1f fbb57f47f9eb6b31 7e9f4b42896d4e82"
			       "8302cc197cbefe3f 1ea041311010bb89 d7646db41d76d33b 03dce6289b6f0978"
			       "a99f2537a9379396 6cf9cf2449557215 5357d3a54de59b6b 8df39fd9c27d7df2"
			       "c941422959a4eeb8 0b4e38f95a90607e 0a1045a5f68f76e8 eba838d8ab00cc95"
			       "702787fc74fb637c 6719cbea33c37602 e22a6bec533f8ebd 4615cee5b60fc281"
			       "441581e635b1ee76 d424007cf7d8058d 1464d356beb625bb 4753c05e30192e0a"
			       "13253c1a59536325 6a77d653cfa8834d 1e54a0e3e605dd3c bc83e197db186d68"
			       "d7c7b07bf060a581 4c3f17ac2d409e50 698428c3a02d1317 a340d4bb51272460"
			       "54a6ebd8a6abd2bd b8e055e988ea476b 434a20e42fb9ff13 5b7112433eca7c87"
			       "bf66cf844f204c70 be681fb623b8a86a f2ab7ebbc489dfef a75b7adab59e378c"
			       "7d86523462617b4e 3f4a66dec5bb55c4 c4b32675176d8594 a0d7ec1f6e3d4d93"
			       "83013b6db6a4dd2a c470c1d213686f13 da74e074b926b402 e1bbebfe60be58c6"
			       "6a3c1e589dc8551c f66248c70908f358 4cb96780f746f3b2 3ebe92de02dff2b0"
			       "f17a7554a7aca4b4 392a33ac86ebdb86 1565c8597dc3c0f2 2b09f5a3ea316564"
			       "822ebebd520d418e 17a538a056d88593 15b47fbd2f5f9f06 3e64305f27d9014b"
			       "b7e04431e6beeec9 6aefc68dca3528a7 fab15e7394d1d45a e6f5000f94039020"
			       "4e336c0ce77d95d4 7a4fb5894b2edf4e 97e55b9af2458fd4 b4eda67f09d80ef0"
			       "c88db87416cbd51d 2d912d0a8e820a13 8306394061e588c4 e681015a6865d434"
			       "eca7494824c48b7c 047af2ef5f808336 60e5ebb9b210a2d7 d91da16c03f642b2"
			       "e881d1c048a43098 b8013bde949a784a 348abdb26e9cc049 c6ab85895ecb033d"
			       "4aa3219d58b4ce5b ddf0ccee32e35a4e cd7eedf82dce36d2 316064b9014dc404"
			       "eeeaf6342b63f0fa c299df1d914afe6b f03ccb7e67d0cade 35e4bd207f33adb3"
			       "d302f23eae2e32a8 a6e0c68fc7d90423 43444d130d424777 d3b265c35602e6c2"
			       "681aea5f48643eec af827c6054c56353 4a6afae872d86541 8816137b5b6563ed"
			       "cf7754a3f1b7600f b7c328dd9c7b93e1 efebae36ae36a157 8244f7b0d1d66fa5"
			       "04835b28935d5a9f 7af834cdac4e0661 b2e276d79a7941ef e5dbc26d64293c22"
			       "e6972fbe4a8ac01d 30a70bfb21e19e62 9ce2682fc74c7bb2 b99f22c779f7022b"
			       "be7aca0b6eb9ee3e 019ab2ab023ade73 112815bcf129f4ce 650b2050bc523fa0"
			       "254f8a1cffbc121c 4cddfa33a01065f5 5df1eb43f66e6278 c4926dd5bcdadefd"
			       "a8c99932175f76ba ece263ea4434c177 6f635ee548193759 2b1177e67b902fbf"
			       "a3974ad2349a729b f2650f850e422f57 191554ed4244c8fb 5e73a4c2c92f7218"
			       "be17d7e689b875a6 05ea6bb493485bd2 1920e6cd02e4dbaf 8973c13cbc6197e5"
			       "adb915137cec79c1 14be4feda0c434b7 29acaf9b5eaa97b0 b9f6917cc3e707eb"
			       "43a7e3ecf7adb52d ce3fc73d3dd2d860 862348e0313ec4ca 7cff64c9b6d3de14"
			       "6b83ac35fabaa2c4 353327e56db1218b b1cf4dca9c73fe88 9302470aca92ecae"
			       "f7f2456dc2f5380a 7a1346af17970ac2 a42d7487f1a90811 1480d7ac5b8f4404"
			       "eac4a8bb3a0fa899 c7251c8bc58128de e488b1f850d41c1e 533ade2f210e3f6e"
			       "de45d49ff6134287 7e72fc4d45c5603e ffe3f4acc8b4ce78 45f0878b108baf94"
			       "94e9bd18e7c799af c8c94b1b1bbcb1fe 07973446b0084161 bc0f81036f8c3755"
			       "bef04785d9d87b89 075d92f9d20562e4 7cb8bf658e9c70f8 adea0d29f2042afa"
			       "ec6da2206f9786a3 8e68b220df028afd 5939687763e470c0 610d8ce1abb3c92e"
			       "ad114a80bf1a4a10 08f9235262d3da86 055ff6e4c98376c7 212aa582191cc1c0"
			       "7b443b98fcce9318 acb6ec6475543663 2d14ea5a4a9c8c2b 812933c5a893e733"
			       "71d2c70b86885a4f 1e4cb29e708186b7 f2389758b59dda1c 5cd89e43d0de02ef"
			       "f558b03984287abb 29f5fd2f22837d3f 3ab0d23e52462491 e0a0127bd4daac77"
			       "7f601e562ba7df4a 443fcb000c2f85e7 6c46347ac1882f7a 86e9777d1515b8a7"
			       "32bf000bc84e004b e4e882b3692a20d8 66d2e15390472e9f d7ee9740300eafbf"
			       "0b828561e1f93907 a5119d6af0cdc982 eea9fdf1e940a0f7 4e556e613f3c15d5"
			       "aaa4d39a70cfaa2d dbb03b2240bfbf94 49d8a427078a584e aa1b909b97064531"
			       "b01797e48f2fcf4f fdc1b65aa9f49888 20ce2e6ed671e3ca c854ebe0da73a8a8"
			       "6e586eecc327a0bf 139c248afee28282 c440613a521a37eb 8ecdc229621e9240"
			       "eb8eaeac8b4aae97 4be6f11d70fc7509 0f3ee4564c113b20 14bd4ed820d436e1"
			       "666ef9d6b0569644 b0f01604357dfff5 8a686905636badc0 4b6f16545041aed7"
			       "3e7e166fe553b2c6 beb6325598ef2cff 23d903d90e8554e1 61a73bbc85d5f1ad"
			       "95f3df0fa227b78f a526b3d21ed6b374 4df956a9cd45f006 276a280c3540e4ce"
			       "b58bfa59acc42f64 81f68ebe0e390fdb 6f35c4e6fb5f6548 f6dc7f03558534fa"
			       "4079344d1c26eb37 7810924dc26e0797 3b9ea5277a99e58b 8594c52b6199d3a2"
			       "f3109d1e120df14f 916357e642d47f5c 2f7d8546ec485b34 ad87e1796de4b451"
			       "cdedd4408ba91350 0b91c7e697192dc4 8569e443a3fe945a 7396e36fe7b2cd23"
			       "466b462315ff7e73 d1c8be52c9e79e39 c7423aea069d3ee1 19320575f213fdad"
			       "0cfb1307c6f7b32f 5e9949363073f4c1 47ae298535a0944a 97dbf43d8f4ed7ee"
			       "f02a7377931b71c8 6421728b7dfc2d5e cd2e6cd3932219c2 42ee4b7a27693703"
			       "0340b47f4ff1ea62 5e19df8695388f69 ba96c8e7d4097183 39fd65e6ff7b5167"
			       "69617a36f4b6f9e4 c56402119e53d006 03b67e4b023689af 37e61aa4569c4051"
			       "7b877e15bbcdeb2c 09d60895f9299bdd 53d1f1a2b7338f22 ffb3fdb8869d6629"
			       "bd030e4b32764f90 62e110ff9b6e682b 04f765e13982d752 22933af5e07d0615"
			       "7e9b5a0727cb25d1 9b6c48e9a20e6b33 d8dc217769b9154e 0ddf7cdef6efc998"
			       "f9765e62ee5df89d ceeb3865a8a857fc 73b5bda193c0ed37 33d3db379582ab25"
			       "79898a99d0ba8c8d 4b718fd52a70ea62 f3dc6b3bd39c1b27 a7fa660de83e64f2"
			       "f94bcd4ce60c555f 63b0698f83782e36 a29ef86a2ef2b811 e2e1b5526ea90de0"
			       "b0d0320ecf209579 1da1a318562e324a 430084468d583d9d ba21ebbc79a80d36"
			       "e93bcf2cd8b9018a a2f3aacb529dce30 3033598bd4921730 6dcfe285dbae0f26"
			       "b68f27e761c3da58 056e1f590f406ab3 09cac9e06aa74e5b 127724c0ce198ecd"
			       "4b0a2ed54dd6bd45 4b57072539330a0a ec211293b957ca8e c0e08ad3cab30773"
			       "8d72fc130a351681 04f65e1d483103d4 92bf6dbe34347284 d0790e425b657790"
			       "70bcf301139a0f6a 9f38b138544db5af 5a5175143ed2871b cda4c261f472b877"
			       "c5a108da9cc87cb6 b8f84d2f3143a86b 8afd2a0b8afca2f7 39a214a2bb625882"
			       "1e2c605acac65227 0aba7fbe7a756342 c4b329783c8536fe 417baf3e360a4fc2"
			       "aef068b11c43be9e 9f14899c58a6633a 7b20dc48691d26e6 2fe45e25aea6a5f7"
			       "814132c9e8792f81 a79a4ac13a0b759c 820013dd775abaa3 b3e6992e9e52bcf2"
			       "ee4ee6ef65aadcc6 1700896438e47217 4a9eea12b61a720f 5768e56fe2cc2e12"
			       "965de68024bc235f 90a34bf3867f28c9 888d9ef36d27de3c 9714f2663349f8c8"
			       "5c521971bca1a98d a63b6378dcd7360c 4d7acca1fe174ece 5b08428768cd4a5a"
			       "651d9e70fa4cb5be 5e5f3dc619df1e7d cdddf484c43742d9 1a4bcdd09d902ede"
			       "28066bb1d18cafb6 1a3812a9cb3deb24 4cd9beb6df09dfdc 0b7973e1789dfe5d"
			       "fd9bfb3c81025dbd cb0f8b002390b1c4 423c4f784f28ca8b 63b90500d47821bc"
			       "ac5f5176b7c8afdc f5fef9ccfd573f2e 059a4fe3c91678b9 80d675a7150874d3"
			       "af65ef2ea6a6d65f 2684cbf62a9e20ec a8edb6325762fdec fd4d87e67681cbeb"
			       "edba2395aca7abb9 aa350ca32ba415ca a8de9415043c08e7 041860a200076916"
			       "4e8a9a765796e983 984b764fc84b0ca2 bfcabeee0ce1828c 5deb573e8902bc67"
			       "ee6dab04efcfcf13 7eb35d020a71a947 de5e2ffa64b7e9dd bbca88348f7342a3"
			       "aa092132f9034e4a 2f8eb2c139be93eb d0812a2ce6617cb7 5e04964c05fb6bac"
			       "756ce961f9790e5c 669975c8b038e8d6 35f464f07bfb9bc5 8e2688fbe0057d21"
			       "5b95de585ec9b4ff 1f1f42c5c5bff19f fc8ebbfc9ff27488 dc7e9135579689a6"
			       "1350219598b8521d e566262ead6822c6 03bb498e06f490b4 a25115f46d8f9c04"
			       "2c2fd42dc2854ace 7cc3cb3489c226fd 6d9c88c7baf8b17b 22ce5d68d4e12892"
			       "6898475ebf8ebb53 b43a5c6f32a7f074 416423027ba27ae1 c99bc3b5e3f9f5d9"
			       "f9e0bd83cdecf949 bc97d04d73f5fb3d b778a82d21402f65 f03623ee7496c783"
			       "c77297057c135a3e 39dd8b425952f15f c4208c7d4128608f 4182c8202c717853"
			       "cdeb6f4f77c4cfdb d05d622918ac33dc 5d15600338d34d6c 71be25b40145d171"
			       "7f576142daa51f31 503a7c4eab101edb 11c220ca400c8ac9 9ef6207c632a9a2a"
			       "ba5dae4b41540a2a 95899bfa4caf20b4 01361429cdedb990 7afd2135491e4b7e"
			       "a47b64b2419eec34 e22391667842d56f 15e26d273a08f4cc f48126cc1748c92b"
			       "47d0fa42ef5d0eb0 038dec4bdf81bf39 e168b577db0f6ce9 4553938de6a1e7af"
			       "381821a4c369429d 70fb0f4dedef4e55 099471dcb0fbe7df 443508913a5aefc6"
			       "3869206335a7b188 56145d5ad6225bd0 60916f21b766773e f92c55be896b50f8"
			       "aaf282b43ded8440 e6784aa62314fcf4 20a9a8e473cd1f5e a7a29ca9e3861724"
			       "26e3927b7db0ae40 9049a4c21a5c7725 90f15e794f231e5b 8d7514363052b3f5"
			       "45f055fab47a4de5 812c826f543a533e 1b29e35ef8ba9851 3f9f9e04b1b0fe6e"
			       "49c46af6c41fae85 02ab8beeb775c92d 85ce1f32bcb46032 541b6a99ce75bb95"
			       "b1e6715f2f767884 7c0870506e7b1ed9 5f54271683de11eb 0566375ed98f3792"
			       "b2d0694ce2a8d1b2 16f6e6eca2f288dd 63651de7d28da1ca de1b2ce691c14708"
			       "0c6c16c99b5ea5a6 b2bc88cd25ba438d c9e33b6456f8bb6e 7dc53411e6ae3d3f"
			       "f4bc4b2294086b08 da2e94427f1fa36a f98c69654b423869 4e0633f9cdf3df81"
			       "6f5ef5dca5d895c2 756dcbf498ca02bf 5328dcbdefa7bc04 6631cb6fff68c7f5"
			       "b113b2ca90c0cfd1 7ed18187f79aad0f d920a1a0f593981c 13360733f9a7b63d"
			       "d6dce0831fb7a59b 9a621e829b72b513 7a986fc40bb31219 718880d4e8f3dcca"
			       "72347a22eeeff333 fb32b6b4ab65262e 11ffe64dd87bc138 6352bbf05ea058fb"
			       "797b39db60eac203 2911a26779410a8a 267bb1f674ec8a4c f419fc00c6fc10ba"
			       "4eb818e463eff790 0d9242fb76400468 46ff3de6d090ec09 55ee43386783cffb"
			       "60241e906addf8ae cfed1070040be90e ab174a7844931ad6 546ddb50d45bd998"
			       "00e9170fe860c6f3 22ddf623147dec86 1dfef62642a99971 d2066567a16ef36a"
			       "843edd16275767ed d971f79307b50fd0 9381daf0c2996f69 92f0f33104c4e320"
			       "5e33df46b0548660 5770264f41a7169d ad04398ff18abb32 e273c2588b12bda2"
			       "a7ff5a5b95c6099b d7474f43a92de26e f0a03fc51959a52c e653592f5c904782"
			       "1e488c33bebf28a3 56479a5b2683da63 acb3c940be37ce34 b705972f2ec7de94"
			       "463064209898fdfb 547e82adca0147b4 d4fac25a975b68c4 711f41e31e981281"
			       "af1c933e13a4185a 8223ef7ea46284c9 c5edbd15c92f58dc f6b9d12137f40cd0"
			       "21af47bb5ecf49e4 11c55750f59e4d18 daba15971b39538c 113fad64c2763203"
			       "2e6c40a8640ce610 7f72cad30e8eb1c8 ebe0f799f80c073b 8d901518d3677bc2"
			       "3b03debfedbc96cc 246973dd15d49f24 ccf8e5aecf480fa3 3521513b1e58bf3c"
			       "a43dfe7908729cf3 5d728b90b45879d6 db9a0c6f9186af19 00f7205f33a90956"
			       "bfca4f386b88f702 991914b639dcc25c 8868da385ce06687 a52141f8ae7f76dc"
			       "87f9f75d49b55548 4a796ea4ca33152c 865650e60e073034 1f2f8a3181256e4b"
			       "68e3943c2c563047 d9f33583fba05fd6 45c68d4c7b80dd0c 33c57f416ff9f43e"
			       "3ea7ce20f38374c3 fa40d805c9b9399f 51664c76fcd502e8 0410d53f1991f8d6"
			       "c4d98bd7d01cf288 81a4c55d12781cd8 d918ecc341f1c011 43a2b1a48d101f1f"
			       "2c307b6cdf80c645 62f3128ba30bf025 95bb934c080cfb83 c3d9dc1ccb8ee12a"
			       "150efadeb21a558c cd0c94f606463405 3c84de6bc30aa171 e91437d76b9f73f3"
			       "ea2744df997c35ad 50f68876de350b3e 18029409573b6726 0032529820a69fb0"
			       "85c2199398b72fec 18d0598be1f1190d 7c8311ebbbd770db 7202b2a76acf8f4c"
			       "409a253dbd1a3662 8f90dc62d737ad82 cbe22d208638a681 ca9a7f17e95a2d1e"
			       "145196c319d10c53 de7dfb7eca357840 7c0d907c1e6a8fe8 82e195b9f86fa8b6"
			       "c21633033dad6b62 ef0ec45b96ced9e1 a73f7f31d7e03553 9b5247d24c65ba1c"
			       "af506a8b1e0df1d2 57816e3249731940 935a88a7f00173b5 058ad62cf8c9be81"
			       "883e63e2bcd28409 26424c77e47d4420 398811d787c52adb 01db8319e935b80c"
			       "2ce3d3d9c21270aa e73b331fda5b5527 3719dc58a0acd85d 72f36c4cbc2c141e"
			       "a4d8b17a14824d8b 602a5719f4908fda 04442229adad582e 9eef2690e7a74518"
			       "5753787a865a2d57 5cc22b4d5b8bca71 6e1318bec3087b54 89f0e1600e58c5e5"
			       "8e908d70db59612a fd600d5168b572fa 137dfbb5358f6aab 025dbc6b7c0bd37a"
			       "a094d8343ccc060e eafcdc010cdb2768 7a16cc5cc5b96944 5492f9bdbf4fd18d"
			       "5caceff19439bd5e e65d4fe0505fe05b eb9dee41c558c53f 99b5386b870afaf6"
			       "4670a189843dbda0 0d9f5b823012a46f 6258cfdd903bdd6f 941e6c797c4097f9"
			       "c62b96d875c2f1d9 c29ba54de5058768 831a1430747c5e54 c0f41bc3cb46620f"
			       "2f21b1bd957f3c29 36e53e8a621c8ac5 40a6f5f4177eddd7 ab84545ff14f9c59"
			       "7be67c8c5953693f ba43635e8bab6f0a 3282568edd00b746 6b341557322263e3"
			       "e200832b7d454337 98d64b4c898cd5b2 75e0ec9f349e6bdc 31c8ab282ea4c92e"
			       "63cbb7daba8657f1 81d2c6ab7b822028 e974a64a8d3b751c a58dac1eca26378e"
			       "3a871e26ac7797ef 4521ecb5d2095552 faad5b8b41b696c3 aec3b98796e375d6"
			       "9866c77a5f8f9246 1b03d5d85cd87c42 8e21ef6f6ae9a0e4 41d55511136fcc98"
			       "82713e1beb6adb83 f6dc5e161fc244c2 e85824e182f74667 86c4f52b81ed5eee"
			       "6dfbf3efc42a2284 0e52e4ffced6cdcf a1d6713bb671b106 cdb49389725006c0"
			       "467ee54e51311393 111c8cf5cfab05d6 a437bbb4ba76f98c 80416bcc82359a60"
			       "1d2ce4c5070fb6cd 1dc46ed342f3f9e8 c6025e7e4a395e6a 76d060028fef9f19"
			       "50a88be11945281b 7275f95525f79572 d3077753bb302552 591ea9d6c636688c"
			       "b3ff90038c7b97b0 110007c08e4eff3e 98d7bfb617094c96 42cdd08964e1c8c2"
			       "9065f8d0b386f1eb ae5d73a5bba76baf 2404d2a836d6eb0a a404154a5dd3042e"
			       "3fa6b845e991a9e7 98e81dd520482b5c 01c4c997b734bc98 09b456d29a7e1a4d"
			       "7c4cf16391346bd4 7c20462840aa5781 0b495ddc301c9a56 f9a9ef3558ec4a40"
			       "33f96efaa68caeac 0b6c66c676dec0b7 8738ec87d57fdfe3 d8c6dc5a282e303e"
			       "976af0c3ee948256 2e1d9c1112b169a2 5ec6b1c410805da0 d2ade413deb66bef"
			       "1ce1a44ab8254594 2f1f6d5ad30d2541 6a467c3c7a61613c dd0039ef2433a6bd"
			       "a882c4e5a9d9d173 d7b19fdbf385864e c2da55f539127968 26a6b2a1e7ca5a0d"
			       "3254ffa47c419b30 15f8c1ee773bd25c fe44fb7cffaac50f a691633d4cdfd322"
			       "b9fe79583627eba2 9b83c1fbc2fffd97 fcad6f19f1d963f4 d8c9b593f76c90a0"
			       "c15e2b04e3a13c49 2cca8348ca7187ae e4702f164af524f4 65b0caa881cdd5e9"
			       "43ffbec7a5f3df0e 2236e646ba799e63 9237b14c5c412f0f 1afa9d041efa510a"
			       "082a884f485ad938 08ee926d1ce8eb38 2552ff58b76c1ac2 a4b60545802d5e98"
			       "ef7e36cc0396a928 7a461dd52e99fe8a 25ae3e2d388bc310 0606d0e8bcba7122"
			       "f741866430e3ea51 4bf00ff2fb16e9ce d5ab58cee24b8c71 5be8e2c987f06b37"
			       "fb4fc89e2f9bb90e d7d1a196847b78d4 1ecfe9523f62634b 34f1706e57246008"
			       "6eb7c99d5b2d17df a9dbf4c333e3decf 53dbe80c8bbcbf2b f66275777508856a"
			       "5a6b527bde8a05a0 f40b524f86ea5efa 284e54b9c35c9fa6 3e2b730eefba13c3"
			       "d6acc68609c01b89 c13c538916934150 24271f84bc193f0f 9c8337bc099b53f7"
			       "00edb48b92acc9b5 eff1eefd87f022ad 7d57de80b8441d13 2393af7f80d3eeec"
			       "79f90e3ff4b6451e cf3a3b15265873a9 f98eb8ffd30a4ffd 0e6317ceca46ca16"
			       "23a7ec8729bcb804 4981d1fa251ea2a1 e4647e10a65c7d1b 7facd035f1b7802f"
			       "5e2229d691655ad6 ce37d918af1f7759 4787594f100a60ce 6a0ec0f214bc596f"
			       "4f09d29368eb6ef4 efdb98248565a8a7 90b575ef86aa6898 8c33cd98367ee770"
			       "07423010b3a026c4 4e1956f0d953e3d6 de4ff60e1b0f56b9 460e2be1bfa305e7"
			       "c4f3f4c292f0b021 36fadc5102c5ff6e 03107c897e21cb42 0a27b5d8b6ea23bd"
			       "f79c306ec254f274 2699f0165533ca99 54169a9bc9622952 94103dbd1d1a3d8c"
			       "c52a193ab2d25dad c2ca1bafb21c8402 9f5fe9376eb23810 d935fad2c66791a4"
			       "13ea77e3412f0b05 057478d9043183e5 d4a903b70fea59c0 a774563fb379e162"
			       "dd1fd1ff7d49b24e bd724258986faf61 6db3bc0ee988398f aec61d3984fe745f"
			       "d076cabd2e765280 8886f749d486b047 8c02c47c21ef1fb1 89909d41112e4e13"
			       "21581886fcc64918 7ffa781ddaae5674 36f4a0de92c83f8b 2c48d7634d4af8af"
			       "0834bd4fae5bc957 2b06d74780609f6e 4df7477262a7596c 85a0598c4f4a4f61"
			       "24e9377bcbe08fdb 90a46a8974395459 58c06c21661bf2e3 c3796f9900b03e72"
			       "221aa304cac54f7e 8372eeddeb03a98a 416104ff41d9493a 292e91a0fc699f59"
			       "401f485aa1dd08d4 00c52cfc3317bd95 3d2e4bb5382682d0 60d38fe0655b766f"
			       "9b3f387270e06205 34b79cc2203b46cf 7d26305b665d4e00 4e8fb87e0f2039f2"
			       "ed95d8ba96be209c 8e990786030c7c16 c314161356fef810 49723fecb8524a5a"
			       "19ea4a568e0ccad5 04afb30efce7cb37 a0e132e80318f75a 34ef386f70611ae4"
			       "9302c83781d7b632 e24be3b3ddce08fb 3a3aa310e8891244 76d76f62ae0a57b5"
			       "d02fe060da05ec63 85a89dee4eb9438d cd7d857aa714348b 1a1152ab79bdcd0b"
			       "1c1445a51eb302e9 3f3b8ae8f868362e 6bcb85605dcf5990 cbdd1fb35d980643"
			       "49f66b8dfa284466 6264a9ee90346a0d 6c123b6d1b0162b8 7dcc46dfe66fafd2"
			       "ede2393b3840a0e5 67bf5d45d38b3907 716ec14143a3f113 dd796780a2feaeab"
			       "7fee5061bb54b790 eb538a8697fca062 5131f91789ef015d e88091d418837260"
			       "f0c68b767603296f 3d0806de6fecf3d7 127fd6b31507c65e fb42e5b91d45ed0c"
			       "0a3830a235d9c53c 89a741a1afabb041 57f356cbd5dbdcdd 22c287d414a76a44"
			       "88803642c1d3df55 af35361a586ebb0e afc5ab8b48af41e9 d14d6fcd5a2d33b8"
			       "a4c3258df8b823e6 428600d54a49d4d8 63c0d55d02ab77ac 80da940afc174586"
			       "7768f29c08d03449 6c40bfa15df8cdcf 045b01777cc626a4 1c1273ff87dbc3a3"
			       "d0980ef772158e21 6c5142fc2c425327 3789ee114bc1dd0e 87b6ff7d114332c0"
			       "cc041bcca402c3ca 84fecae50c061692 dbc42de706ad6a5b d3dca9c86821917a"
			       "b1f2fd6501c1777b db76a66e8cd5cf3b e43839428147a161 50b5a3c60537f43b"
			       "9f6bb486232e92d7 60bfef25744d13e6 5a52d9625f97006b d1bdf41c0ee1835f"
			       "33762c6cd97bcc92 e7cc64d3c1c75e32 4519cf0fb9da46db 32099af6979d0ba3"
			       "8067ca9d0bf011b9 4ae7cf68c19377b0 2ea034b753cb5984 0b27ccabcc2c8056"
			       "570393be9df5981d 26ab652ff4459229 b02fa35a8e41da66 b7d036a093b08d50"
			       "14bb73c28376a369 47156908cb019ea5 3abedc86bc72886c 42e7f2cf632a375e"
			       "2f76983d2bbc5f64 697af115f35a8bdf bd1669dc32ace0ee f603202dcd6cb0c6"
			       "3a92a981edf60196 bc9ee7995323aa4b dc5e2eeb1ae7caf6 a2af066ab8bf2587"
			       "b1cf45a3fcfc05fc 9918ccf74c57e0ab f0e19b37acf644e4 cbf1f8a941619fe4"
			       "0598d356b1d6b9b6 f9638f716fe8a033 ce73a0b1280272ba ede41ff30c8eb15a"
			       "5e8309f6599a8506 21049ee745f12b26 2e04d1ccae97e6dd 60f4ccdb6da01313"
			       "ed16c65ff69ba197 d072b35ea31c4695 b0dd0c957334faa9 dd9b92b3a48b7f3e"
			       "90053ca6e70c59db 4763b8318c7e27a5 9c73eb0b0e98b53e fe7a27379fd4e887"
			       "4e3661f806fe110f 87f503c7ce705c12 f9c7e0b0b75d4166 06271f9cb85737f9"
			       "5cc5a739972aa7bf 44bd5f79eb9ddf91 99e869a4adac9456 709b7ffd04123159"
			       "59a78bf52204c393 c029ddb13ac8effb e808e1b002447334 e3e464a06465d979"
			       "6d0758a1b2496f85 42dba228f57442e5 17b9deeaffa7eb7e 689abf16c5ee284d"
			       "1e34dce084ccb593 50ca420ca2dbdb3e d8c384e756760bc9 05f8a61644963ee0"
			       "c722820cba30d336 84629f5a9856e82e 3c648b4293422f51 f9708f22c6edf4f7"
			       "d2d2887eec32e871 652f0b6d6dc0b567 6052cd09d80ef7ef f86b0ea1802beb05"
			       "89bc9f3350031424 23138712ea46d9e5 d44cba2b65543732 bb7a3930bb4ee7d7"
			       "c23ecc118055b559 9df03ea3281a5f98 36eda2912cc0aae3 166c70d4953205de"
			       "e4dd89457171c3ea dfcb4ed63c5e92d6 ce38bf00c9f33ae1 16b185e51e3eb665"
			       "4b55e4a17f584183 2f0f8ef7511f2b08 b2b1aec967544b29 64a20ec3748076b4"
			       "e8f772119dd47de2 59a14cc6ba578511 4070920c3eca3aaa 35dd4f23db00e733"
			       "496aed0d09aa11c6 165b8ed0c1639ef9 15ccba3241777c6d 30edbb8decb34311"
			       "a8ec847fd5475373 1347d45a10a80e69 32edb35e9a2c95b5 9541394cf28b5ad0"
			       "53e6db854049ed48 cefd5ad1494dfd85 663f88215a5123e4 8bcfebbac76cc0ce"
			       "a01208c1e907dfd7 b051ae0bc0804a1e 3a42b2b8948ddfa4 1caaac64a3da1c69"
			       "270a485524846848 fe291531d314197a 8381482e6909844a 69c69740815c9c64"
			       "6687e4139371ee1c b9a635997a070152 89ff74788e43936a eba2a05340f61625"
			       "82061f8867ded0d9 1851f7d526a0915c a59ded312ace9bd5 930fe1bf952f127d"
			       "edccb9b676ed1580 6dd428148989421a 4ffef2306eb0c7d5 ddafb8dbd6ba8cab"
			       "7f1d73685716cf8f d6d8bf4bbb23b99d 0f2514f56a7f29bd c8568d2eceb314cf"
			       "5246a0d410704ddd 369fc55053496e28 8f54b922cc0d5253 ffd8f54ccf7d1d79"
			       "927a9805007ee238 0a9679aa35203d61 d50e7327cbd5d09d 00af0531e4194a4a"
			       "80608987b185bb5c 0addb2743824dc23 3734c865d95374ab b68d8e2fd7bc6482"
			       "25ed1dbcc5701088 a24a2505f2e878ff 6a53694b84b331be 213f82204f3698b0"
			       "a89d2d763e501d8c a2207517e2cd9dcb 02daf804852a1cc2 2091fae7476ddd6f"
			       "ce95b96b5d21a545 36e4e852262b7247 4b0660ca9c35aa1e 5bc2855600d11448"
			       "02f8ddb2c9855ba7 749be2f8a90295f0 68f7594f12237958 092a8166eb851a4c"
			       "73dcd4ad98c65310 53a785323f850edc ac5bd2c6d57c9fa4 e04ea2d62e948ac9"
			       "ddd93cbddecaa187 e13435420cce4c97 31fbd964dbd620a1 28aaa00ad54e2907"
			       "751edf3e6608aafa 5fb38743231f88c0 fb9275fd680eab24 fcfde7570d0d0cf7"
			       "c11bf19eb4be4e77 ba91a7e234b0972c 9657b3632d989404 0d210752d807eb25"
			       "d5fa4b5f134e58bb ccd164124d564cd4 948c7c5804a6cdc4 e2f529f53ab6c54e"
			       "ebe94713cdcdb729 f60196e28e896d0f 92bd2a26aac1c47e 2b1796e4bddbe36c"
			       "96f2d3ac642031c9 a78e362fdb51bd7b 8ac0673dd3cd7f7f 6a636443bbe59821"
			       "5a000535b8277b95 e8ee0e3eef722da9 c5534024be37f50e 38346bb40801f6e2"
			       "f1fd8ec4dfc88484 9bcb61076d50f543 28a95e152ef2229b cb2d72beb3c778f2"
			       "a5af8add8036480f 7434c7ca766e4cca 7253c87cac6c38c8 230907135ef9adba"
			       "815f069cf369ebee 81e89fae54b94128 cade70570873a2ce 8687d306eab3506d"
			       "7cba9629604cf2ae 693efc0a6318b22e a5cbd33ddcb7a98c 7fe2beeeb93adfc8"
			       "eb974e22bc9b3988 27939e007820f848 4ac2d2438120757d 9984bb24ae349e39"
			       "2db4536d06441da0 f319df609cc1179b 80c8d82c13bd740d 9205812bc447a668"
			       "b45a6538bfa1b618 01ad2bcb8cecd031 08478ff44b1b3ba3 2a02f3ce2e4bcaba"
			       "2e73d43e60a1ab51 21da0ce5bea16fbf 9e4775883fbaeb40 fd0382e5f54c7195"
			       "6ae8e7d0a48c3bff b92e5b7de9d4e33f f0cb858529b56fcf aa750077d214e5e7"
			       "417bcd9e4d3e2ce4 8b5ba8ddd8e04b0b c894124e591db44a 7eb8d3b17aa80421"
			       "358cc7ab17782960 cb1de8ef4947232d 151d6f15a45effd6 c1aa8934d235ebff"
			       "43ac35f42fff5d88 ebe053ee39bedd04 54334ad1850290f7 ce840196833c2297"
			       "7be9b3aba318d52e fed5618cebdd4ffb 7a5b2f634f7b3711 c516166e636efde4"
			       "1541fc58a42317b1 8da16e9780ddbb7a e08f01d3f7dfd2a1 23d99f8fdd08f93e"
			       "e76cb43d76110c8f 12d898eb4296b502 872fdd8aaf83622c 29bc9cf5ea979044"
			       "392e4c0dc81b4d04 5f86c58988143b92 a1ee68152861d162 c118c8124a1d81fb"
			       "e7ec8ec0ab2a1c2d 6e636b9b6d284ef3 0bd4d0f2bf75cc0e 2aa27ead27276ad6"
			       "bd5da58d210179c8 991820c307b3ee28 0832aa236dafd0a1 118983581b213cf7"
			       "2d63bb92510708e3 ac18c947d083cf38 d44a45ad90360858 51d31ac8b7f9ebf2"
			       "b8b2d6df6ca0871d 8a1a5a4747a0eef5 772f79fb11e3d0bf 4080529c14d133cb"
			       "1ad8535d63f3a1a9 c466c52f27d287ec 4c32cf3eb5ba19a5 34836810de3c3061"
			       "ed6c546f7bcbf2a6 6bf8df8f1d8e81b4 44cca8144bfdf61d 52ff3b2652583d96"
			       "0592cc63c873426b d21edab31bb9f84d 04bc774f4272e446 2fce018c73fcc356"
			       "bb329a7fb23fb3b5 185014f14df81e6a 670b98778e8f9505 107c6bd3f87e477a"
			       "bff01a5bcc2c34a2 03155fb2243ce21b 77378ec1b801f8ad 20570f1f7c3421b7"
			       "4380fed97b2bb74e 8432479a9a33925f 9ec5c92e841a7357 b32690624e9433cb"
			       "fb705b04f965dc3d 7c230521e7a8a2a4 69eae7ac990d062a 7f4993de3ccd15c6"
			       "00c8930b96480077 e1028ebff5ab2eb5 08e419e652d5bc22 f1bb85fa3bdeb249"
			       "460e42a918086a20 cfe6f3ee22d9be98 2d86ef588d92a03c 5dfac374b34234dd"
			       "bcabc7cb18ea1a6a c9307949d5475535 5018e844757ebfaa 0f1b3c70a8462424"
			       "c48b1e94e3b692a3 31171d8ba4e7bfab affe4f9078cd0723 b095fd2f0616110f"
			       "8646045489e7100b 45366b676fdf5f31 2bd11999c4a7dd71 e64c2755dd06a48c"
			       "dc4f2301ca5a7730 0cb14c2014bc2041 e7434a93d5b2c418 57236a97aa822a79"
			       "978266302a2d9463 126332b2d0f5445c c23648700adde567 2b4f2f55d72a09c8"
			       "fd97b66f8d6a2b68 6f5e288c009da8e9 dd9a3c7612a777e2 c4113258950bc17c"
			       "ed754bf8cb77a9f2 d1fd33d241fa4278 09cef422b5dc1e53 60eab473decdd7dd"
			       "e262fbe34f0c61a3 5668a89972e15903 24bc21d052e49897 6e562d456ede24f4"
			       "66f5d1a0cc050b20 26faf20c32efd009 b05665b0698b3e48 2df144aa1aafa114"
			       "dc0995929b1d15df 594e2c088ecb88cf 50234622efe69ddd 78448efe147cf189"
			       "f8181fee349a17df a8686d130d5e6fb0 fc14e7a1107aaf9a c82329858e17bd3c"
			       "de6c217951c7849c 370ffb3e2de92aa2 98ea2326464166b6 d2f4acde7e190622"
			       "d8ab91cd3c1a57c5 f8106f95e6a02980 b7bff80cccbc953c 982c5c76cec0e92a"
			       "50e4d9dbd6f4c9e5 5af22555a87e1108 da9493e1733d68d1 24a0806887685850"
			       "21f45c0c1c861657 625d8334d5a6527a bab1691401a09f4a 5984ae0b26bf76df"
			       "9bd983981907ea87 da86150ca0044e00 cd8b78a31cf4f775 e9b698156a2ea874"
			       "a855b5e78d8bbc22 df80025fcffce42e d1226d15ad6542f9 154b1abb9a719020"
			       "2129fe4e75c97f3c 015f037a11a50146 9d7d6ffd1308012d 822eee54eda9b1a2"
			       "39363ce4d4ac3160 78dabbcec96e2cde ce4e7dcd36973336 f84eb4cefd2d9c36"
			       "d2a7ee922d424602 44b18661c6645db6 ea5ad18a693ff704 07e47e63bdc6fab2"
			       "b6b9bcf17e66eab4 5815f7cc49df86c6 95ba6194fff7a21a e666049d481d7f09"
			       "616cffa95483e792 28ccd6dd5eab65f6 937c4f4882bd6dcb 8f23d59db737bb75"
			       "c69521cbd8c823ba aa967c24c9c075fb fa6c5f23d109a88f 0e4bfb3f4a168a00"
			       "39c7b4dd2366a7e7 24aea80088e7f426 8ec05f44db8c6ab1 2dcb0579f564e78b"
			       "9631b75ca5b7d5e3 d07ce04dc1137188 98473c5025374cd9 6e1005e52aa10d25"
			       "0fb67e0db5286a09 b27c4daddeb00044 0751a1f2edf5b22f b6e9268ed0e662d6"
			       "b8bc853dfc3b31c5 58638a6be19f9b03 34ca8d825c44c326 43220aeb512d49b6"
			       "8db91a7f0b65e2be 8e6da818679e4d46 121754eaf3ff5fa8 7d28510536dda9d4"
			       "755ddbd324337a8f 58bcc4b7c40f033c eca67487207b230f a5d8f2b5904e805f"
			       "c462db7709d92c3f b82cc42f8bd99511 ddcfb69992118172 28fa16e6191b6596"
			       "b8f210152bebdb3c cfee9cce3f78b9b1 11a6132d7e8e6ce2 0052cf3546b614f4"
			       "e6a713bac09b0351 83ae11d86460c51a 5d8f408a2b291f3c 036e85b6033c4ec3"
			       "42d1460279d19cfc efb645c743ff3b9f d631618da013abe2 4ed77b38ad4791e9"
			       "206cc3f31c6fdfb9 f2ed2228aee0a05f e00a43e1d1048ef7 ff2f2a93f533df70"
			       "4b993b15673fbd93 f747429822f809bb cd3e0df4d3fa10b8 f40feb4648fcf6d0"
			       "f695fd9a2d857888 7bdd2ff2a3a5da2a 607f6b201d5615d3 0d8ebc1fbcb058ef"
			       "a88e562543e861a9 c10b4abd7d42374a ac946abcce92ef4b 75b095879f418b3d"
			       "e8a12c61ec6a3bf8 cf9e8c4d3a3aa63c 36866f38b5b42b42 dbffd5ad6b4a566b"
			       "bac3044cd140bfbb 9eb6cf6229c192cb d62d6f078b6221a6 278df3c018a41d0b"
			       "2e1317f71f8ae001 c18d802db638e873 6ce225bf6f0ae169 3c7d8b27c1350a88"
			       "80ac7f1c09b319ab c7a0217802fa8824 f8b9d38aec542570 c2451f742f8f51aa"
			       "98afcf08455d6765 5ce1ceed690a71a4 7f3bb14ea9b4c998 c0f76c3c637b8cf8"
			       "72196aaca7d2e9ea 1c9f81394af9e3cd 0509149383f64d30 31bc50240211ac62"
			       "9c722ccc2e7c4b6f 6f0b94d84b4a0eb3 9984172a7381e50b 38b89945bceff0a3"
			       "604d875a6ba2e836 defb9b2ac716c646 e28497b4e216fd59 f5830aca13349684"
			       "8eb3703ff06f2c1e d4830a86eaf73770 873ae9d2849ba615 eb46d7b0ee036f2d"));
}
