#include <stdio.h>
#include <stdint.h>

static uint32_t
invert (unsigned x)
{
  /* Return ceil(2^32 / x) = floor ((2^32 + x-1) / x) = 1 + floor
     ((2^32-1) / x. */
  return (uint32_t) -1 / x;
}

static void
output_encoding (unsigned n, unsigned m)
{
  uint32_t M0, M1;
  unsigned c;

  printf ("{\n");
  for (M0 = M1 = m; n > 1; n = (n+1)/2)
    {
      unsigned c0, c1;
      printf ("  { %u, %u, %u, %u, %u, ", n, M0, M1, invert(M0), invert(M1));
      c1 = 0;
      if (!(n & 1))
	for (M1 *= M0; M1 >= 16384; M1 = (M1 + 255) >> 8)
	  c1++;
      for (c0 = 0, M0 *= M0; M0 >= 16384; M0 = (M0 + 255) >> 8)
	c0++;
      printf (" %u, %u },\n", c0, c1);
    }
  printf ("  { %u, %u, ", n, M1);
  for (c = 0; M1 > 0; M1 >>= 8)
    c++;

  printf ("%u, %u, %u, %u, %u }\n", 0, 0, 0, c, 0);
  printf ("};\n");
}

int
main (void)
{
  unsigned Q = 4591;
  unsigned P = 761;
  output_encoding (P, Q);
  output_encoding (P, (Q+2)/3);
}
