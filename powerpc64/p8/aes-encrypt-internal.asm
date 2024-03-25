C powerpc64/p8/aes-encrypt-internal.asm

ifelse(`
   Copyright (C) 2020 Mamone Tarsha
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
')

C Register usage:

define(`SP', `r1')
define(`TOCP', `r2')

define(`ROUNDS', `r3')
define(`KEYS', `r4')
define(`LENGTH', `r6')
define(`DST', `r7')
define(`SRC', `r8')
C r9 used as loop index register, r10-r12, r14-r17 as constants.

define(`K', `v1')
define(`S0', `v2')
define(`S1', `v3')
define(`S2', `v4')
define(`S3', `v5')
define(`S4', `v6')
define(`S5', `v7')
define(`S6', `v8')
define(`S7', `v9')

IF_BE(`define(`KEY_BSWAP', `xxbrw')')
IF_LE(`define(`KEY_BSWAP', `xxbrd')')

.file "aes-encrypt-internal.asm"

.text

 C _aes_encrypt(unsigned rounds, const uint32_t *keys,
 C       const struct aes_table *T,
 C       size_t length, uint8_t *dst,
 C       uint8_t *src)

define(`FUNC_ALIGN', `5')
PROLOGUE(_nettle_aes_encrypt)
 subi ROUNDS,ROUNDS,1
 srdi LENGTH,LENGTH,4

 C Used as offsets for load/store, throughout this function
 li             r10,0x10
 li             r11,0x20
 li             r12,0x30

 srdi r5,LENGTH,3 #8x loop count
 cmpldi r5,0
 beq L4x

 std r14,-32(SP)
 std r15,-24(SP)
 std r16,-16(SP)
 std r17,-8(SP)

 li r14,0x40
 li r15,0x50
 li r16,0x60
 li r17,0x70

.align 5
Lx8_loop:
 lxvd2x VSR(K),0,KEYS
 KEY_BSWAP VSR(K), VSR(K)

 lxvd2x VSR(S0),0,SRC
 lxvd2x VSR(S1),r10,SRC
 lxvd2x VSR(S2),r11,SRC
 lxvd2x VSR(S3),r12,SRC
 lxvd2x VSR(S4),r14,SRC
 lxvd2x VSR(S5),r15,SRC
 lxvd2x VSR(S6),r16,SRC
 lxvd2x VSR(S7),r17,SRC

IF_LE(`OPN_VSR_XX(xxbrd, S0,S1,S2,S3,S4,S5,S6,S7)')

 OPN_XXY(vxor, K, S0, S1, S2, S3, S4, S5, S6, S7)

 mtctr ROUNDS
 li r9,0x10

.align 5
L8x_round_loop:
 lxvd2x VSR(K),r9,KEYS
 KEY_BSWAP VSR(K), VSR(K)
 OPN_XXY(vcipher, K, S0, S1, S2, S3, S4, S5, S6, S7)
 addi r9,r9,0x10
 bdnz L8x_round_loop

 lxvd2x VSR(K),r9,KEYS
 KEY_BSWAP VSR(K), VSR(K)
 OPN_XXY(vcipherlast, K, S0, S1, S2, S3, S4, S5, S6, S7)

IF_LE(`OPN_VSR_XX(xxbrd, S0,S1,S2,S3,S4,S5,S6,S7)')

 stxvd2x VSR(S0),0,DST
 stxvd2x VSR(S1),r10,DST
 stxvd2x VSR(S2),r11,DST
 stxvd2x VSR(S3),r12,DST
 stxvd2x VSR(S4),r14,DST
 stxvd2x VSR(S5),r15,DST
 stxvd2x VSR(S6),r16,DST
 stxvd2x VSR(S7),r17,DST

 addi SRC,SRC,0x80
 addi DST,DST,0x80

 subic. r5,r5,1
 bne Lx8_loop

 ld r14,-32(SP)
 ld r15,-24(SP)
 ld r16,-16(SP)
 ld r17,-8(SP)

 clrldi LENGTH,LENGTH,61

L4x:
 srdi   r5,LENGTH,2
 cmpldi   r5,0
 beq   L2x

 lxvd2x   VSR(K),0,KEYS
 KEY_BSWAP VSR(K), VSR(K)

 lxvd2x VSR(S0),0,SRC
 lxvd2x VSR(S1),r10,SRC
 lxvd2x VSR(S2),r11,SRC
 lxvd2x VSR(S3),r12,SRC

IF_LE(`OPN_VSR_XX(xxbrd, S0,S1,S2,S3)')

 OPN_XXY(vxor, K, S0, S1, S2, S3)

 mtctr ROUNDS
 li r9,0x10
.align 5
L4x_round_loop:
 lxvd2x VSR(K),r9,KEYS
 KEY_BSWAP VSR(K), VSR(K)
 OPN_XXY(vcipher, K, S0, S1, S2, S3)
 addi   r9,r9,0x10
 bdnz  L4x_round_loop

 lxvd2x VSR(K),r9,KEYS
 KEY_BSWAP VSR(K), VSR(K)
 OPN_XXY(vcipherlast, K, S0, S1, S2, S3)

IF_LE(`OPN_VSR_XX(xxbrd, S0,S1,S2,S3)')

 stxvd2x VSR(S0),0,DST
 stxvd2x VSR(S1),r10,DST
 stxvd2x VSR(S2),r11,DST
 stxvd2x VSR(S3),r12,DST

 addi   SRC,SRC,0x40
 addi   DST,DST,0x40

 clrldi LENGTH,LENGTH,62

L2x:
 srdi  r5,LENGTH,1
 cmpldi  r5,0
 beq   L1x

 lxvd2x VSR(K),0,KEYS
 KEY_BSWAP VSR(K), VSR(K)

 lxvd2x VSR(S0),0,SRC
 lxvd2x VSR(S1),r10,SRC

IF_LE(`OPN_VSR_XX(xxbrd, S0,S1)')

 vxor  S0,S0,K
 vxor   S1,S1,K

 mtctr   ROUNDS
 li  r9,0x10
.align 5
L2x_round_loop:
 lxvd2x VSR(K),r9,KEYS
 KEY_BSWAP VSR(K), VSR(K)
 vcipher S0,S0,K
 vcipher S1,S1,K
 addi   r9,r9,0x10
 bdnz   L2x_round_loop

 lxvd2x VSR(K),r9,KEYS
 KEY_BSWAP VSR(K), VSR(K)
 vcipherlast S0,S0,K
 vcipherlast S1,S1,K

IF_LE(`OPN_VSR_XX(xxbrd, S0,S1)')

 stxvd2x VSR(S0),0,DST
 stxvd2x VSR(S1),r10,DST

 addi   SRC,SRC,0x20
 addi   DST,DST,0x20

 clrldi LENGTH,LENGTH,63

L1x:
 cmpldi LENGTH,0
 beq   Ldone

 lxvd2x VSR(K),0,KEYS
 KEY_BSWAP VSR(K), VSR(K)

 lxvd2x VSR(S0),0,SRC

IF_LE(`xxbrd VSR(S0),VSR(S0)')

 vxor   S0,S0,K

 mtctr   ROUNDS
 li   r9,0x10
.align 5
L1x_round_loop:
 lxvd2x VSR(K),r9,KEYS
 KEY_BSWAP VSR(K), VSR(K)
 vcipher S0,S0,K
 addi   r9,r9,0x10
 bdnz   L1x_round_loop

 lxvd2x VSR(K),r9,KEYS
 KEY_BSWAP VSR(K), VSR(K)
 vcipherlast S0,S0,K

IF_LE(`xxbrd VSR(S0),VSR(S0)')

 stxvd2x VSR(S0),0,DST

Ldone:
 blr
EPILOGUE(_nettle_aes_encrypt)
