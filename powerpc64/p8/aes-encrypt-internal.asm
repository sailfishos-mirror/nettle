C powerpc64/p8/aes-encrypt-internal.asm

ifelse(`
   Copyright (C) 2020 Mamone Tarsha
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

define(`swap_mask', `v0')

define(`K', `v1')
define(`S0', `v2')
define(`S1', `v3')
define(`S2', `v4')
define(`S3', `v5')
define(`S4', `v6')
define(`S5', `v7')
define(`S6', `v8')
define(`S7', `v9')

.file "aes-encrypt-internal.asm"

.text

 C _aes_encrypt(unsigned rounds, const uint32_t *keys,
 C       const struct aes_table *T,
 C       size_t length, uint8_t *dst,
 C       uint8_t *src)

define(`FUNC_ALIGN', `5')
PROLOGUE(_nettle_aes_encrypt)
 DATA_LOAD_VEC(swap_mask,.swap_mask,r5)

 subi ROUNDS,ROUNDS,1
 srdi LENGTH,LENGTH,4

 srdi r5,LENGTH,3 #8x loop count
 cmpldi r5,0
 beq L4x

 std r25,-56(SP);
 std r26,-48(SP);
 std r27,-40(SP);
 std r28,-32(SP);
 std r29,-24(SP);
 std r30,-16(SP);
 std r31,-8(SP);

 li r25,0x10
 li r26,0x20
 li r27,0x30
 li r28,0x40
 li r29,0x50
 li r30,0x60
 li r31,0x70

.align 5
Lx8_loop:
 lxvd2x VSR(K),0,KEYS
 vperm   K,K,K,swap_mask

 lxvd2x VSR(S0),0,SRC
 lxvd2x VSR(S1),r25,SRC
 lxvd2x VSR(S2),r26,SRC
 lxvd2x VSR(S3),r27,SRC
 lxvd2x VSR(S4),r28,SRC
 lxvd2x VSR(S5),r29,SRC
 lxvd2x VSR(S6),r30,SRC
 lxvd2x VSR(S7),r31,SRC

IF_LE(`vperm S0,S0,S0,swap_mask
 vperm S1,S1,S1,swap_mask
 vperm S2,S2,S2,swap_mask
 vperm S3,S3,S3,swap_mask
 vperm S4,S4,S4,swap_mask
 vperm S5,S5,S5,swap_mask
 vperm S6,S6,S6,swap_mask
 vperm S7,S7,S7,swap_mask')

 vxor S0,S0,K
 vxor S1,S1,K
 vxor S2,S2,K
 vxor S3,S3,K
 vxor S4,S4,K
 vxor S5,S5,K
 vxor S6,S6,K
 vxor S7,S7,K

 mtctr ROUNDS
 li r10,0x10
.align 5
L8x_round_loop:
 lxvd2x VSR(K),r10,KEYS
 vperm   K,K,K,swap_mask
 vcipher S0,S0,K
 vcipher S1,S1,K
 vcipher S2,S2,K
 vcipher S3,S3,K
 vcipher S4,S4,K
 vcipher S5,S5,K
 vcipher S6,S6,K
 vcipher S7,S7,K
 addi r10,r10,0x10
 bdnz L8x_round_loop

 lxvd2x VSR(K),r10,KEYS
 vperm   K,K,K,swap_mask
 vcipherlast S0,S0,K
 vcipherlast S1,S1,K
 vcipherlast S2,S2,K
 vcipherlast S3,S3,K
 vcipherlast S4,S4,K
 vcipherlast S5,S5,K
 vcipherlast S6,S6,K
 vcipherlast S7,S7,K

IF_LE(`vperm S0,S0,S0,swap_mask
 vperm S1,S1,S1,swap_mask
 vperm S2,S2,S2,swap_mask
 vperm S3,S3,S3,swap_mask
 vperm S4,S4,S4,swap_mask
 vperm S5,S5,S5,swap_mask
 vperm S6,S6,S6,swap_mask
 vperm S7,S7,S7,swap_mask')

 stxvd2x VSR(S0),0,DST
 stxvd2x VSR(S1),r25,DST
 stxvd2x VSR(S2),r26,DST
 stxvd2x VSR(S3),r27,DST
 stxvd2x VSR(S4),r28,DST
 stxvd2x VSR(S5),r29,DST
 stxvd2x VSR(S6),r30,DST
 stxvd2x VSR(S7),r31,DST

 addi SRC,SRC,0x80
 addi DST,DST,0x80
 subic. r5,r5,1
 bne Lx8_loop

 ld r25,-56(SP);
 ld r26,-48(SP);
 ld r27,-40(SP);
 ld r28,-32(SP);
 ld r29,-24(SP);
 ld r30,-16(SP);
 ld r31,-8(SP);

 clrldi LENGTH,LENGTH,61

L4x:
 srdi   r5,LENGTH,2
 cmpldi   r5,0
 beq   L2x

 lxvd2x   VSR(K),0,KEYS
 vperm   K,K,K,swap_mask

 lxvd2x VSR(S0),0,SRC
 li  r9,0x10
 lxvd2x VSR(S1),r9,SRC
 addi   r9,r9,0x10
 lxvd2x VSR(S2),r9,SRC
 addi   r9,r9,0x10
 lxvd2x VSR(S3),r9,SRC

IF_LE(`vperm S0,S0,S0,swap_mask
 vperm S1,S1,S1,swap_mask
 vperm S2,S2,S2,swap_mask
 vperm S3,S3,S3,swap_mask')

 vxor S0,S0,K
 vxor S1,S1,K
 vxor S2,S2,K
 vxor S3,S3,K

 mtctr ROUNDS
 li r10,0x10
.align 5
L4x_round_loop:
 lxvd2x VSR(K),r10,KEYS
 vperm  K,K,K,swap_mask
 vcipher S0,S0,K
 vcipher S1,S1,K
 vcipher S2,S2,K
 vcipher S3,S3,K
 addi   r10,r10,0x10
 bdnz  L4x_round_loop

 lxvd2x VSR(K),r10,KEYS
 vperm   K,K,K,swap_mask
 vcipherlast S0,S0,K
 vcipherlast S1,S1,K
 vcipherlast S2,S2,K
 vcipherlast S3,S3,K

IF_LE(`vperm S0,S0,S0,swap_mask
 vperm S1,S1,S1,swap_mask
 vperm S2,S2,S2,swap_mask
 vperm S3,S3,S3,swap_mask')

 stxvd2x VSR(S0),0,DST
 li  r9,0x10
 stxvd2x VSR(S1),r9,DST
 addi   r9,r9,0x10
 stxvd2x VSR(S2),r9,DST
 addi  r9,r9,0x10
 stxvd2x VSR(S3),r9,DST

 addi   SRC,SRC,0x40
 addi   DST,DST,0x40

 clrldi LENGTH,LENGTH,62

L2x:
 srdi  r5,LENGTH,1
 cmpldi  r5,0
 beq   L1x

 lxvd2x VSR(K),0,KEYS
 vperm K,K,K,swap_mask

 lxvd2x VSR(S0),0,SRC
 li   r9,0x10
 lxvd2x VSR(S1),r9,SRC

IF_LE(`vperm S0,S0,S0,swap_mask
 vperm S1,S1,S1,swap_mask')

 vxor  S0,S0,K
 vxor   S1,S1,K

 mtctr   ROUNDS
 li  r10,0x10
.align 5
L2x_round_loop:
 lxvd2x VSR(K),r10,KEYS
 vperm  K,K,K,swap_mask
 vcipher S0,S0,K
 vcipher S1,S1,K
 addi   r10,r10,0x10
 bdnz   L2x_round_loop

 lxvd2x VSR(K),r10,KEYS
 vperm  K,K,K,swap_mask
 vcipherlast S0,S0,K
 vcipherlast S1,S1,K

IF_LE(`vperm S0,S0,S0,swap_mask
 vperm S1,S1,S1,swap_mask')

 stxvd2x VSR(S0),0,DST
 li  r9,0x10
 stxvd2x VSR(S1),r9,DST

 addi   SRC,SRC,0x20
 addi   DST,DST,0x20

 clrldi LENGTH,LENGTH,63

L1x:
 cmpldi LENGTH,0
 beq   Ldone

 lxvd2x VSR(K),0,KEYS
 vperm   K,K,K,swap_mask

 lxvd2x VSR(S0),0,SRC

IF_LE(`vperm S0,S0,S0,swap_mask')

 vxor   S0,S0,K

 mtctr   ROUNDS
 li   r10,0x10
.align 5
L1x_round_loop:
 lxvd2x VSR(K),r10,KEYS
 vperm  K,K,K,swap_mask
 vcipher S0,S0,K
 addi   r10,r10,0x10
 bdnz   L1x_round_loop

 lxvd2x VSR(K),r10,KEYS
 vperm  K,K,K,swap_mask
 vcipherlast S0,S0,K

IF_LE(`vperm S0,S0,S0,swap_mask')

 stxvd2x VSR(S0),0,DST

Ldone:
 blr
EPILOGUE(_nettle_aes_encrypt)

 .data
 .align 4
.swap_mask:
IF_LE(`.byte 8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7')
IF_BE(`.byte 3,2,1,0,7,6,5,4,11,10,9,8,15,14,13,12')
