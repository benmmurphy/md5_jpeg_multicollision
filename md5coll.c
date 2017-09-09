/* MD5 collisions based on M. Stevens, "Fast Collision Attack on MD5",
 *  March 2006 (http://eprint.iacr.org/2006/104)
 * and the second-block differential paths from his MSc thesis
 * (Note that the Q[6] condition for the 1,1 case given in his thesis
 * appears to have an incorrect MSB, which had to be fixed.)
 * Recommend compiling with -NDEBUG to disable the asserts
 *
 * Copyright (c) 2017 Mako
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */
#include "md5.h"
#include <time.h>
#include <assert.h>
#include <stdio.h>
#include <string.h>

/* The four core functions - F1 is optimized somewhat */

/* #define F1(x, y, z) (x & y | ~x & z) */
#define F1(x, y, z) (z ^ (x & (y ^ z)))
#define F2(x, y, z) F1(z, x, y)
#define F3(x, y, z) (x ^ y ^ z)
#define F4(x, y, z) (y ^ (x | ~z))

/* This is the central step in the MD5 algorithm. */
#define MD5STEP(f, w, x, y, z, data, s) \
	( w += f(x, y, z) + data,  w = w<<s | w>>(32-s),  w += x )

/* Q[-3] = A; Q[-2] = D; Q[-1] = C; Q[0] = B */
#define MD5UNSTEP(Q, n, k, s) (((Q[n+1]-Q[n])<<(32-s)|(Q[n+1]-Q[n])>>s) - F1(Q[n], Q[n-1], Q[n-2]) - k - Q[n-3])
#define MD5UNSTEP2(Q, n, k, s) (((Q[n+1]-Q[n])<<(32-s)|(Q[n+1]-Q[n])>>s) - F2(Q[n], Q[n-1], Q[n-2]) - k - Q[n-3])

void CheckBlock1(uint32_t iv[4], uint32_t in[16]);

struct qcond {
	uint32_t mask, pmask, inv, cbits;
};

static const struct qcond qconds[] = {
        {},
        { 0xffffffff, 0x00000000, 0x00000000, 0x00000000 }, // 1
        { 0xffffffff, 0x00000000, 0x00000000, 0x00000000 }, // 2
        { 0xfe87bc3f, 0x00000000, 0x017841c0, 0x017843c0 }, // 3
        { 0x44000033, 0x0287bc00, 0x000002c0, 0x83ffffc8 }, // 4 tmask = 0x38000004
        { 0x00000000, 0x04000033, 0x41ffffc8, 0xffffffff }, // 5
        { 0x00000000, 0x00000000, 0xb84b82d6, 0xffffffff }, // 6
        { 0x68000084, 0x00000000, 0x02401b43, 0x97ffff7b }, // 7
        { 0x2b8f6e04, 0x40000000, 0x405090d3, 0xd47091fb }, // 8
        { 0x00000000, 0x40020000, 0x60040068, 0xf14690e9 }, // 9 tmask = 0x0eb94f16 t2mask = 0x00002000
        { 0x40000000, 0x00000000, 0x1040b089, 0xbfffff9f }, // 10 t2mask = 0x00000060
        { 0x10408008, 0x40002000, 0x4fbb5f16, 0xefbf7ff7 }, // 11
        { 0x1ed9df7f, 0x40200000, 0x40222080, 0xe1262080 }, // 12
        { 0x5efb4f77, 0x00000000, 0x20049008, 0xa104b088 }, // 13
        { 0x1fff5f77, 0x40000000, 0x4000a088, 0xe000a088 }, // 14
        { 0x5efe7ff7, 0x00010000, 0x80018000, 0xa1018008 }, // 15
        { 0x1ffdffff, 0x40020000, 0xe0020000, 0xe0020000 }, // 16
        { 0x3ffd7ff7, 0x40008008, 0xc0000000, 0xc0028008 }, // 17
        { 0x5ffdffff, 0x20000000, 0x80020000, 0xa0020000 }, // 18
        { 0x7ffdffff, 0x00000000, 0x80000000, 0x80020000 }, // 19
        { 0x7ffbffff, 0x00040000, 0x80040000, 0x80040000 }, // 20
        { 0x7ffdffff, 0x00020000, 0x80000000, 0x80020000 }, // 21
        { 0x7fffffff, 0x00000000, 0x80000000, 0x80000000 }, // 22
        { 0x7fffffff, 0x00000000, 0x00000000, 0x80000000 }, // 23
        { 0x7fffffff, 0x00000000, 0x80000000, 0x80000000 }, // 24
};

static const struct qcond qc00[] = {
        {},
        { 0x7dfdf7be, 0x80000000, 0x00020800, 0x82020841 }, // 1
        { 0x49a0e73e, 0x80000000, 0x201f0080, 0xb65f18c1 }, // 2
        { 0x0000040c, 0x8000e000, 0x3dcc1230, 0xfffffbf3 }, // 3
        { 0x00000004, 0x80000008, 0x93af7963, 0xfffffffb }, // 4
        { 0x00000004, 0x00000000, 0xbc429940, 0xfffffffb }, // 5
        { 0x00001044, 0x00000000, 0x22576eb9, 0xffffefbb }, // 6
        { 0x00200806, 0x00000000, 0xbd0430b0, 0xffdff7f9 }, // 7
        { 0x60050110, 0x00000004, 0x09581e2a, 0x9ffafeef }, // 8
        { 0x40044000, 0x00000000, 0xb9c20041, 0xbbca92ed }, // 9 tmask = 0x04310d12 t2mask = 0x00002000
        { 0x00000000, 0x00044000, 0xf28aa209, 0xf7ffffdf }, // 10 t2mask = 0x08000020
        { 0x12888008, 0x00012000, 0xa4754f57, 0xed777ff7 }, // 11
        { 0x1ed98d7f, 0x00200000, 0x41221200, 0xe1267280 }, // 12
        { 0x0efb1d77, 0x00000000, 0x3100c008, 0xf104e288 }, // 13
        { 0x0fff5d77, 0x00000000, 0x2000a288, 0xf000a288 }, // 14
        { 0x0efe7ff7, 0x00010000, 0xe0010008, 0xf1018008 }, // 15
        { 0x0ffdffff, 0x00020000, 0x50020000, 0xf0020000 }, // 16
        { 0x7ffd7ff7, 0x00008008, 0x80000000, 0x80028008 }, // 17
        { 0x5ffdffff, 0x20000000, 0x00020000, 0xa0020000 }, // 18
        { 0x7ffdffff, 0x00000000, 0x00020000, 0x80020000 }, // 19
        { 0x7ffbffff, 0x00040000, 0x00040000, 0x80040000 }, // 20
        { 0x7ffdffff, 0x00020000, 0x00000000, 0x80020000 }, // 21
        { 0x7fffffff, 0x00000000, 0x00000000, 0x80000000 }, // 22
        { 0x7fffffff, 0x00000000, 0x00000000, 0x80000000 }, // 23
        { 0x7fffffff, 0x00000000, 0x80000000, 0x80000000 }, // 24
};

static const struct qcond qc01[] = {
        {},
        { 0x7dfff39e, 0x80000020, 0x00000020, 0x82000c61 }, // 1
        { 0x4db0e03e, 0x80000000, 0x30460400, 0xb24f1fc1 }, // 2
        { 0x0c000008, 0x80800002, 0x103c32b0, 0xf3fffff7 }, // 3
        { 0x00000000, 0x88000000, 0xd157efd1, 0xffffffff }, // 4
        { 0x82000000, 0x00000000, 0x151900ab, 0x7dffffff }, // 5
        { 0x80000000, 0x00000000, 0x3347f06f, 0x7fffffff }, // 6
        { 0x00010130, 0x00000000, 0x79ea9e46, 0xfffefecf }, // 7
        { 0x40200800, 0x00000000, 0xa548136d, 0xbfdff7ff }, // 8
        { 0x00044000, 0x00000000, 0x394002f1, 0x3bca92fd }, // 9 tmask = 0x44310d02 t2mask = 0x80002000
        { 0x00000000, 0x00044000, 0xb288a208, 0xf7ffffcf }, // 10 t2mask = 0x08000030
        { 0x12808008, 0x00012000, 0xe4754f47, 0xed7f7ff7 }, // 11
        { 0x1ef18d7f, 0x00000000, 0x810a1200, 0xe10e7280 }, // 12
        { 0x1efb1d77, 0x00000000, 0x6104c008, 0xe104e288 }, // 13
        { 0x1fff5d77, 0x00000000, 0xe000a288, 0xe000a288 }, // 14
        { 0x1efe7ff7, 0x00010000, 0xa0010008, 0xe1018008 }, // 15
        { 0x1ffdffff, 0x00020000, 0x80020000, 0xe0020000 }, // 16
        { 0x7ffd7ff7, 0x00008008, 0x00000000, 0x80028008 }, // 17
        { 0x5ffdffff, 0x20000000, 0x80020000, 0xa0020000 }, // 18
        { 0x7ffdffff, 0x00000000, 0x80020000, 0x80020000 }, // 19
        { 0x7ffbffff, 0x00040000, 0x80040000, 0x80040000 }, // 20
        { 0x7ffdffff, 0x00020000, 0x80000000, 0x80020000 }, // 21
        { 0x7fffffff, 0x00000000, 0x80000000, 0x80000000 }, // 22
        { 0x7fffffff, 0x00000000, 0x00000000, 0x80000000 }, // 23
        { 0x7fffffff, 0x00000000, 0x80000000, 0x80000000 }, // 24
};

static const struct qcond qc10[] = {
        {},
        { 0x7dfdf6be, 0x80000000, 0x00000940, 0x82020941 }, // 1
        { 0x79b0c6ba, 0x80000000, 0x004c3800, 0x864f3945 }, // 2
        { 0x19300210, 0x80000082, 0x2401012c, 0xe6cffdef }, // 3
        { 0x10300000, 0x01000030, 0x6287dacb, 0xefcfffff }, // 4
        { 0x10000000, 0x00300000, 0x0289955c, 0xefffffff }, // 5
        { 0x00000000, 0x00000000, 0x919b0066, 0xffffffff }, // 6
        { 0x20444000, 0x00000000, 0x41091e65, 0xdfbbbfff }, // 7
        { 0x09040000, 0x00000000, 0xa0d81e79, 0xf6fbffff }, // 8
        { 0x00050000, 0x00000000, 0x508851c1, 0xdb8ad9d5 }, // 9 tmask = 0x2470042a t2mask = 0x00002200
        { 0x00010080, 0x00040000, 0x028aeb11, 0xf7feff7b }, // 10 t2mask = 0x08000004
        { 0x128b8110, 0x20002280, 0x2474446b, 0xed747eef }, // 11
        { 0x3ef38d7f, 0x00080000, 0x81081200, 0xc10c7280 }, // 12
        { 0x3efb1d77, 0x00000000, 0x8104c008, 0xc104e288 }, // 13
        { 0x5fff5d77, 0x00000000, 0x0000a288, 0xa000a288 }, // 14
        { 0x1efe7ff7, 0x00010000, 0xe0010008, 0xe1018008 }, // 15
        { 0x5ffdffff, 0x00020000, 0x80020000, 0xa0020000 }, // 16
        { 0x7ffd7ff7, 0x00008008, 0x00000000, 0x80028008 }, // 17
        { 0x5ffdffff, 0x20000000, 0x80020000, 0xa0020000 }, // 18
        { 0x7ffdffff, 0x00000000, 0x80020000, 0x80020000 }, // 19
        { 0x7ffbffff, 0x00040000, 0x80040000, 0x80040000 }, // 20
        { 0x7ffdffff, 0x00020000, 0x80000000, 0x80020000 }, // 21
        { 0x7fffffff, 0x00000000, 0x80000000, 0x80000000 }, // 22
        { 0x7fffffff, 0x00000000, 0x00000000, 0x80000000 }, // 23
        { 0x7fffffff, 0x00000000, 0x80000000, 0x80000000 }, // 24
};

static const struct qcond qc11[] = {
        {},
        { 0x7dfff79e, 0x80000020, 0x00000860, 0x82000861 }, // 1
        { 0x75bef63e, 0x80000000, 0x08410000, 0x8a4109c1 }, // 2
        { 0x10345614, 0x84000002, 0x0002a1a0, 0xefcba9eb }, // 3
        { 0x00145400, 0x00000014, 0x660aa0ca, 0xffebabff }, // 4
        { 0x80000000, 0x00145400, 0x1423a220, 0x7fffffff }, // 5
        { 0x00000000, 0x80000000, 0x89d40058, 0xffffffff }, // 6
        { 0x40000880, 0x00000000, 0x394bd45b, 0xbffff77f }, // 7
        { 0x00002090, 0x00000000, 0xa1d85c09, 0xffffdf6f }, // 8
        { 0x00044000, 0x00000000, 0x7a803161, 0x7b8ab16d }, // 9 tmask = 0x04710c12 t2mask = 0x80000280
        { 0x00002000, 0x00044000, 0xf28a82c9, 0xf7ffdfdf }, // 10 t2mask = 0x08000020
        { 0x128a8108, 0x00012280, 0x84754c57, 0xed757ef7 }, // 11
        { 0x9edb8d7f, 0x00200000, 0x21201200, 0x61247280 }, // 12
        { 0x3efb1d77, 0x80000000, 0x4104c008, 0xc104e288 }, // 13
        { 0x1fff5d77, 0x00000000, 0x8000a288, 0xe000a288 }, // 14
        { 0x1efe7ff7, 0x00010000, 0x20010008, 0xe1018008 }, // 15
        { 0x1ffdffff, 0x40020000, 0xc0020000, 0xe0020000 }, // 16
        { 0x3ffd7ff7, 0x40008008, 0xc0000000, 0xc0028008 }, // 17
        { 0x5ffdffff, 0x20000000, 0x00020000, 0xa0020000 }, // 18
        { 0x7ffdffff, 0x00000000, 0x00020000, 0x80020000 }, // 19
        { 0x7ffbffff, 0x00040000, 0x00040000, 0x80040000 }, // 20
        { 0x7ffdffff, 0x00020000, 0x00000000, 0x80020000 }, // 21
        { 0x7fffffff, 0x00000000, 0x00000000, 0x80000000 }, // 22
        { 0x7fffffff, 0x00000000, 0x00000000, 0x80000000 }, // 23
        { 0x7fffffff, 0x00000000, 0x80000000, 0x80000000 }, // 24
};


static const struct qcond* qconds2[4] = {
	qc00,qc01,qc10,qc11
};

static const uint32_t q9m9masks[4] = { // for second block
	0x04310d12, 0x44310d02, 0x2470042a, 0x04710c12
};

static const uint32_t q9q10masks[4] = { // for second block
	0x08002020, 0x88002030, 0x08002204, 0x880002a0
};
#define Q10MASK 0x8000034 // to split off Q10 part


#define Q_BAD(Q,n,qc) (((Q[n]&qc[n].cbits) ^ (Q[n-1]&qc[n].pmask)) != qc[n].inv)
	
static inline uint64_t xorshift64star(uint64_t *state) {
         uint64_t x = *state;
         x ^= x >> 12;
         x ^= x << 25;
         x ^= x >> 27;
         *state = x;
         return x * 0x2545F4914F6CDD1D;
}

static inline uint32_t getrand32(uint64_t *state) {
	return (uint32_t)xorshift64star(state);
}

#define HAS_BAD_CHARS(a) (badchars && (badchars[(a)&255] || badchars[((a)>>8)&255] || badchars[((a)>>16)&255] || badchars[((a)>>24)&255]))

#define Q9M9MASK 0x0eb94f16

static inline double timediff(struct timespec start, struct timespec end) {
	if(end.tv_nsec < start.tv_nsec) {
		return end.tv_sec-start.tv_sec-1+(1000000000+end.tv_nsec-start.tv_nsec)/1000000000.0;
	} else {
		return end.tv_sec-start.tv_sec+(end.tv_nsec-start.tv_nsec)/1000000000.0;
	}
}

void MD5CollideBlock0(uint32_t iv[4], uint32_t block[16], const char *badchars) {
	uint64_t rs = time(NULL) ^ 0xfeedface;
	rs = xorshift64star(&rs);
	uint32_t QandIV[28] = { iv[0], iv[3], iv[2], iv[1] };
	uint32_t *Q = QandIV+3;
	int success;
	uint32_t t;

#ifdef PROFILING
	struct timespec start, startinner, end;
	double overalltime = 0.0, innertime = 0.0;
	clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &start);
#endif
	while(1) {
		for(int i = 1; i < 17; i++) {
			Q[i] = ((getrand32(&rs) & qconds[i].mask) | (Q[i-1] & qconds[i].pmask)) ^ qconds[i].inv;
		}
		block[0] = MD5UNSTEP(Q, 0, 0xd76aa478, 7);
		if(HAS_BAD_CHARS(block[0])) continue;
		block[6] = MD5UNSTEP(Q, 6, 0xa8304613, 17);
		if(HAS_BAD_CHARS(block[6])) continue;
		block[11] = MD5UNSTEP(Q, 11, 0x895cd7be, 22);
		if(HAS_BAD_CHARS(block[11]) || HAS_BAD_CHARS(block[11]+(1<<15))) continue;
		block[14] = MD5UNSTEP(Q, 14, 0xa679438e, 17);
#ifdef JPEGHACK // nasty hack to insert a JPEG comment marker
		block[14] = (block[14] & 0xff000000) | 0x5000feff;
		Q[15] = Q[11]; MD5STEP(F1, Q[15], Q[14], Q[13], Q[12], block[14] + 0xa679438e, 17);
		if(Q_BAD(Q,15,qconds)) continue;
#else
		if(HAS_BAD_CHARS(block[14]) || HAS_BAD_CHARS(block[14]+(1U<<31))) continue;
#endif
#ifdef PDFHACK // nasty hack for PDF generation
		block[15] = 0x286f4420; // " Do("
		Q[16] = Q[12]; MD5STEP(F1, Q[16], Q[15], Q[14], Q[13], block[15] + 0x49b40821, 22);
		if(Q_BAD(Q,16,qconds)) continue;
#else
		block[15] = MD5UNSTEP(Q, 15, 0x49b40821, 22);
		if(HAS_BAD_CHARS(block[15])) continue;
#endif

		success = 0;
		for(int i = 0; i < 100; i++) {
			// choose Q[17], check Q[18..21]. Changes block[1..5]. 9 bitconditions.
			Q[17] = ((getrand32(&rs) & 0x3ffd7ff7) | (Q[16] & 0x40008008)) ^ 0xc0000000;
		
			Q[18] = Q[14]; MD5STEP(F2, Q[18], Q[17], Q[16], Q[15], block[6] + 0xc040b340, 9);
			if(Q_BAD(Q,18,qconds))
				continue;

			Q[19] = Q[15]; MD5STEP(F2, Q[19], Q[18], Q[17], Q[16], block[11] + 0x265e5a51, 14);
			if(Q_BAD(Q,19,qconds))
				continue;

			Q[20] = Q[16]; MD5STEP(F2, Q[20], Q[19], Q[18], Q[17], block[0] + 0xe9b6c7aa, 20);
			if(Q_BAD(Q,20,qconds))
				continue;

			block[1] = MD5UNSTEP2(Q, 16, 0xf61e2562, 5);
			Q[2] = Q[-2]; MD5STEP(F1, Q[2], Q[1], Q[0], Q[-1], block[1] + 0xe8c7b756, 12);
			if(HAS_BAD_CHARS(block[1])) continue;

			block[5] = MD5UNSTEP(Q, 5, 0x4787c62a, 12);
			Q[21] = Q[17]; MD5STEP(F2, Q[21], Q[20], Q[19], Q[18], block[5] + 0xd62f105d, 5);
			if(Q_BAD(Q,21,qconds))
				continue;
			if(HAS_BAD_CHARS(block[5])) continue;

			block[2] = MD5UNSTEP(Q, 2, 0x242070db, 17);
			if(HAS_BAD_CHARS(block[2])) continue;
			success = 1;
			break;
		}
		if(!success) continue;

		// Don't use Q[4] -> block[5] tunnel to fix Q[21] as probably
		// wouldn't work - we'd do:
		//    block[5] = const - (const ^ ourbits)
		//    Q[21] = LROT(const + block[5], 5) + Q[20]
		// the high-order bits get rotated back to the LSB
		// so barring a fortuitous carry, won't touch the condition
		
		// use 3-bit Q[9,10] -> block[10] tunnels to satisfy
		// 3 bitconditions on Q[22,23], T22 - affects block[8..10,12,13]
		for(int q10ctr = 0; q10ctr < 8; q10ctr++) {
			Q[9] = (Q[9] & ~0x00002000) | ((q10ctr<<13)&0x00002000);
			Q[10] = (Q[10] & ~0x00000060) | ((q10ctr<<4)&0x00000060);
			
			//block[8] = MD5UNSTEP(Q, 8, 0x698098d8, 7);
			//block[9] = MD5UNSTEP(Q, 9, 0x8b44f7af, 12);
			block[10] = MD5UNSTEP(Q, 10, 0xffff5bb1, 17);
			if(HAS_BAD_CHARS(block[10])) continue;
			assert(block[11] == MD5UNSTEP(Q, 11, 0x895cd7be, 22));
			//block[12] = MD5UNSTEP(Q, 12, 0x6b901122, 7);
			block[13] = MD5UNSTEP(Q, 13, 0xfd987193, 12);
			if(HAS_BAD_CHARS(block[13])) continue;
				
			Q[22] = Q[18]; MD5STEP(F2, Q[22], Q[21], Q[20], Q[19], block[10] + 0x02441453, 9);
			if((Q[22] & 0x80000000) == 0) continue;

			Q[23] = Q[19]; MD5STEP(F2, Q[23], Q[22], Q[21], Q[20], block[15] + 0xd8a1e681, 14);
			if((Q[23] & 0x80000000) != 0) continue;
			t = Q[19] + F2(Q[22], Q[21], Q[20]) +  block[15] + 0xd8a1e681;
			if(t & (1<<17)) continue;
			t = t<<14 | t>>(32-14);
			t += Q[22];
			assert(Q[23] == t);
				
			// precalculating these speeds up the critical inner loop by ~20%
			// while some of these could be hoisted up a loop level, probably pointless
			uint32_t part8 = F1(Q[8], Q[7], Q[6]) + 0x698098d8 + Q[5];
			uint32_t part9 = 0x8b44f7af + Q[6];
			uint32_t part12 = ((Q[13]-Q[12])<<(32-7)|(Q[13]-Q[12])>>7) - F1(Q[12], Q[11], Q[10]) -  0x6b901122;
			uint32_t q9base = Q[9]&~Q9M9MASK; // may be set from last iteration

			// use 4-bit Q[4] -> block[4] tunnel with cond Q[5]=0 && Q[6]=1
			// changes block[3,4,7] (not 5,6 due to tunnel - protects Q[..23])
			for(int q4ctr = 0; q4ctr < 16; q4ctr++) {
				Q[4] = (Q[4] & ~0x38000004) | (((q4ctr<<2)|(q4ctr<<26)) & 0x38000004);

				block[3] = MD5UNSTEP(Q, 3, 0xc1bdceee, 22);
				if(HAS_BAD_CHARS(block[3])) continue;
				block[4] = MD5UNSTEP(Q, 4, 0xf57c0faf, 7);
				if(HAS_BAD_CHARS(block[4]) || HAS_BAD_CHARS(block[4]+(1U<<31))) continue;
				assert(block[5] == MD5UNSTEP(Q, 5, 0x4787c62a, 12));
				assert(block[6] == MD5UNSTEP(Q, 6, 0xa8304613, 17));
				block[7] = MD5UNSTEP(Q, 7, 0xfd469501, 22);
				if(HAS_BAD_CHARS(block[7])) continue;
								      
				Q[24] = Q[20]; MD5STEP(F2, Q[24], Q[23], Q[22], Q[21], block[4] + 0xe7d3fbc8, 20); 
				if((Q[24] & 0x80000000) == 0) continue;

#if 1
				for(int i = 17; i < 25; i++) {
					assert(!Q_BAD(Q,i,qconds));
				}
#endif

	 
#ifdef PROFILING
				clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &startinner);
#endif
				// use 16-bit Q[9] -> m[9] tunnel with cond Q[10]=0 && Q[11]=1
				// affects block[8, 9, 12], preserves block[10,11]
				// we seem to spend about 99.9% of our time in this inner loop
				for(int q9ctr = 0; q9ctr < (1<<16); q9ctr++) {
					uint32_t a, b, c, d;
					// there's probably some clever way to compute these shifts
					// couldn't tell you what it is though - I brute-forced it!
					Q[9] = q9base | (((q9ctr)^(q9ctr<<8)^(q9ctr<<14))&Q9M9MASK);

					block[8] = ((Q[9]-Q[8])<<(32-7)|(Q[9]-Q[8])>>7) - part8;
					assert(block[8] == MD5UNSTEP(Q, 8, 0x698098d8, 7));
					if(HAS_BAD_CHARS(block[8])) continue;

					block[9] = ((Q[10]-Q[9])<<(32-12)|(Q[10]-Q[9])>>12) - F1(Q[9], Q[8], Q[7]) - part9;
					assert(block[9] == MD5UNSTEP(Q, 9, 0x8b44f7af, 12));
					if(HAS_BAD_CHARS(block[9])) continue;

					assert(block[10] == MD5UNSTEP(Q, 10, 0xffff5bb1, 17));
					assert(block[11] == MD5UNSTEP(Q, 11, 0x895cd7be, 22));

					block[12] = part12 - Q[9];
					assert(block[12] == MD5UNSTEP(Q, 12, 0x6b901122, 7));
					if(HAS_BAD_CHARS(block[12])) continue;
			
					a = Q[21]; b = Q[24]; c = Q[23]; d = Q[22];

					MD5STEP(F2, a, b, c, d, block[9] + 0x21e1cde6, 5); // 25
					MD5STEP(F2, d, a, b, c, block[14] + 0xc33707d6, 9);
					MD5STEP(F2, c, d, a, b, block[3] + 0xf4d50d87, 14);
					MD5STEP(F2, b, c, d, a, block[8] + 0x455a14ed, 20);
					MD5STEP(F2, a, b, c, d, block[13] + 0xa9e3e905, 5);
					MD5STEP(F2, d, a, b, c, block[2] + 0xfcefa3f8, 9);
					MD5STEP(F2, c, d, a, b, block[7] + 0x676f02d9, 14);
					MD5STEP(F2, b, c, d, a, block[12] + 0x8d2a4c8a, 20);

					MD5STEP(F3, a, b, c, d, block[5] + 0xfffa3942, 4); // 33
					MD5STEP(F3, d, a, b, c, block[8] + 0x8771f681, 11); // 34
					/* equivalent to MD5STEP(F3, c, d, a, b, block[11] + 0x6d9d6122, 16); */
					c += F3(d, a, b) + block[11] + 0x6d9d6122;
					if(c & (1<<15)) continue;
					c = c<<16 | c>>16;
					c += d;
					MD5STEP(F3, b, c, d, a, block[14] + 0xfde5380c, 23);
					MD5STEP(F3, a, b, c, d, block[1] + 0xa4beea44, 4);
					MD5STEP(F3, d, a, b, c, block[4] + 0x4bdecfa9, 11);
					MD5STEP(F3, c, d, a, b, block[7] + 0xf6bb4b60, 16);
					MD5STEP(F3, b, c, d, a, block[10] + 0xbebfbc70, 23);
					MD5STEP(F3, a, b, c, d, block[13] + 0x289b7ec6, 4);
					MD5STEP(F3, d, a, b, c, block[0] + 0xeaa127fa, 11);
					MD5STEP(F3, c, d, a, b, block[3] + 0xd4ef3085, 16);
					MD5STEP(F3, b, c, d, a, block[6] + 0x04881d05, 23);
					MD5STEP(F3, a, b, c, d, block[9] + 0xd9d4d039, 4);
					MD5STEP(F3, d, a, b, c, block[12] + 0xe6db99e5, 11); // 46
					MD5STEP(F3, c, d, a, b, block[15] + 0x1fa27cf8, 16); // 47
					MD5STEP(F3, b, c, d, a, block[2] + 0xc4ac5665, 23); // 48
					if(((d^b)&0x80000000) != 0) continue; // I

					MD5STEP(F4, a, b, c, d, block[0] + 0xf4292244, 6); //49
					if(((a^c)&0x80000000) != 0) continue; // J
					MD5STEP(F4, d, a, b, c, block[7] + 0x432aff97, 10); // 50
					if(((d^b)&0x80000000) == 0) continue; // K = ~I
					MD5STEP(F4, c, d, a, b, block[14] + 0xab9423a7, 15); // 51
					if(((a^c)&0x80000000) != 0) continue; // J
					MD5STEP(F4, b, c, d, a, block[5] + 0xfc93a039, 21); // 52
					if(((d^b)&0x80000000) != 0) continue; // K
					MD5STEP(F4, a, b, c, d, block[12] + 0x655b59c3, 6); // 53
					if(((a^c)&0x80000000) != 0) continue; // J
					MD5STEP(F4, d, a, b, c, block[3] + 0x8f0ccc92, 10); // 54
					if(((d^b)&0x80000000) != 0) continue; // K
					MD5STEP(F4, c, d, a, b, block[10] + 0xffeff47d, 15); // 55
					if(((a^c)&0x80000000) != 0) continue; // J
					MD5STEP(F4, b, c, d, a, block[1] + 0x85845dd1, 21); // 56
					if(((d^b)&0x80000000) != 0) continue; // K
					MD5STEP(F4, a, b, c, d, block[8] + 0x6fa87e4f, 6); // 57
					if(((a^c)&0x80000000) != 0) continue; // J
					MD5STEP(F4, d, a, b, c, block[15] + 0xfe2ce6e0, 10); // 58
					if(((d^b)&0x80000000) != 0) continue; // K
					MD5STEP(F4, c, d, a, b, block[6] + 0xa3014314, 15); // 59
					if(((a^c)&0x80000000) != 0) continue; // J
					MD5STEP(F4, b, c, d, a, block[13] + 0x4e0811a1, 21); // 60
					if(((d^b)&0x80000000) == 0) continue; // I = ~K
					MD5STEP(F4, a, b, c, d, block[4] + 0xf7537e82, 6); // 61
					if(((a^c)&0x80000000) != 0) continue; // J
					MD5STEP(F4, d, a, b, c, block[11] + 0xbd3af235, 10); // 62
					if(((d^b)&0x80000000) != 0) continue; // I
					MD5STEP(F4, c, d, a, b, block[2] + 0x2ad7d2bb, 15); // 63
					if(((a^c)&0x80000000) != 0) continue; // J
					MD5STEP(F4, b, c, d, a, block[9] + 0xeb86d391, 21); // 64

					uint32_t newiv1 = iv[1]+b, newiv2 = iv[2]+c, newiv3 = iv[3] + d;

					if( (newiv1&0x02000000) || ((newiv2^newiv1)&0x82000000) ||
					    ((newiv3^newiv2)&0x82000000) || ((newiv2^newiv1) & 1))
						continue;
					
					printf("-"); fflush(stdout);						

					uint32_t block2[16];
					memcpy(block2, block, 16*sizeof(uint32_t));
					block2[4] += 1U<<31;
					block2[11] += 1U<<15;
					block2[14] += 1U<<31;

					uint32_t iv1[4], iv2[4];
					memcpy(iv1, iv, 4*sizeof(uint32_t));
					memcpy(iv2, iv, 4*sizeof(uint32_t));
					MD5Transform(iv1, block); // technically redundant, but not worth getting rid of
					MD5Transform(iv2, block2);
					assert(iv[0]+a == iv1[0] && iv[1]+b == iv1[1]  && iv[2]+c == iv1[2] && iv[3]+d == iv1[3]);
					if(iv2[0] == iv1[0] + 0x80000000 && iv2[1] == iv1[1] + 0x82000000 &&
					   iv2[2] == iv1[2] + 0x82000000 && iv2[3] == iv1[3] + 0x82000000) {
#ifdef PROFILING
						clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &end);
						overalltime = timediff(start, end);
						innertime += timediff(startinner, end);
						printf("\ninner: %f total: %f\n", innertime, overalltime);
#endif
						return;
					}
				}
#ifdef PROFILING
				clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &end);
				innertime += timediff(startinner, end);
#endif
			}
		}
	}
}

// WARNING: some of the blocks are constrained enough that using badchars
// may potentially hang forever. You have been warned
void MD5CollideBlock1(uint32_t iv[4], uint32_t block[16], const char *badchars) {
	uint64_t rs = time(NULL) ^ 0xdeadf00d;
	rs = xorshift64star(&rs);
	uint32_t QandIV[25] = { iv[0], iv[3], iv[2], iv[1] };
	uint32_t *Q = QandIV+3;
	int success, numq9q10;
	uint32_t q9m9bits[1<<9], q9q10bits[1<<6];
	int path = (iv[1]&1) | ((iv[1] >> 5) & 2);
	const struct qcond *qc = qconds2[path];
	printf("(%i%i)", path>>1, path&1); fflush(stdout);
	// precompute this as it's in the inner loop and too complicated
	// if we didn't have to handle multiple paths with different tunnels
	// we could use the same trick as for the previous block, but we do.
	for(int i = 0; i < (1<<9); i++) {
		uint32_t bits = 0; int offset = 0;
		for(int j = 0; j < 9; j++) {
			while((q9m9masks[path] & (1U<<offset)) == 0) offset++;
			if(i & (1<<j))
				bits |= 1<<offset;
			offset++;
		}
		assert(offset <= 32);
		assert((bits&q9m9masks[path]) == bits);
		if(i>0) assert(bits > q9m9bits[i-1]);
		q9m9bits[i] = bits;
	}
	for(int i = 0; ; i++) {
		uint32_t bits = 0; int offset = 0;
		for(int j = 0; i > (1<<j)-1 ; j++) {
			while(offset<32 && (q9q10masks[path] & (1U<<offset)) == 0) offset++;
			if(offset >= 32) { offset = 33; break; }
			if(i & (1<<j))
				bits |= 1<<offset;
			offset++;
		}
		if(offset > 32) {
			numq9q10 = i; break;
		}
		assert((bits&q9q10masks[path]) == bits);
		if(i>0) assert(bits > q9q10bits[i-1]);
		q9q10bits[i] = bits;
	}
	//printf("DEBUG: num q9q10=%i\n", numq9q10);
	
	while(1) {
		// obnoxious special-case hack since we don't have Q[1] at this point
		Q[2] = ((getrand32(&rs) & qc[2].mask) | (Q[0] & qc[2].pmask)) ^ qc[2].inv;
		for(int i = 3; i < 17; i++) {
			Q[i] = ((getrand32(&rs) & qc[i].mask) | (Q[i-1] & qc[i].pmask)) ^ qc[i].inv;
		}
		block[5] = MD5UNSTEP(Q, 5, 0x4787c62a, 12);
		if(HAS_BAD_CHARS(block[5])) continue;
		block[6] = MD5UNSTEP(Q, 6, 0xa8304613, 17);
		if(HAS_BAD_CHARS(block[6])) continue;
		block[7] = MD5UNSTEP(Q, 7, 0xfd469501, 22);
		if(HAS_BAD_CHARS(block[7])) continue;
		//block[8] = MD5UNSTEP(Q, 8, 0x698098d8, 7);
		//block[9] = MD5UNSTEP(Q, 9, 0x8b44f7af, 12);
		//block[10] = MD5UNSTEP(Q, 10, 0xffff5bb1, 17);
		block[11] = MD5UNSTEP(Q, 11, 0x895cd7be, 22);
		if(HAS_BAD_CHARS(block[11]) || HAS_BAD_CHARS(block[11]-(1U<<15))) continue;
		//block[12] = MD5UNSTEP(Q, 12, 0x6b901122, 7);
		//block[13] = MD5UNSTEP(Q, 13, 0xfd987193, 12);
		block[14] = MD5UNSTEP(Q, 14, 0xa679438e, 17);
		if(HAS_BAD_CHARS(block[14]) || HAS_BAD_CHARS(block[14]-(1U<<31))) continue;
		block[15] = MD5UNSTEP(Q, 15, 0x49b40821, 22);
		if(HAS_BAD_CHARS(block[15])) continue;
		success = 0;
		for(int i = 0; i < 2000; i++) {
			Q[1] = ((getrand32(&rs) & qc[1].mask) | (Q[0] & qc[1].pmask)) ^ qc[1].inv;
			block[0] = MD5UNSTEP(Q, 0, 0xd76aa478, 7);
			if(HAS_BAD_CHARS(block[0])) continue;
			block[1] = MD5UNSTEP(Q, 1, 0xe8c7b756, 12);
			if(HAS_BAD_CHARS(block[1])) continue;
			//block[2] = MD5UNSTEP(Q, 2, 0x242070db, 17);
			block[3] = MD5UNSTEP(Q, 3, 0xc1bdceee, 22);
			if(HAS_BAD_CHARS(block[3])) continue;
			block[4] = MD5UNSTEP(Q, 4, 0xf57c0faf, 7);
			if(HAS_BAD_CHARS(block[4]) || HAS_BAD_CHARS(block[4]-(1U<<31))) continue;

			Q[17] = Q[13]; MD5STEP(F2, Q[17], Q[16], Q[15], Q[14], block[1] + 0xf61e2562, 5);
			if(Q_BAD(Q,17,qc))
				continue;
			
			Q[18] = Q[14]; MD5STEP(F2, Q[18], Q[17], Q[16], Q[15], block[6] + 0xc040b340, 9);
			if(Q_BAD(Q,18,qc))
				continue;

			Q[19] = Q[15]; MD5STEP(F2, Q[19], Q[18], Q[17], Q[16], block[11] + 0x265e5a51, 14);
			if(Q_BAD(Q,19,qc))
				continue;

			Q[20] = Q[16]; MD5STEP(F2, Q[20], Q[19], Q[18], Q[17], block[0] + 0xe9b6c7aa, 20);
			if(Q_BAD(Q,20,qc))
				continue;

			Q[21] = Q[17]; MD5STEP(F2, Q[21], Q[20], Q[19], Q[18], block[5] + 0xd62f105d, 5);
			if(Q_BAD(Q,21,qc))
				continue;

			block[2] = MD5UNSTEP(Q, 2, 0x242070db, 17);
			if(HAS_BAD_CHARS(block[2])) continue;
			success = 1;
			break;
		}

		if(!success)
			continue;


		uint32_t q9base = Q[9];
		assert((q9base&q9m9masks[path]) == 0);
		assert((q9base&q9q10masks[path]&~Q10MASK) == 0);

		uint32_t q10base = Q[10];
		assert((q10base&q9q10masks[path]&Q10MASK) == 0);
		for(int q10ctr = 0; q10ctr < numq9q10; q10ctr++) {
			uint32_t a2, b2, c2, d2;
			uint32_t q9save = Q[9] = q9base | (q9q10bits[q10ctr]&~Q10MASK);
			Q[10] = q10base | (q9q10bits[q10ctr]&Q10MASK);

			block[10] = MD5UNSTEP(Q, 10, 0xffff5bb1, 17);
			if(HAS_BAD_CHARS(block[10])) continue;
			assert(block[11] == MD5UNSTEP(Q, 11, 0x895cd7be, 22));
			a2 = Q[21]; b2 = Q[20]; c2 = Q[19]; d2 = Q[18];
			MD5STEP(F2, d2, a2, b2, c2, block[10] + 0x02441453, 9); // 22
			if((d2 & 0x80000000) != qc[22].inv) continue;

			// same as MD5STEP(F2, c2, d2, a2, b2, block[15] + 0xd8a1e681, 14); // 23
			c2 = c2 + F2(d2, a2, b2) + block[15] + 0xd8a1e681;
			if((c2 & (1<<17)) == 0) continue; // opposite of first block
			c2 = c2<<14 | c2>>(32-14);
			c2 += d2;
			if((c2 & 0x80000000) != qc[23].inv) continue;

			MD5STEP(F2, b2, c2, d2, a2, block[4] + 0xe7d3fbc8, 20); // 24
			if((b2 & 0x80000000) == 0) continue;

			block[13] = MD5UNSTEP(Q, 13, 0xfd987193, 12);
			if(HAS_BAD_CHARS(block[13])) continue;

			for(int q9ctr = 0; q9ctr < (1<<9); q9ctr++) {
				uint32_t a = a2, b = b2, c = c2, d = d2;
				Q[9] = q9save | q9m9bits[q9ctr];

				block[8] = MD5UNSTEP(Q, 8, 0x698098d8, 7);
				if(HAS_BAD_CHARS(block[8])) continue;
				block[9] = MD5UNSTEP(Q, 9, 0x8b44f7af, 12);
				if(HAS_BAD_CHARS(block[9])) continue;
				assert(block[10] == MD5UNSTEP(Q, 10, 0xffff5bb1, 17));
				assert(block[11] == MD5UNSTEP(Q, 11, 0x895cd7be, 22));
				block[12] = MD5UNSTEP(Q, 12, 0x6b901122, 7);
				if(HAS_BAD_CHARS(block[12])) continue;

				MD5STEP(F2, a, b, c, d, block[9] + 0x21e1cde6, 5); // 25
				MD5STEP(F2, d, a, b, c, block[14] + 0xc33707d6, 9);
				MD5STEP(F2, c, d, a, b, block[3] + 0xf4d50d87, 14);
				MD5STEP(F2, b, c, d, a, block[8] + 0x455a14ed, 20);
				MD5STEP(F2, a, b, c, d, block[13] + 0xa9e3e905, 5);
				MD5STEP(F2, d, a, b, c, block[2] + 0xfcefa3f8, 9);
				MD5STEP(F2, c, d, a, b, block[7] + 0x676f02d9, 14);
				MD5STEP(F2, b, c, d, a, block[12] + 0x8d2a4c8a, 20);

				MD5STEP(F3, a, b, c, d, block[5] + 0xfffa3942, 4); // 33
				MD5STEP(F3, d, a, b, c, block[8] + 0x8771f681, 11); // 34
				// same as MD5STEP(F3, c, d, a, b, block[11] + 0x6d9d6122, 16); // 35
				c += F3(d, a, b) + block[11] + 0x6d9d6122;
				if((c & (1<<15)) == 0) continue; // opposite of first block
				c = c<<16 | c>>16;
				c += d;
				MD5STEP(F3, b, c, d, a, block[14] + 0xfde5380c, 23);
				MD5STEP(F3, a, b, c, d, block[1] + 0xa4beea44, 4);
				MD5STEP(F3, d, a, b, c, block[4] + 0x4bdecfa9, 11);
				MD5STEP(F3, c, d, a, b, block[7] + 0xf6bb4b60, 16);
				MD5STEP(F3, b, c, d, a, block[10] + 0xbebfbc70, 23);
				MD5STEP(F3, a, b, c, d, block[13] + 0x289b7ec6, 4);
				MD5STEP(F3, d, a, b, c, block[0] + 0xeaa127fa, 11);
				MD5STEP(F3, c, d, a, b, block[3] + 0xd4ef3085, 16);
				MD5STEP(F3, b, c, d, a, block[6] + 0x04881d05, 23);
				MD5STEP(F3, a, b, c, d, block[9] + 0xd9d4d039, 4);
				MD5STEP(F3, d, a, b, c, block[12] + 0xe6db99e5, 11); // 46
				MD5STEP(F3, c, d, a, b, block[15] + 0x1fa27cf8, 16); // 47
				MD5STEP(F3, b, c, d, a, block[2] + 0xc4ac5665, 23); // 48
				if(((d^b)&0x80000000) != 0) continue; // I

				MD5STEP(F4, a, b, c, d, block[0] + 0xf4292244, 6); //49
				if(((a^c)&0x80000000) != 0) continue; // J
				MD5STEP(F4, d, a, b, c, block[7] + 0x432aff97, 10); // 50
				if(((d^b)&0x80000000) == 0) continue; // K = ~I
				MD5STEP(F4, c, d, a, b, block[14] + 0xab9423a7, 15); // 51
				if(((a^c)&0x80000000) != 0) continue; // J
				MD5STEP(F4, b, c, d, a, block[5] + 0xfc93a039, 21); // 52
				if(((d^b)&0x80000000) != 0) continue; // K
				MD5STEP(F4, a, b, c, d, block[12] + 0x655b59c3, 6); // 53
				if(((a^c)&0x80000000) != 0) continue; // J
				MD5STEP(F4, d, a, b, c, block[3] + 0x8f0ccc92, 10); // 54
				if(((d^b)&0x80000000) != 0) continue; // K
				MD5STEP(F4, c, d, a, b, block[10] + 0xffeff47d, 15); // 55
				if(((a^c)&0x80000000) != 0) continue; // J
				MD5STEP(F4, b, c, d, a, block[1] + 0x85845dd1, 21); // 56
				if(((d^b)&0x80000000) != 0) continue; // K
				MD5STEP(F4, a, b, c, d, block[8] + 0x6fa87e4f, 6); // 57
				if(((a^c)&0x80000000) != 0) continue; // J
				MD5STEP(F4, d, a, b, c, block[15] + 0xfe2ce6e0, 10); // 58
				if(((d^b)&0x80000000) != 0) continue; // K
				MD5STEP(F4, c, d, a, b, block[6] + 0xa3014314, 15); // 59
				if(((a^c)&0x80000000) != 0) continue; // J
				MD5STEP(F4, b, c, d, a, block[13] + 0x4e0811a1, 21); // 60
				if(((d^b)&0x80000000) == 0) continue; // I = ~K
				MD5STEP(F4, a, b, c, d, block[4] + 0xf7537e82, 6); // 61
				if(((a^c)&0x80000000) != 0) continue; // J
				MD5STEP(F4, d, a, b, c, block[11] + 0xbd3af235, 10); // 62
				if(((d^b)&0x80000000) != 0) continue; // I
				MD5STEP(F4, c, d, a, b, block[2] + 0x2ad7d2bb, 15); // 63
				if(((a^c)&0x80000000) != 0) continue; // J
				MD5STEP(F4, b, c, d, a, block[9] + 0xeb86d391, 21); // 64

				printf("*"); fflush(stdout);

				uint32_t block2[16];
				memcpy(block2, block, 16*sizeof(uint32_t));
				block2[4] -= 1U<<31;
				block2[11] -= 1U<<15;
				block2[14] -= 1U<<31;

				uint32_t iv1[4], iv2[4];
				memcpy(iv1, iv, 4*sizeof(uint32_t));
				iv2[0] = iv1[0] + 0x80000000; iv2[1] = iv1[1] + 0x82000000;
				iv2[2] = iv1[2] + 0x82000000; iv2[3] = iv1[3] + 0x82000000;
				MD5Transform(iv1, block);
				MD5Transform(iv2, block2);
				assert(iv[0] + a == iv1[0] && iv[1] +b == iv1[1]  && iv[2]+c == iv1[2] && iv[3]+d == iv1[3]);
				if(iv2[0] == iv1[0] && iv2[1] == iv1[1] && iv2[2] == iv1[2] && iv2[3] == iv1[3])
					return;
			}
			
		}
	}
}

#ifdef BENCHMARK
#define NUM_RUNS 100
int main(void) {
	uint32_t iv[4] = { 0x67452301,0xefcdab89,0x98badcfe,0x10325476  };
	uint32_t block[16], block2[16];
	uint64_t rs = time(NULL);
	struct timespec start, end;
	double totaltime0 = 0.0, totaltime1 = 0.0;
	rs = xorshift64star(&rs);
#if 1
	for(int count = 0; count < NUM_RUNS; count++) {
		do{
			for(int i = 0; i < 4; i++)
				iv[i] = getrand32(&rs);
		} while ( ((iv[2]>>25)&1) == ((iv[2]>>24)&1) || ((iv[3]>>25)&1) != ((iv[3]>>24)&1));
		
		clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &start);
		MD5CollideBlock0(iv, block, NULL);
		clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &end);
		double time0 = timediff(start,end);
		totaltime0 += time0;

		MD5Transform(iv, block);
		
		clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &start);
		MD5CollideBlock1(iv, block2, NULL);
		clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &end);
		double time1 = timediff(start,end);
		totaltime1 += time1;

		printf("\nblock0 %f s, block1 %f s\n",time0,time1);
	}
	printf("\n\naverage: block0 %f s, block1 %f s\n",totaltime0/NUM_RUNS,totaltime1/NUM_RUNS);
}
#endif	

#endif

#ifdef STANDALONE
static const char unclean_map[256] = {
  1,0,0,0,0,0,0,0,0,1,1,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  1,0,0,1,0,1,0,0,1,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,0,
  1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1
};

#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>

int main(void) {
	uint32_t iv[4] = { 0x67452301,0xefcdab89,0x98badcfe,0x10325476  };
	uint32_t block[16], block2[16];
	uint64_t rs = time(NULL);
	rs = xorshift64star(&rs);
#if 1
	do{
	for(int i = 0; i < 4; i++)
		iv[i] = getrand32(&rs);
	} while ( ((iv[2]>>25)&1) == ((iv[2]>>24)&1) || ((iv[3]>>25)&1) != ((iv[3]>>24)&1));
#endif	
	for(int i = 0; i < 4; i++)
		printf("%08x", iv[i]);
	printf("\n");
	MD5CollideBlock0(iv, block, unclean_map);
	for(int i = 0; i < 16; i++)
		printf("%08x", block[i]);
	printf("\n");
	MD5Transform(iv, block);
	MD5CollideBlock1(iv, block2, NULL /*unclean_map*/);
	for(int i = 0; i < 16; i++)
		printf("%08x", block2[i]);
	printf("\n");
	FILE *f = fopen("demoa.tmp","wb");
	fwrite(block, 4, 16, f);
	fwrite(block2, 4, 16, f);
	fclose(f);
	block[4] += 1U<<31;
	block[11] += 1U<<15;
	block[14] += 1U<<31;
	block2[4] -= 1U<<31;
	block2[11] -= 1U<<15;
	block2[14] -= 1U<<31;
	f = fopen("demob.tmp","wb");
	fwrite(block, 4, 16, f);
	fwrite(block2, 4, 16, f);
	fclose(f);
}
#endif
