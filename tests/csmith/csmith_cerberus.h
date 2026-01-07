/* Csmith runtime header for Cerberus interpreter testing
 *
 * This is a modified version of csmith_minimal.h that:
 * 1. Does NOT use printf (not supported in our Lean interpreter)
 * 2. Returns the checksum via exit() so we can compare return values
 *
 * Usage: Compile csmith tests with:
 *   -DCSMITH_MINIMAL -include tests/csmith/csmith_cerberus.h
 *
 * Or modify tests to #include "csmith_cerberus.h" instead of "csmith.h"
 */

#ifndef CSMITH_CERBERUS_H
#define CSMITH_CERBERUS_H

/* Integer types from custom_stdint_x86.h */
typedef signed char int8_t;
typedef unsigned char uint8_t;
typedef short int16_t;
typedef unsigned short uint16_t;
typedef int int32_t;
typedef unsigned int uint32_t;
typedef long long int64_t;
typedef unsigned long long uint64_t;

/* Limits from custom_limits.h */
#define INT8_MAX 127
#define INT8_MIN (-128)
#define UINT8_MAX 255
#define INT16_MAX 32767
#define INT16_MIN (-32768)
#define UINT16_MAX 65535
#define INT32_MAX 2147483647
#define INT32_MIN (-2147483647-1)
#define UINT32_MAX 4294967295U
#define INT64_MAX 9223372036854775807LL
#define INT64_MIN (-9223372036854775807LL-1)
#define UINT64_MAX 18446744073709551615ULL

#define STATIC static
#define UNDEFINED(__val) (__val)
#define LOG_INDEX
#define LOG_EXEC
#define FUNC_NAME(x) (safe_##x)
#define assert(x)
#define _CSMITH_BITFIELD(x) ((x>32)?(x%32):x)

/* Include safe math operations */
#include "safe_math.h"

/* Global checksum context */
static uint64_t crc32_context = 0;

/* No-op platform init - NOT inline so Cerberus exports the body */
static void platform_main_begin(void) {}
static void crc32_gentab(void) {}

/* transparent_crc: just accumulate into checksum, no printing
 * NOT inline so Cerberus exports the body */
static void
transparent_crc(uint64_t val, char* vname, int flag)
{
    (void)vname;  /* unused */
    (void)flag;   /* unused */
    crc32_context += val;
}

/* transparent_crc_bytes: accumulate bytes into checksum
 * NOT inline so Cerberus exports the body */
static void
transparent_crc_bytes(char *ptr, int nbytes, char* vname, int flag)
{
    int i;
    (void)vname;
    (void)flag;
    for (i = 0; i < nbytes; i++) {
        crc32_context += ptr[i];
    }
}

/* exit() declaration - provided by Cerberus runtime */
void exit(int status);

/* printf declaration - needed for array index printing in csmith tests.
 * These calls are guarded by print_hash_value which is 0, so they never
 * actually execute. We just need the declaration for compilation. */
int printf(const char *format, ...);

/* platform_main_end: exit with checksum as return code (no printf needed!)
 * We use the low byte of the checksum as the exit code (0-255).
 * This allows both Cerberus and our Lean interpreter to return the
 * same value, which we can compare for correctness.
 * NOT inline so Cerberus exports the body */
static void
platform_main_end(uint64_t x, int flag)
{
    (void)flag;
    exit((int)(x & 0xFF));
}

#endif /* CSMITH_CERBERUS_H */
