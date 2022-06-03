#pragma once

/* target arch. */
#define FHK_ARCH_x86_64    1

/* target os. */
#define FHK_OS_WINDOWS     1
#define FHK_OS_POSIX       2

/* architecture detection. */
#ifndef FHK_ARCH
#if defined(__x86_64__)
#define FHK_ARCH           FHK_ARCH_x86_64
#endif
#endif

/* os detection. */
#ifndef FHK_OS
#if defined(_WIN32) || defined(__cygwin__)
#define FHK_OS             FHK_OS_WINDOWS
#else
#define FHK_OS             FHK_OS_POSIX
#endif
#endif

/* target features. */

#if FHK_OS == FHK_OS_WINDOWS
#define FHK_WINDOWS        1
#endif

#if FHK_OS == FHK_OS_POSIX
#define FHK_MMAP           1
#define FHK_ASM_CORO       1
#endif
