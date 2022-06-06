#pragma once

#define jointok__(a,b)     a##b
#define jointok_(a,b)      jointok__(a,b)

/* target arch. */
#define FHK_ARCH_x86_64    1

/* target os. */
#define FHK_OS_Windows     1
#define FHK_OS_POSIX       2
#ifdef FHK_TARGET_OS
#define FHK_OS             jointok_(FHK_OS_, FHK_TARGET_OS)
#endif

/* coroutine backend. */
#define FHK_CO_builtin     1
#define FHK_CO_libco       2
#define FHK_CO             jointok_(FHK_CO_, FHK_TARGET_CO)

/* architecture detection. */
#ifndef FHK_ARCH
#if defined(__x86_64__)
#define FHK_ARCH           FHK_ARCH_x86_64
#endif
#endif

/* os detection. */
#ifndef FHK_OS
#if defined(_WIN32) || defined(__cygwin__)
#define FHK_OS             FHK_OS_Windows
#else
#define FHK_OS             FHK_OS_POSIX
#endif
#endif

/* target features. */

#if FHK_OS == FHK_OS_Windows
#define FHK_WINDOWS        1
#endif

#if FHK_OS == FHK_OS_POSIX
#define FHK_MMAP           1
#define FHK_ASM_CORO       1
#endif
