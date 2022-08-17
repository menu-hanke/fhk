#-------------------------------------------------------------------------------#
# fhk makefile.                                                                 #
#                                                                               #
# useful variables you may set when invoking `make`:                            #
#     TRACE           set to `all` to enable all trace messages.                #
#                     (see trace.h for more granular control.)                  #
#     DEBUG           set to `y` to enable debugging.                           #
#     CROSS           cross-compiler toolchain prefix.                          #
#-------------------------------------------------------------------------------#

# programs
CC             = $(CROSS)gcc
AR             = $(CROSS)gcc-ar
LUAJIT         = luajit
BCLOADER       = $(LUAJIT) bcloader
PYTHON         = python
CYTHON         = cython

# embed lua bytecode? [y]/n
LINKLUA       ?= y

# enable debugging? y/[n]
DEBUG         ?= n

# build with sanitizers? y/[n]
SANITIZE      ?= n
ASAN          ?= -fsanitize=address
UBSAN         ?= -fsanitize=undefined -fno-sanitize=shift,signed-integer-overflow

# enable tracing? (see trace.h. set to `all` to enable all trace messages).
TRACE         ?=

# compiler options
CCWARN        ?= -Wall -Wextra -Wno-maybe-uninitialized
ifeq (y,$(DEBUG))
CCOPT         ?= -O0
CCDEBUG       ?= -g3
CCDEF         ?=
else
CCOPT         ?= -O2 -ffast-math
CCDEBUG       ?=
CCDEF         ?= -DNDEBUG
endif

# cross-compilation
TARGET        ?= $(HOST)
CROSS         ?=

# host settings
ifneq (,$(findstring Windows,$(OS)))
HOST          ?= Windows
HOST_CYGWIN   ?= $(findstring CYGWIN,$(shell uname -s))
else
HOST          ?= $(shell uname -s)
endif

# target settings
ifeq (Windows,$(TARGET))
TARGET_EXE     = .exe
TARGET_SO      = .dll
else
TARGET_SO      = .so
endif

# arch settings
ARCHTEST = $(shell $(CC) $(CCDEF) -E -dM target.h 2>/dev/null)
ifneq (,$(findstring FHK_x64,$(ARCHTEST)))
ARCH           = x64
endif

# disable default rules. all my homies hate default rules.
.SUFFIXES:

#--------------------------------------------------------------------------------

XCFLAGS     = $(CCOPT) $(CCDEF) $(CCDEBUG) $(CCWARN)
XLDFLAGS    =
FHKCFLAGS   = $(XCFLAGS) $(CFLAGS)
FHKLDFLAGS  = $(XLDFLAGS) $(LDFLAGS)

ifneq (,$(TRACE))
XCFLAGS    += -DFHK_TRACE=$(TRACE)
endif

ifeq (y,$(SANITIZE))
XCFLAGS    += $(ASAN) $(UBSAN)
XLDFLAGS   += $(ASAN) $(UBSAN)
endif

# objects
CORE_O      = build.o debug.o solve.o sub.o swap_$(ARCH).o
LOADER_O    = loader.o
PYX_O       = _ctypes.pyx.o
ifeq (y,$(LINKLUA))
XLUACORE_O  = fhk_cdef.lua.o fhk_clib.lua.o fhk_ctypes.lua.o fhk_driver.lua.o
XLUALANG_O  = fhk_lang_Expr.lua.o fhk_lang_Lua.lua.o
XLUALIB_O   = fhk_api.lua.o reflect.lua.o
XLUAPY_O    = fhk_pyx.lua.o
endif

#--------------------------------------------------------------------------------

help:
	@echo "targets:"
	@echo "    fhk$(TARGET_SO) - Lua dynamic library"
	@echo "    libfhk.a - Lua static library"
	@echo "    libfhkpy.a - Python static library"

# fhk.so - Lua dynamic library
fhk$(TARGET_SO): FHKCFLAGS += -fPIC
fhk$(TARGET_SO): FHKLDFLAGS += $(shell $(BCLOADER) -f)
fhk$(TARGET_SO): $(CORE_O) $(XLUACORE_O) $(XLUALANG_O) $(XLUALIB_O) $(LOADER_O)
	$(CC) -shared $^ $(FHKLDFLAGS) -o $@

# libfhk.a - Lua static library
libfhk.a: $(CORE_O) $(XLUACORE_O) $(XLUALANG_O) $(XLUALIB_O)

# libfhkpy.a - Python static library
libfhky.a: $(CORE_O) $(XLUACORE_O) $(XLUALANG_O) $(XLUAPY_O) $(PYX_O)

#--------------------------------------------------------------------------------

%.a:
	$(AR) rcs $@ $^

%.o: %.c
	$(CC) $(FHKCFLAGS) -c $< -o $@

%.o: %.S
	$(CC) $(FHKCFLAGS) -c $< -o $@

%.lua.o: %.lua
	$(LUAJIT) -b -n $(subst _,.,$(notdir $*)) $< $@

%.lua: %.lua.h
	$(CC) $(CCDEF) $(LUAHDEF) -P -E -nostdinc $< 2>/dev/null >$@ || true

%.pyx.c: %.pyx
	$(CYTHON) $< -o $@

asmdef.h: asmdef.lua fhk_cdef.lua
	$(LUAJIT) asmdef.lua > $@

loader.c:
	$(BCLOADER) -o $(TARGET) -n fhk -c fhk_api -L > $@

CCGITHASH = $(shell HASH=$$(git rev-parse --short HEAD) && echo -DFHK_GITHASH=$$HASH)
fhk_cdef.lua: LUAHDEF = -DFHK_CORO=$(CORO) $(CCGITHASH)

#--------------------------------------------------------------------------------

.PHONY: clean
clean:
	$(RM) *.o *.a *.so *.pyx.c *.pyx.h loader.c fhk_cdef.lua

.PHONY: dep
dep:
	$(MAKE) clean
	$(CC) $(CCDEF) -MM *.c *.S > Makefile.dep
	$(CC) $(CCDEF) -MM -MT fhk_cdef.lua fhk_cdef.lua.h >> Makefile.dep

#--------------------------------------------------------------------------------

-include Makefile.dep
