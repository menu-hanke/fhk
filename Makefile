#-------------------------------------------------------------------------------#
# fhk makefile.                                                                 #
#-------------------------------------------------------------------------------#

# programs
CC             = $(CROSS)gcc
AR             = $(CROSS)gcc-ar
LUAJIT         = luajit
BCLOADER       = $(LUAJIT) bcloader
PYTHON         = python
CYTHON         = cython
PKGCONFIG      = pkg-config
PYCONFIG       = python3-config

# libraries
LUAJIT_I       = $(shell $(PKGCONFIG) --cflags-only-I luajit)
PYTHON_I       = $(shell $(PYCONFIG) --includes)
LUAJIT_L      ?= $(shell $(PKGCONFIG) --libs luajit)

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
TARGET_PYEXT   = $(shell $(PYCONFIG) --extension-suffix 2>/dev/null)

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

ifneq (,$(TRACE))
CCDEF      += -DFHK_TRACE=$(TRACE)
endif

ifeq (y,$(SANITIZE))
XCFLAGS    += $(ASAN) $(UBSAN)
XLDFLAGS   += $(ASAN) $(UBSAN)
endif

# objects
CORE_O      = build.o debug.o solve.o sub.o swap_$(ARCH).o
LOADER_O    = loader.o
PYX_O       = fhk_api.pyx.o
ifeq (y,$(LINKLUA))
XLUACORE_O  = fhk_cdef.lua.o fhk_clib.lua.o fhk_ctypes.lua.o fhk_driver.lua.o
XLUALANG_O  = fhk_lang_Expr.lua.o fhk_lang_Lua.lua.o fhk_lang_Python.lua.o
XLUALIB_O   = fhk_api.lua.o reflect.lua.o
XLUAPY_O    = fhk_pyx.lua.o
endif

#--------------------------------------------------------------------------------

help:
	@echo "targets:"
	@echo "    lua          Lua shared library (fhk$(TARGET_SO))"
	@echo "    pyx          CPython extension  (fhk$(TARGET_PYEXT))"

.PHONY: lua pyx
lua: fhk$(TARGET_SO)
pyx: fhk$(TARGET_PYEXT)

# Lua dynamic library
fhk$(TARGET_SO): XCFLAGS += -fPIC
fhk$(TARGET_SO): $(CORE_O) $(XLUACORE_O) $(XLUALANG_O) $(XLUALIB_O) $(LOADER_O)
	$(CC) -shared $^ $(XLDFLAGS) $(LDFLAGS) -o $@

# Python dynamic library
fhk$(TARGET_PYEXT): XCFLAGS += -fPIC
fhk$(TARGET_PYEXT): $(CORE_O) $(XLUACORE_O) $(XLUALANG_O) $(XLUAPY_O) $(PYX_O)
	$(CC) -shared $^ $(XLDFLAGS) $(LUAJIT_L) $(LDFLAGS) -o $@

#--------------------------------------------------------------------------------

%.a:
	$(AR) rcs $@ $^

%.o: %.c
	$(CC) $(XCFLAGS) $(CFLAGS) -c $< -o $@

%.o: %.S
	$(CC) $(XCFLAGS) $(CFLAGS) -c $< -o $@

%.lua.o: %.lua
	$(LUAJIT) -b -n $(subst _,.,$(notdir $*)) $< $@

%.lua: %.lua.h
	$(CC) $(CCDEF) $(LUAHDEF) -P -E -nostdinc $< 2>/dev/null >$@ || true

fhk_api.pyx.c: fhk_api.pyx
	$(CYTHON) -f --module-name fhk $< -o $@

asmdef.h: asmdef.lua fhk_cdef.lua
	$(LUAJIT) asmdef.lua > $@

loader.c:
	$(BCLOADER) -o $(TARGET) -n fhk -c fhk_api -L > $@

CCGITHASH = $(shell HASH=$$(git rev-parse --short HEAD) && echo -DFHK_GITHASH='\"'$$HASH'\"')
fhk_cdef.lua: LUAHDEF = -DFHK_CORO=$(CORO) $(CCGITHASH)
fhk_api.pyx.o: XCFLAGS += $(LUAJIT_I) $(PYTHON_I) $(CCGITHASH)

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
