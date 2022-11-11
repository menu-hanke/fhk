#-------------------------------------------------------------------------------#
# fhk makefile.                                                                 #
#-------------------------------------------------------------------------------#

# programs
CC             = $(CROSS)gcc
AR             = $(CROSS)gcc-ar
STRIP          = $(CROSS)strip
LUAJIT         = luajit
BCLOADER       = $(LUAJIT) bcloader
PKGCONFIG      = pkg-config

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
HOST_MINGW    ?= $(findstring MINGW64,$(shell uname -s))
else
HOST          ?= $(shell uname -s)
endif

# target settings
ifeq (Windows,$(TARGET))
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

#---- Compiler options ----------------------------------------------------------------------------

XCFLAGS     = $(CCOPT) $(CCDEF) $(CCDEBUG) $(CCWARN)
XLDFLAGS    =

ifneq (,$(TRACE))
CCDEF      += -DFHK_TRACE=$(TRACE)
endif

ifeq (y,$(SANITIZE))
XCFLAGS    += $(ASAN) $(UBSAN)
XLDFLAGS   += $(ASAN) $(UBSAN)
endif

ifneq (,$(CCDEBUG))
STRIP       = :
else
ifeq (Windows,$(TARGET))
STRIP      += --strip-unneeded
endif
endif

#---- Help ----------------------------------------------------------------------------

help:
	@echo "targets:"
	@echo "    lua          Lua shared library (fhk$(TARGET_SO))"
	@echo "    pyx          CPython extension  (fhk$(TARGET_PYEXT))"

#---- Host library common ----------------------------------------------------------------------------

CORE_O      = build.o debug.o solve.o sub.o swap_$(ARCH).o
LOADER_O    = loader.o
PYX_O       = fhk_api.pyx.o
ifeq (y,$(LINKLUA))
XLUACORE_O  = fhk_cdef.lua.o fhk_clib.lua.o fhk_ctypes.lua.o fhk_driver.lua.o fhk_trace.lua.o
XLUALANG_O  = fhk_lang_Expr.lua.o fhk_lang_Lua.lua.o fhk_lang_Python.lua.o
XLUALIB_O   = fhk_api.lua.o reflect.lua.o
XLUAPY_O    = fhk_pyx.lua.o
endif

LUAJIT_I    = $(shell $(PKGCONFIG) --cflags-only-I luajit)
LUAJIT_L    = $(shell $(PKGCONFIG) --libs luajit)

#---- Lua host library ----------------------------------------------------------------------------

fhk$(TARGET_SO): XCFLAGS += -fPIC
ifeq (Windows,$(TARGET))
fhk$(TARGET_SO): XLDFLAGS += $(LUAJIT_L)
endif
fhk$(TARGET_SO): $(CORE_O) $(XLUACORE_O) $(XLUALANG_O) $(XLUALIB_O) $(LOADER_O)
	$(CC) -shared $^ $(XLDFLAGS) $(LDFLAGS) -o $@
	$(STRIP) $@

.PHONY: lua
lua: fhk$(TARGET_SO)

#---- Python host library ----------------------------------------------------------------------------

PYTHON    = python
CYTHON    = $(PYTHON) -m cython
PYTHON_I  = -I$(shell $(PYTHON) -c 'import sysconfig; print(sysconfig.get_config_var("INCLUDEPY"))' 2>/dev/null)
ifeq (Windows,$(TARGET))
PYTHON_L  = $(shell $(PYTHON) -c 'import sysconfig; import os; print(os.path.join(sysconfig.get_config_var("BINDIR"), "python"+sysconfig.get_config_var("py_version_nodot")+".dll"))' 2>/dev/null)
endif # else: don't need to link libpython.

TARGET_PYEXT = $(shell $(PYTHON) -c 'import sysconfig; print(sysconfig.get_config_var("EXT_SUFFIX"))' 2>/dev/null)

fhk$(TARGET_PYEXT): XCFLAGS += -fPIC
fhk$(TARGET_PYEXT): $(CORE_O) $(XLUACORE_O) $(XLUALANG_O) $(XLUAPY_O) $(PYX_O)
	$(CC) -shared $^ $(XLDFLAGS) $(LUAJIT_L) $(PYTHON_L) $(LDFLAGS) -o $@
	$(STRIP) $@

.PHONY: pyx
pyx: fhk$(TARGET_PYEXT)

#---- Rules ----------------------------------------------------------------------------

%.a:
	$(AR) rcs $@ $^

%.o: %.c
	$(CC) $(XCFLAGS) $(CFLAGS) -c $< -o $@

%.o: %.S
	$(CC) $(XCFLAGS) $(CFLAGS) -c $< -o $@

%.lua.c: %.lua
	$(LUAJIT) -b -n $(subst _,.,$(notdir $*)) $< $@

%.lua: %.lua.h
	$(CC) $(CCDEF) $(LUAHDEF) -P -E -nostdinc $< 2>/dev/null >$@ || true

fhk_api.pyx.c: fhk_api.pyx
	$(CYTHON) -f --module-name fhk $< -o $@

asmdef.h: asmdef.lua fhk_cdef.lua
	$(LUAJIT) asmdef.lua > $@

loader.c:
	$(BCLOADER) -o $(TARGET) -n fhk -c fhk_api -L > $@

CCGITVER = $(shell GITVER=$$(git describe) && echo -DFHK_GITVER='\"'$$(echo $$GITVER | cut -c2- -)'\"')
fhk_cdef.lua: LUAHDEF = $(CCGITVER)
fhk_api.pyx.o: XCFLAGS += $(LUAJIT_I) $(PYTHON_I) $(CCGITVER)
ifeq (Windows,$(TARGET))
# https://github.com/cython/cython/issues/2670#issuecomment-432212671
fhk_api.pyx.o: XCFLAGS += -DMS_WIN64
endif

#---- Auxiliary ----------------------------------------------------------------------------

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
