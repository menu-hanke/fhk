#-------------------------------------------------------------------------------#
# fhk makefile.                                                                 #
#                                                                               #
# useful variables you may set when invoking `make`:                            #
#     CROSS           cross-compiler toolchain prefix.                          #
#     DEBUG           set to `y` to enable debugging.                           #
#                                                                               #
# useful cflags:                                                                #
#     -DFHK_TRACE=    trace flags (see trace.h)                                 #
#-------------------------------------------------------------------------------#

# programs
CC             = $(CROSS)gcc
AR             = $(CROSS)gcc-ar
LUAJIT         = luajit
BCLOADER       = $(LUAJIT) bcloader
PYTHON         = python
CYTHON         = cython
PKGCONFIG      = pkg-config

# include paths
LUAJIT_I       = $(shell $(PKGCONFIG) --cflags-only-I luajit)
PYTHON_I       = -I$(shell $(PYTHON) -c 'import sysconfig; print(sysconfig.get_path("include"))')

# embed lua bytecode? [y]/n
LINKLUA       ?= y

# enable debugging? y/[n]
DEBUG         ?= n

# debugging
ASAN          ?= -fsanitize=address
UBSAN         ?= -fsanitize=undefined -fno-sanitize=shift,signed-integer-overflow

# coroutine implementation (builtin/libco). automatically chosen if left empty.
CORO          ?=

# link time optimization? (TODO: this can and should be replaced with amalg)
CCLTO         ?= -flto

# asan/ubsan?
SANITIZE      ?=

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

# linker options
LJ_LDFLAGS    ?= -lm
BCL_LDFLAGS   ?= $(shell $(BCLOADER) -f)

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

# disable default rules. all my homies hate default rules.
.SUFFIXES:

#--------------------------------------------------------------------------------

# objects
CORE_O      = arena.o build.o cmd.o debug.o mut.o prune.o solve.o state.o
EMBED_O     = jtab.o
PYX_O       = _ctypes.pyx.o
ifeq (y,$(LINKLUA))
LUACORE_O   = fhk_cdef.lua.o fhk_clib.lua.o fhk_ctypes.lua.o fhk_driver.lua.o fhk_g.lua.o \
			  fhk_lib.lua.o fhk_rules.lua.o
LUALIB_O    = fhk_api.lua.o ffi-reflect/reflect.lua.o
LUAPY_O     = fhk_py.lua.o
BCLOADER_O  = loader.o
endif

#--------------------------------------------------------------------------------

ifeq (,$(CORO))
ARCHTEST = $(shell $(CC) $(CCDEF) -E -dM target.h 2>/dev/null)
ifeq (,$(findstring FHK_ASM_CORO,$(ARCHTEST)))
CORO := libco
else
CORO := builtin
endif
endif

ifeq (builtin,$(CORO))
CORE_O += co_asm.o co_builtin.o
CCDEF += -DFHK_CO=builtin
endif

ifeq (libco,$(CORO))
CORE_O += co_libco.o
CCDEF += -DFHK_CO=libco
endif

# build version
CCGITHASH   = $(shell HASH=$$(git rev-parse --short HEAD) && echo -DFHK_GITHASH=$$HASH)

# final flags
CFLAGS      = $(CCOPT) $(CCDEF) $(FHK_CCDEF) $(CCDEBUG) $(CCWARN) $(CCINCLUDE) $(CCLTO) $(XCFLAGS)

#--------------------------------------------------------------------------------

help:
	@echo "targets:"
	@echo "    libfhklua.a - Lua static library"
	@echo "    fhk$(TARGET_SO) - C+Lua shared library"
	@echo "    libfhkpy.a - Python static library"

libfhklua.a: $(CORE_O) $(EMBED_O) $(LUACORE_O) $(LUALIB_O)
libfhkpy.a:  $(CORE_O) $(EMBED_O) $(PYX_O) $(LUACORE_O) $(LUAPY_O) $(BCLOADER_O)

%.a:
	$(AR) rcs $@ $^

fhk$(TARGET_SO): CFLAGS += -fPIC
fhk$(TARGET_SO): $(CORE_O) $(EMBED_O) $(LUACORE_O) $(LUALIB_O) $(BCLOADER_O)
	$(CC) -shared $^ $(BCL_LDFLAGS) -o $@

#--------------------------------------------------------------------------------

%.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@

%.o: %.S
	$(CC) $(CFLAGS) -c $< -o $@

%.lua.o: %.lua
	$(LUAJIT) -b -n $(subst _,.,$(notdir $*)) $< $@

%.lua: %.lua.h
	$(CC) $(CCDEF) $(LUAHDEF) -P -E -nostdinc $< 2>/dev/null >$@ || true

%.pyx.c: %.pyx
	$(CYTHON) $< -o $@

loader.c:
	$(BCLOADER) -o $(TARGET) -n fhk -c fhk_api -L > $@
loader.o: CFLAGS += $(LUAJIT_I)

fhk_cdef.lua: LUAHDEF = -DFHK_CORO=$(CORO) $(CCGITHASH)
_ctypes.pyx.o: CCINCLUDE += $(LUAJIT_I) $(PYTHON_I)

#--------------------------------------------------------------------------------

.PHONY: clean
clean:
	$(RM) *.o *.a *.so *.pyx.c *.pyx.h loader.c fhk_cdef.lua

.PHONY: dep
dep:
	$(MAKE) clean
	$(CC) $(CCDEF) -MM *.c | sed -r 's|^.*\.o: (.*-)\.c|\1.o: \1.c|' > Makefile.dep
	$(CC) $(CCDEF) -MM *.lua.h | sed -r 's|^.*\.o: (.*-\.lua)\.h|\1: \1.h|' >> Makefile.dep

#--------------------------------------------------------------------------------

-include Makefile.dep
