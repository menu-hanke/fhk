#pragma once

#include "conf.h"

#include <stdio.h>

/* tracing.
 * usage:
 *     #define TRACE_flag1(f,...) (0x1 | TRACE_##f(__VA_ARGS__))
 *     #define TRACE_flag2(f,...) (0x2 | TRACE_##f(__VA_ARGS__))
 *     ...
 * then get the flags with:
 *     TRACE(myflags)
 * then define trace messages:
 *     #if TRACEON(someflags)
 *     #define TRACE_XXX "tag", trace_func, "fmt"
 */

#define TRACE_()                  0
#define TRACE_all(...)            (~0)
#define TRACE__(f,...)            TRACE_##f(__VA_ARGS__)
#define TRACE(...)                TRACE__(__VA_ARGS__)
#define TRACEON(a,b)              (TRACE(a) & TRACE(b))

#define trace_off(...)            do {} while(0)
#define trace_tag(a,...)          a
#define trace_func(a,b,...)       b
#define trace_msg(a,b,c,...)      c
#define trace_(x,...)             trace_func(x, trace_off) (trace_tag(x), trace_msg(x,~,~), ##__VA_ARGS__)
#define trace(msg,...)            trace_(TRACE_##msg, ##__VA_ARGS__)

#define TRACE_solver(f,...)       (0x1  | TRACE_##f(__VA_ARGS__))
#define TRACE_cmd(f,...)          (0x2  | TRACE_##f(__VA_ARGS__))
#define TRACE_layout(f,...)       (0x4  | TRACE_##f(__VA_ARGS__))
#define TRACE_build(f,...)        (0x8  | TRACE_##f(__VA_ARGS__))
#define TRACE_prune(f,...)        (0x10 | TRACE_##f(__VA_ARGS__))
#define FHK_TRACEON(flags)        TRACEON(FHK_TRACE, flags)

#define trace_fhk(tag, fmt, ...)   fprintf(stderr, ">fhk %-10s" fmt "\n", tag, ##__VA_ARGS__)

#if FHK_TRACEON(solver)

#define TRACE_YSHAPE   "solver", trace_fhk, "-> SHAPE        %ld"
#define TRACE_YVAR     "solver", trace_fhk, "-> VREF         %s:%ld"
#define TRACE_YMAPK    "solver", trace_fhk, "-> MAPCALLK     %ld (%ld)"
#define TRACE_YMAPI    "solver", trace_fhk, "-> MAPCALLI     %ld:%ld"
#define TRACE_YMOD     "solver", trace_fhk, "-> MODCALL      %s:%d (%u -> %u)"
#define TRACE_YOK      "solver", trace_fhk, "-> OK"

#define TRACE_ENTERV   "solver", trace_fhk, "(%3ld) ENTER     %s:%ld: beta: %g"
#define TRACE_ENTERM   "solver", trace_fhk, "(%3ld) ENTER/m   %s:%d [%s:%d]: min: %g (%g)   beta: %g (%g)"
#define TRACE_BOUND    "solver", trace_fhk, "(%3ld) BOUND     %s:%d [%s:%d]: inverse: (%g) > (%g)"
#define TRACE_CHOSEN   "solver", trace_fhk, "(%3ld) CHOOSE    %s:%d [%s:%d]: cost: %g / %g   <#%u>"
#define TRACE_FAILED   "solver", trace_fhk, "(%3ld) FAIL      %s:%d: cost: %g > %g"
#define TRACE_PENALTY  "solver", trace_fhk, "(%3ld) ++++      %s:%d [%s:%d]: penalty  %s~%x [+%g] [%g/%g]"
#define TRACE_PARAM    "solver", trace_fhk, "(%3ld) ++++      %s:%d [%s:%d]: param    %s~%x [+%g] [%g/%g]"
#define TRACE_PARAMB   "solver", trace_fhk, "(%3ld) ++++ (!)  %s:%d [%s:%d]: param    %s~%x > %g"
#define TRACE_CHAIN    "solver", trace_fhk, "(%3ld) CHAIN     %s:%d [%s:%d]: inverse: %g / %g"

#endif


#if FHK_TRACEON(cmd)

#define TRACE_SETMAPK  "cmd",    trace_fhk, "<- SETMAPK      %ld :: 0x%lx"
#define TRACE_SETMAPI  "cmd",    trace_fhk, "<- SETMAPI      [%d]:%d :: 0x%lx"
#define TRACE_SETROOT  "cmd",    trace_fhk, "<- SETROOT      (0x%x) %d:%d..+%d"
#define TRACE_SETROOTP "cmd",    trace_fhk, "<- SETROOT      (0x%x) %d:%d..+%d  -->  %p"
#define TRACE_SETVALD  "cmd",    trace_fhk, "<- SETVALUE     (direct) %s  -->  %p :: %s"
#define TRACE_SETVALI  "cmd",    trace_fhk, "<- SETVALUE     %s:%d..+%d :: %s"

#endif


#if FHK_TRACEON(layout)

#define TRACE_LINKEDGE "layout", trace_fhk, "LINK  EDGE   %s  <->  %s"
#define TRACE_LINKCHK  "layout", trace_fhk, "LINK  CHECK  %s"
#define TRACE_LINKVAR  "layout", trace_fhk, "LINK  VAR    %s"
#define TRACE_LIMKMOD  "layout", trace_fhk, "LINK  MODEL  %s"
#define TRACE_LINKGRD  "layout", trace_fhk, "LINK  GUARD  %s"
#define TRACE_LINKMRG  "layout", trace_fhk, "MERGE GUARD  %s  ->  %s"
#define TRACE_LINKSKIP "layout", trace_fhk, "SKIP         %s"

#define TRACE_OGIVEN   "layout", trace_fhk, "ORDER VAR/g  [%3d] %s"
#define TRACE_OVAR     "layout", trace_fhk, "ORDER VAR/c  [%3d] %s"
#define TRACE_OMODEL   "layout", trace_fhk, "ORDER MODEL  [%3d] %s"
#define TRACE_OGUARD   "layout", trace_fhk, "ORDER GUARD  [%3d] %s"
#define TRACE_OSKIPMAP "layout", trace_fhk, "SKIP  MAP/%c  [%3d] ---"
#define TRACE_OMAP     "layout", trace_fhk, "ORDER MAP/%c  [%3d] %3d"

#endif


#if FHK_TRACEON(prune)

#define TRACE_PGIVEN   "prune",  trace_fhk, "GIVEN        %s"
#define TRACE_PLMOD    "prune",  trace_fhk, "LOW  MODEL   %s: %g (%g)"
#define TRACE_PHMOD    "prune",  trace_fhk, "HIGH MODEL   %s: %g (%g)"
#define TRACE_PLVAR    "prune",  trace_fhk, "LOW  VAR     %s: %g"
#define TRACE_PHVAR    "prune",  trace_fhk, "HIGH VAR     %s: %g"
#define TRACE_PMMOD    "prune",  trace_fhk, "MARK MODEL   %s: [%g, %g]"
#define TRACE_PMVAR    "prune",  trace_fhk, "MARK VAR     %s: [%g, %g]"
#define TRACE_PMGUARD  "prune",  trace_fhk, "MARK GUARD   %s"
#define TRACE_PMRET    "prune",  trace_fhk, "MARK RET     %s"
#define TRACE_PSWEEP   "prune",  trace_fhk, "SWEEP        %s"

#endif
