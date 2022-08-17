#pragma once

#include "conf.h"

#include <stdio.h>

/*
 * tracing.
 *
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

#define TRACE_build(f,...)        (0x1  | TRACE_##f(__VA_ARGS__))
#define TRACE_sub(f,...)          (0x2  | TRACE_##f(__VA_ARGS__))
#define TRACE_solver(f,...)       (0x4  | TRACE_##f(__VA_ARGS__))
#define FHK_TRACEON(flags)        TRACEON(FHK_TRACE, flags)

#define trace_fhk(tag, fmt, ...)   fprintf(stderr, ">fhk %-10s" fmt "\n", tag, ##__VA_ARGS__)

#if FHK_TRACEON(build)
#define TRACE_INTRPRED  "intern",   trace_fhk, "MERGE PRED   0x%-5x %s -> %s"
#define TRACE_INTRGRD   "intern",   trace_fhk, "MERGE GUARD  0x%-5x %s -> %s"
#define TRACE_LINKVAR   "link",     trace_fhk, "LINK VAR     0x%-5x %s"
#define TRACE_LINKMOD   "link",     trace_fhk, "LINK MODEL   0x%-5x %s"
#define TRACE_LINKPARAM "link",     trace_fhk, "LINK PARAM   0x%-5x %s -> %s"
#define TRACE_LINKRET   "link",     trace_fhk, "LINK RETURN  0x%-5x %s -> %s"
#define TRACE_LINKSKIP  "link",     trace_fhk, "SKIP         0x%-5x %s"
#define TRACE_LINKPRED  "link",     trace_fhk, "LINK PRED    0x%-5x %s"
#define TRACE_LINKCHECK "link",     trace_fhk, "LINK CHECK   0x%-5x %s -> %s [+%g]"
#define TRACE_BNDGIVEN  "analysis", trace_fhk, "GIVEN        %s"
#define TRACE_BNDLOMOD  "analysis", trace_fhk, "LOW  MODEL   %s: %g (%g)"
#define TRACE_BNDHIMOD  "analysis", trace_fhk, "HIGH MODEL   %s: %g (%g)"
#define TRACE_BNDLOVAR  "analysis", trace_fhk, "LOW  VAR     %s: %g"
#define TRACE_BNDHIVAR  "analysis", trace_fhk, "HIGH VAR     %s: %g"
#define TRACE_MARKVAR   "mark",     trace_fhk, "MARK VAR     %s: [%g, %g]"
#define TRACE_MARKMOD   "mark",     trace_fhk, "MARK MODEL   %s: [%g, %g]"
#define TRACE_LAYOCOMP  "layout",   trace_fhk, "LAYOUT COMPUTED  VAR    %04d.---- %s [0x%x]"
#define TRACE_LAYOGIVEN "layout",   trace_fhk, "LAYOUT GIVEN     VAR    %04d.%04d %s"
#define TRACE_LAYODVAR  "layout",   trace_fhk, "LAYOUT DERIVE    VAR    %04d.%04d %s"
#define TRACE_LAYOPGRD  "layout",   trace_fhk, "LAYOUT PREDICATE GUARD  %04d.---- %s [0x%x]"
#define TRACE_LAYOMOD   "layout",   trace_fhk, "LAYOUT COMPUTED  MODEL  %04d.%04d %s [0x%x]"
#define TRACE_LAYODMOD  "layout",   trace_fhk, "LAYOUT DERIVE    MODEL  %04d.%04d %s [0x%x]"
#endif

#if FHK_TRACEON(sub)
#define TRACE_SETROOTM  "sub",      trace_fhk, "<- SETROOT  %s :: %s:%d"
#define TRACE_SETROOTSS "sub",      trace_fhk, "<- SETROOT  %s :: 0x%lx"
#define TRACE_SETVALR   "sub",      trace_fhk, "<- SETVALUE %s --> %p :: %s"
#define TRACE_SETVALI   "sub",      trace_fhk, "<- SETVALUE %s:%ld..+%ld :: %s"
#define TRACE_SETVALD   "sub",      trace_fhk, "<- SETVALUE %s:%ld..+%ld"
#endif

#if FHK_TRACEON(solver)
#define TRACE_JERR      "solver",   trace_fhk, "-> 0000 ERR"
#define TRACE_JOK       "solver",   trace_fhk, "-> 0001 OK"
#define TRACE_JMP       "solver",   trace_fhk, "-> %04d JMP %s:%d"
#define TRACE_ENTERV    "solver",   trace_fhk, "%05ld ENTER COMPUTED  %s:%ld | beta: %g"
#define TRACE_ENTERC    "solver",   trace_fhk, "%05ld ENTER CANDIDATE %s:%ld | beta: %g, delta: %g"
#define TRACE_ENTERD    "solver",   trace_fhk, "%05ld ENTER DERIVE    %s:%ld | beta: %g"
#define TRACE_PENALTY   "solver",   trace_fhk, "%05ld +++++ CHECK %03d %s:%ld -> %s~%s [+%g] [%g/%g]"
#define TRACE_PARAM     "solver",   trace_fhk, "%05ld +++++ PARAM %03d %s:%ld -> %s~%s [+%g] [%g/%g]"
#define TRACE_TAILP     "solver",   trace_fhk, "%05ld +++++ TAILP %03d %s:%ld -> %s~%s [+%g] [%g/%g]"
#define TRACE_CHAINM    "solver",   trace_fhk, "%05ld CHAIN MODEL     %s:%ld | cost: %g, inv: %g"
#define TRACE_CHAINV    "solver",   trace_fhk, "%05ld CHAIN VAR       %s:%ld [%s:%ld] | cost: %g, inv: %g"
#define TRACE_CHAINC    "solver",   trace_fhk, "%05ld CHAIN VAR       %s:%ld [%s:%ld] | cost: %g"
#define TRACE_BOUND     "solver",   trace_fhk, "%05ld BOUND MODEL     %s:%ld | cost: %g, beta: %g, delta: %g"
#define TRACE_BOUNDV    "solver",   trace_fhk, "%05ld BOUND VAR       %s:%ld | cost: %g"
#define TRACE_TOLER     "solver",   trace_fhk, "%05ld TOLERANCE       %s:%ld (+0x%x / %g)"
#define TRACE_EVALV     "eval",     trace_fhk, "%05ld EVAL COMPUTED   %s:%ld"
#define TRACE_EVALM     "eval",     trace_fhk, "%05ld EVAL MODEL      %s:%ld"
#endif
