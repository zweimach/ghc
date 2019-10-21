/* ----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 1998-2004
 *
 * Time values in the RTS
 *
 * To understand the structure of the RTS headers, see the wiki:
 *   https://gitlab.haskell.org/ghc/ghc/wikis/commentary/source-tree/includes
 *
 * --------------------------------------------------------------------------*/

#pragma once

#include <stdbool.h>

// For most time values in the RTS we use a fixed resolution of nanoseconds,
// normalising the time we get from platform-dependent APIs to this
// resolution.
#define TIME_RESOLUTION 1000000000
typedef struct {
  uint64_t time;
} Time;

#define TIME_MAX HS_INT64_MAX

#if TIME_RESOLUTION == 1000000000
// I'm being lazy, but it's awkward to define fully general versions of these
#define TimeToMS(t)      (((t).time) / 1000000)
#define TimeToUS(t)      (((t).time) / 1000)
#define TimeToNS(t)      ((t).time)
#define MSToTime(t)      ((Time){.time=(t * 1000000)})
#define USToTime(t)      ((Time){.time=(t * 1000)})
#define NSToTime(t)      ((Time){.time=(t)})
#else
#error Fix TimeToNS(), TimeToUS() etc.
#endif

#define SecondsToTime(t) ((Time){.time=(t) * TIME_RESOLUTION})
#define TimeToSeconds(t) ((t.time) / TIME_RESOLUTION)
#define TimeToSecondsDbl(t) ((double)(t.time) / TIME_RESOLUTION)

// Use instead of SecondsToTime() when we have a floating-point
// seconds value, to avoid truncating it.
INLINE_HEADER Time fsecondsToTime (double t)
{
    return (Time) { .time = t * TIME_RESOLUTION };
}

INLINE_HEADER Time addTime (Time t1, Time t2)
{
    return (Time) { .time = t1.time + t2.time };
}

INLINE_HEADER Time subTime (Time t1, Time t2)
{
    return (Time) { .time = t1.time - t2.time };
}

INLINE_HEADER int divTime (Time t1, Time t2)
{
    return t1.time / t2.time;
}

INLINE_HEADER Time minTime (Time t1, Time t2)
{
    return (t1.time < t2.time) ? t1 : t2;
}

INLINE_HEADER bool eqTime (Time t1, Time t2)
{
    return t1.time == t2.time;
}

INLINE_HEADER bool ltTime (Time t1, Time t2)
{
    return t1.time < t2.time;
}

Time getProcessElapsedTime (void);
