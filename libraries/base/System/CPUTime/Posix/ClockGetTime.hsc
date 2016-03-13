{-# LANGUAGE CPP, CApiFFI, NumDecimals #-}

#include "HsFFI.h"
#include "HsBaseConfig.h"

module System.CPUTime.Posix.ClockGetTime
    ( getCPUTime
    , getCpuTimePrecision
    ) where

import Foreign
import Foreign.C

#if HAVE_TIME_H
#include <time.h>
#endif

getCPUTime :: IO Integer
getCPUTime = fmap snd $ withTimespec $ \ts ->
    throwErrnoIfMinus1_ "clock_gettime"
    $ clock_gettime (#const CLOCK_PROCESS_CPUTIME_ID) ts

getCpuTimePrecision :: IO Integer
getCpuTimePrecision = fmap snd $ withTimespec $ \ts ->
    throwErrnoIfMinus1_ "clock_getres"
    $ clock_getres (#const CLOCK_PROCESS_CPUTIME_ID) ts

data Timespec

-- | Perform the given action to fill in a @struct timespec@, returning the
-- result of the action and the value of the @timespec@ in picoseconds.
withTimespec :: (Ptr Timespec -> IO a) -> IO (a, Integer)
withTimespec action =
    allocaBytes (# const sizeof(struct timespec)) $ \p_ts -> do
        r <- action p_ts
        u_sec  <- (#peek struct timespec,tv_sec)  p_ts :: IO CTime
        u_nsec <- (#peek struct timespec,tv_nsec) p_ts :: IO CLong
        return (r, realToInteger u_sec * 1e12 + realToInteger u_nsec * 1e3)

foreign import capi unsafe "time.h clock_getres"  clock_getres  :: CInt -> Ptr Timespec -> IO CInt
foreign import capi unsafe "time.h clock_gettime" clock_gettime :: CInt -> Ptr Timespec -> IO CInt

-- | CTime, CClock, CUShort etc are in Real but not Fractional,
-- so we must convert to Double before we can round it
realToInteger :: Real a => a -> Integer
realToInteger ct = round (realToFrac ct :: Double)
