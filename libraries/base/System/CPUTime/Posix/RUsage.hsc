{-# LANGUAGE CPP, CApiFFI #-}

#include "HsFFI.h"
#include "HsBaseConfig.h"

module System.CPUTime.Posix.RUsage
    ( getCPUTime
    , getCpuTimePrecision
    ) where

import Data.Ratio
import Foreign
import Foreign.C

-- For struct rusage
#if HAVE_SYS_RESOURCE_H
#include <sys/resource.h>
#endif

getCPUTime :: IO Integer
getCPUTime = allocaBytes (#const sizeof(struct rusage)) $ \ p_rusage -> do
    throwErrnoIfMinus1_ "getrusage" $ getrusage (#const RUSAGE_SELF) p_rusage

    let ru_utime = (#ptr struct rusage, ru_utime) p_rusage
    let ru_stime = (#ptr struct rusage, ru_stime) p_rusage
    u_sec  <- (#peek struct timeval,tv_sec)  ru_utime :: IO CTime
    u_usec <- (#peek struct timeval,tv_usec) ru_utime :: IO CSUSeconds
    s_sec  <- (#peek struct timeval,tv_sec)  ru_stime :: IO CTime
    s_usec <- (#peek struct timeval,tv_usec) ru_stime :: IO CSUSeconds
    return ((realToInteger u_sec * 1000000 + realToInteger u_usec +
             realToInteger s_sec * 1000000 + realToInteger s_usec)
                * 1000000)

type CRUsage = ()
foreign import capi unsafe "HsBase.h getrusage" getrusage :: CInt -> Ptr CRUsage -> IO CInt

getCpuTimePrecision :: IO Integer
getCpuTimePrecision =
    return $ round ((1000000000000::Integer) % fromIntegral clk_tck)

foreign import ccall unsafe clk_tck :: CLong

-- | CTime, CClock, CUShort etc are in Real but not Fractional,
-- so we must convert to Double before we can round it
realToInteger :: Real a => a -> Integer
realToInteger ct = round (realToFrac ct :: Double)
