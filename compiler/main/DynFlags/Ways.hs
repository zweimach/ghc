module DynFlags.Ways where

import Platform
import DynFlags.GeneralFlags

import Data.List (intersperse)

-- The central concept of a "way" is that all objects in a given
-- program must be compiled in the same "way".  Certain options change
-- parameters of the virtual machine, eg. profiling adds an extra word
-- to the object header, so profiling objects cannot be linked with
-- non-profiling objects.

-- After parsing the command-line options, we determine which "way" we
-- are building - this might be a combination way, eg. profiling+threaded.

-- We then find the "build-tag" associated with this way, and this
-- becomes the suffix used to find .hi files and libraries used in
-- this compilation.

data Way
  = WayCustom String -- for GHC API clients building custom variants
  | WayThreaded
  | WayDebug
  | WayProf
  | WayEventLog
  | WayDyn
  deriving (Eq, Ord, Show)

allowed_combination :: [Way] -> Bool
allowed_combination way = and [ x `allowedWith` y
                              | x <- way, y <- way, x < y ]
  where
        -- Note ordering in these tests: the left argument is
        -- <= the right argument, according to the Ord instance
        -- on Way above.

        -- dyn is allowed with everything
        _ `allowedWith` WayDyn                  = True
        WayDyn `allowedWith` _                  = True

        -- debug is allowed with everything
        _ `allowedWith` WayDebug                = True
        WayDebug `allowedWith` _                = True

        (WayCustom {}) `allowedWith` _          = True
        WayThreaded `allowedWith` WayProf       = True
        WayThreaded `allowedWith` WayEventLog   = True
        WayProf     `allowedWith` WayEventLog   = True
        _ `allowedWith` _                       = False

mkBuildTag :: [Way] -> String
mkBuildTag ways = concat (intersperse "_" (map wayTag ways))

wayTag :: Way -> String
wayTag (WayCustom xs) = xs
wayTag WayThreaded = "thr"
wayTag WayDebug    = "debug"
wayTag WayDyn      = "dyn"
wayTag WayProf     = "p"
wayTag WayEventLog = "l"

wayRTSOnly :: Way -> Bool
wayRTSOnly (WayCustom {}) = False
wayRTSOnly WayThreaded = True
wayRTSOnly WayDebug    = True
wayRTSOnly WayDyn      = False
wayRTSOnly WayProf     = False
wayRTSOnly WayEventLog = True

wayDesc :: Way -> String
wayDesc (WayCustom xs) = xs
wayDesc WayThreaded = "Threaded"
wayDesc WayDebug    = "Debug"
wayDesc WayDyn      = "Dynamic"
wayDesc WayProf     = "Profiling"
wayDesc WayEventLog = "RTS Event Logging"

-- Turn these flags on when enabling this way
wayGeneralFlags :: Platform -> Way -> [GeneralFlag]
wayGeneralFlags _ (WayCustom {}) = []
wayGeneralFlags _ WayThreaded = []
wayGeneralFlags _ WayDebug    = []
wayGeneralFlags _ WayDyn      = [Opt_PIC]
    -- We could get away without adding -fPIC when compiling the
    -- modules of a program that is to be linked with -dynamic; the
    -- program itself does not need to be position-independent, only
    -- the libraries need to be.  HOWEVER, GHCi links objects into a
    -- .so before loading the .so using the system linker.  Since only
    -- PIC objects can be linked into a .so, we have to compile even
    -- modules of the main program with -fPIC when using -dynamic.
wayGeneralFlags _ WayProf     = [Opt_SccProfilingOn]
wayGeneralFlags _ WayEventLog = []

-- Turn these flags off when enabling this way
wayUnsetGeneralFlags :: Platform -> Way -> [GeneralFlag]
wayUnsetGeneralFlags _ (WayCustom {}) = []
wayUnsetGeneralFlags _ WayThreaded = []
wayUnsetGeneralFlags _ WayDebug    = []
wayUnsetGeneralFlags _ WayDyn      = [-- There's no point splitting objects
                                      -- when we're going to be dynamically
                                      -- linking. Plus it breaks compilation
                                      -- on OSX x86.
                                      Opt_SplitObjs,
                                      -- If splitobjs wasn't useful for this,
                                      -- assume sections aren't either.
                                      Opt_SplitSections]
wayUnsetGeneralFlags _ WayProf     = []
wayUnsetGeneralFlags _ WayEventLog = []

wayOptc :: Platform -> Way -> [String]
wayOptc _ (WayCustom {}) = []
wayOptc platform WayThreaded = case platformOS platform of
                               OSOpenBSD -> ["-pthread"]
                               OSNetBSD  -> ["-pthread"]
                               _         -> []
wayOptc _ WayDebug      = []
wayOptc _ WayDyn        = []
wayOptc _ WayProf       = ["-DPROFILING"]
wayOptc _ WayEventLog   = ["-DTRACING"]

wayOptl :: Platform -> Way -> [String]
wayOptl _ (WayCustom {}) = []
wayOptl platform WayThreaded =
        case platformOS platform of
        -- FreeBSD's default threading library is the KSE-based M:N libpthread,
        -- which GHC has some problems with.  It's currently not clear whether
        -- the problems are our fault or theirs, but it seems that using the
        -- alternative 1:1 threading library libthr works around it:
        OSFreeBSD  -> ["-lthr"]
        OSOpenBSD  -> ["-pthread"]
        OSNetBSD   -> ["-pthread"]
        _          -> []
wayOptl _ WayDebug      = []
wayOptl _ WayDyn        = []
wayOptl _ WayProf       = []
wayOptl _ WayEventLog   = []

wayOptP :: Platform -> Way -> [String]
wayOptP _ (WayCustom {}) = []
wayOptP _ WayThreaded = []
wayOptP _ WayDebug    = []
wayOptP _ WayDyn      = []
wayOptP _ WayProf     = ["-DPROFILING"]
wayOptP _ WayEventLog = ["-DTRACING"]
