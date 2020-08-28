{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UnliftedFFITypes #-}

{-|
Module      :  GHC.Exts.Heap
Copyright   :  (c) 2012 Joachim Breitner
License     :  BSD3
Maintainer  :  Joachim Breitner <mail@joachim-breitner.de>

With this module, you can investigate the heap representation of Haskell
values, i.e. to investigate sharing and lazy evaluation.
-}

module GHC.Exts.Heap (
    -- * Closure types
      Closure
    , LiftedClosure
    , GenClosure(..)
    , ClosureType(..)
    , PrimType(..)
    , WhatNext(..)
    , WhyBlocked(..)
    , TsoFlags(..)
    , HasHeapRep(getClosureDataX)
    , getClosureData

    -- * Info Table types
    , StgInfoTable(..)
    , EntryFunPtr
    , HalfWord
    , ItblCodes
    , itblSize
    , peekItbl
    , pokeItbl

    -- * Cost Centre (profiling) types
    , StgTSOProfInfo(..)
    , IndexTable(..)
    , CostCentre(..)
    , CostCentreStack(..)

     -- * Closure inspection
    , getBoxedClosureData
    , allClosures

    -- * Boxes
    , Box(..)
    , asBox
    , areBoxesEqual
    ) where

import Prelude
import GHC.Exts.Heap.Closures
import GHC.Exts.Heap.ClosureTypes
import GHC.Exts.Heap.Constants
import GHC.Exts.Heap.ProfInfo.Types
#if defined(PROFILING)
import GHC.Exts.Heap.ProfInfo.PeekProfInfo_ProfilingEnabled
import GHC.Exts.Heap.InfoTableProf
#else
-- This import makes PeekProfInfo_ProfilingEnabled available in make-based
-- builds. See #15197 for details (even though the related patch didn't
-- seem to fix the issue).
-- GHC.Exts.Heap.Closures uses the same trick to include
-- GHC.Exts.Heap.InfoTableProf into make-based builds.
import GHC.Exts.Heap.ProfInfo.PeekProfInfo_ProfilingEnabled ()

import GHC.Exts.Heap.ProfInfo.PeekProfInfo_ProfilingDisabled
import GHC.Exts.Heap.InfoTable
#endif
import GHC.Exts.Heap.Utils
import qualified GHC.Exts.Heap.FFIClosures as FFIClosures

import Control.Monad
import Data.Bits
import GHC.Arr
import GHC.Exts
import GHC.Int
import GHC.Word

import Foreign

#include "ghcconfig.h"

-- | Some closures (e.g.TSOs) don't have corresponding types to represent them in Haskell.
-- So when we have a pointer to such closure that we want to inspect, we `unsafeCoerce` it
-- into the following `LiftedClosure` lifted type (could be any lifted type) so that the
-- appropriate `instance HasHeapRep (a :: TYPE 'LiftedRep)` is used to decode the closure.
data LiftedClosure

class HasHeapRep (a :: TYPE rep) where

    -- | Decode a closure to it's heap representation ('GenClosure').
    -- Inside a GHC context 'b' is usually a 'GHC.Exts.Heap.Closures.Box'
    -- containing a thunk or an evaluated heap object. Outside it can be a
    -- 'Word' for "raw" usage of pointers.

    getClosureDataX ::
        (forall c . c -> IO (Ptr StgInfoTable, [Word], [b]))
        -- ^ Helper function to get info table, memory and pointers of the
        -- closure. The order of @[b]@ is significant and determined by
        -- @collect_pointers()@ in @rts/Heap.c@.
        -> a -- ^ Closure to decode
        -> IO (GenClosure b) -- ^ Heap representation of the closure

instance HasHeapRep (a :: TYPE 'LiftedRep) where
    getClosureDataX = getClosureX

instance HasHeapRep (a :: TYPE 'UnliftedRep) where
    getClosureDataX k x = getClosureX (k . unsafeCoerce#) (unsafeCoerce# x)

instance Int# ~ a => HasHeapRep (a :: TYPE 'IntRep) where
    getClosureDataX _ x = return $
        IntClosure { ptipe = PInt, intVal = I# x }

instance Word# ~ a => HasHeapRep (a :: TYPE 'WordRep) where
    getClosureDataX _ x = return $
        WordClosure { ptipe = PWord, wordVal = W# x }

instance Int64# ~ a => HasHeapRep (a :: TYPE 'Int64Rep) where
    getClosureDataX _ x = return $
        Int64Closure { ptipe = PInt64, int64Val = I64# (unsafeCoerce# x) }

instance Word64# ~ a => HasHeapRep (a :: TYPE 'Word64Rep) where
    getClosureDataX _ x = return $
        Word64Closure { ptipe = PWord64, word64Val = W64# (unsafeCoerce# x) }

instance Addr# ~ a => HasHeapRep (a :: TYPE 'AddrRep) where
    getClosureDataX _ x = return $
        AddrClosure { ptipe = PAddr, addrVal = I# (unsafeCoerce# x) }

instance Float# ~ a => HasHeapRep (a :: TYPE 'FloatRep) where
    getClosureDataX _ x = return $
        FloatClosure { ptipe = PFloat, floatVal = F# x }

instance Double# ~ a => HasHeapRep (a :: TYPE 'DoubleRep) where
    getClosureDataX _ x = return $
        DoubleClosure { ptipe = PDouble, doubleVal = D# x }

-- From GHC.Runtime.Heap.Inspect
amap' :: (t -> b) -> Array Int t -> [b]
amap' f (Array i0 i _ arr#) = map g [0 .. i - i0]
    where g (I# i#) = case indexArray# arr# i# of
                          (# e #) -> f e

-- | Takes any value (closure) as parameter and returns a tuple of:
-- * A 'Ptr' to the info table
-- * The memory of the closure as @[Word]@
-- * Pointers of the closure's @struct@ (in C code) in a @[Box]@.
-- The pointers are collected in @Heap.c@.
getClosureRaw :: a -> IO (Ptr StgInfoTable, [Word], [Box])
getClosureRaw x = do
    case unpackClosure# x of
-- This is a hack to cover the bootstrap compiler using the old version of
-- 'unpackClosure'. The new 'unpackClosure' return values are not merely
-- a reordering, so using the old version would not work.
#if MIN_VERSION_ghc_prim(0,5,3)
        (# iptr, dat, pointers #) -> do
#else
        (# iptr, pointers, dat #) -> do
#endif
             let nelems = (I# (sizeofByteArray# dat)) `div` wORD_SIZE
                 end = fromIntegral nelems - 1
                 rawWds = [W# (indexWordArray# dat i) | I# i <- [0.. end] ]
                 pelems = I# (sizeofArray# pointers)
                 ptrList = amap' Box $ Array 0 (pelems - 1) pelems pointers
             pure (Ptr iptr, rawWds, ptrList)

getClosureData :: forall rep (a :: TYPE rep) . HasHeapRep a => a -> IO Closure
getClosureData = getClosureDataX getClosureRaw


-- | This function returns a parsed heap representation ('GenClosure') of the
-- closure _at this moment_, even if it is unevaluated or an indirection or
-- other exotic stuff. Beware when passing something to this function, the same
-- caveats as for 'asBox' apply.
--
-- Inside a GHC context 'b' is usually a 'GHC.Exts.Heap.Closures.Box'
-- containing a thunk or an evaluated heap object. Outside it can be a
-- 'Word' for "raw" usage of pointers.
--
-- 'get_closure_raw' should provide low level details of the closure's heap
-- respresentation. The order of @[b]@ is significant and determined by
-- @collect_pointers()@ in @rts/Heap.c@.
--
-- For most use cases 'getClosureData' is an easier to use alternative.

getClosureX :: forall a b.
            (forall c . c -> IO (Ptr StgInfoTable, [Word], [b]))
            -- ^ Helper function to get info table, memory and pointers of the
            -- closure
            -> a -- ^ Closure to decode
            -> IO (GenClosure b) -- ^ Heap representation of the closure
getClosureX get_closure_raw x = do
    (iptr, wds, pts) <- get_closure_raw (unsafeCoerce# x)
    itbl <- peekItbl iptr
    -- The remaining words after the header
    let rawWds = drop (closureTypeHeaderSize (tipe itbl)) wds
    -- For data args in a pointers then non-pointers closure
    -- This is incorrect in non pointers-first setups
    -- not sure if that happens
        npts = drop (closureTypeHeaderSize (tipe itbl) + length pts) wds
    case tipe itbl of
        t | t >= CONSTR && t <= CONSTR_NOCAF -> do
            (p, m, n) <- dataConNames iptr
            if m == "GHC.ByteCode.Instr" && n == "BreakInfo"
              then pure $ UnsupportedClosure itbl
              else pure $ ConstrClosure itbl pts npts p m n

        t | t >= THUNK && t <= THUNK_STATIC -> do
            pure $ ThunkClosure itbl pts npts

        THUNK_SELECTOR -> do
            unless (length pts >= 1) $
                fail "Expected at least 1 ptr argument to THUNK_SELECTOR"
            pure $ SelectorClosure itbl (head pts)

        t | t >= FUN && t <= FUN_STATIC -> do
            pure $ FunClosure itbl pts npts

        AP -> do
            unless (length pts >= 1) $
                fail "Expected at least 1 ptr argument to AP"
            -- We expect at least the arity, n_args, and fun fields
            unless (length rawWds >= 2) $
                fail $ "Expected at least 2 raw words to AP"
            let splitWord = rawWds !! 0
            pure $ APClosure itbl
#if defined(WORDS_BIGENDIAN)
                (fromIntegral $ shiftR splitWord (wORD_SIZE_IN_BITS `div` 2))
                (fromIntegral splitWord)
#else
                (fromIntegral splitWord)
                (fromIntegral $ shiftR splitWord (wORD_SIZE_IN_BITS `div` 2))
#endif
                (head pts) (tail pts)

        PAP -> do
            unless (length pts >= 1) $
                fail "Expected at least 1 ptr argument to PAP"
            -- We expect at least the arity, n_args, and fun fields
            unless (length rawWds >= 2) $
                fail "Expected at least 2 raw words to PAP"
            let splitWord = rawWds !! 0
            pure $ PAPClosure itbl
#if defined(WORDS_BIGENDIAN)
                (fromIntegral $ shiftR splitWord (wORD_SIZE_IN_BITS `div` 2))
                (fromIntegral splitWord)
#else
                (fromIntegral splitWord)
                (fromIntegral $ shiftR splitWord (wORD_SIZE_IN_BITS `div` 2))
#endif
                (head pts) (tail pts)

        AP_STACK -> do
            unless (length pts >= 1) $
                fail "Expected at least 1 ptr argument to AP_STACK"
            pure $ APStackClosure itbl (head pts) (tail pts)

        IND -> do
            unless (length pts >= 1) $
                fail "Expected at least 1 ptr argument to IND"
            pure $ IndClosure itbl (head pts)

        IND_STATIC -> do
            unless (length pts >= 1) $
                fail "Expected at least 1 ptr argument to IND_STATIC"
            pure $ IndClosure itbl (head pts)

        BLACKHOLE -> do
            unless (length pts >= 1) $
                fail "Expected at least 1 ptr argument to BLACKHOLE"
            pure $ BlackholeClosure itbl (head pts)

        BCO -> do
            unless (length pts >= 3) $
                fail $ "Expected at least 3 ptr argument to BCO, found "
                        ++ show (length pts)
            unless (length rawWds >= 4) $
                fail $ "Expected at least 4 words to BCO, found "
                        ++ show (length rawWds)
            let splitWord = rawWds !! 3
            pure $ BCOClosure itbl (pts !! 0) (pts !! 1) (pts !! 2)
#if defined(WORDS_BIGENDIAN)
                (fromIntegral $ shiftR splitWord (wORD_SIZE_IN_BITS `div` 2))
                (fromIntegral splitWord)
#else
                (fromIntegral splitWord)
                (fromIntegral $ shiftR splitWord (wORD_SIZE_IN_BITS `div` 2))
#endif
                (drop 4 rawWds)

        ARR_WORDS -> do
            unless (length rawWds >= 1) $
                fail $ "Expected at least 1 words to ARR_WORDS, found "
                        ++ show (length rawWds)
            pure $ ArrWordsClosure itbl (head rawWds) (tail rawWds)

        t | t >= MUT_ARR_PTRS_CLEAN && t <= MUT_ARR_PTRS_FROZEN_CLEAN -> do
            unless (length rawWds >= 2) $
                fail $ "Expected at least 2 words to MUT_ARR_PTRS_* "
                        ++ "found " ++ show (length rawWds)
            pure $ MutArrClosure itbl (rawWds !! 0) (rawWds !! 1) pts

        t | t >= SMALL_MUT_ARR_PTRS_CLEAN && t <= SMALL_MUT_ARR_PTRS_FROZEN_CLEAN -> do
            unless (length rawWds >= 1) $
                fail $ "Expected at least 1 word to SMALL_MUT_ARR_PTRS_* "
                        ++ "found " ++ show (length rawWds)
            pure $ SmallMutArrClosure itbl (rawWds !! 0) pts

        t | t == MUT_VAR_CLEAN || t == MUT_VAR_DIRTY -> do
            unless (length pts >= 1) $
                fail $ "Expected at least 1 words to MUT_VAR, found "
                        ++ show (length pts)
            pure $ MutVarClosure itbl (head pts)

        t | t == MVAR_CLEAN || t == MVAR_DIRTY -> do
            unless (length pts >= 3) $
                fail $ "Expected at least 3 ptrs to MVAR, found "
                        ++ show (length pts)
            pure $ MVarClosure itbl (pts !! 0) (pts !! 1) (pts !! 2)

        BLOCKING_QUEUE ->
            pure $ OtherClosure itbl pts wds
        --    pure $ BlockingQueueClosure itbl
        --        (pts !! 0) (pts !! 1) (pts !! 2) (pts !! 3)

        --  pure $ OtherClosure itbl pts wds
        --
        WEAK ->
            pure $ WeakClosure
                { info = itbl
                , cfinalizers = pts !! 0
                , key = pts !! 1
                , value = pts !! 2
                , finalizer = pts !! 3
                , link = pts !! 4
                }
        TSO -> do
            unless (length pts == 6) $
                fail $ "Expected 6 ptr arguments to TSO, found "
                        ++ show (length pts)

            allocaArray (length wds) (\ptr -> do
                pokeArray ptr wds

                fields <- FFIClosures.peekTSOFields peekStgTSOProfInfo ptr
                pure $ TSOClosure
                    { info = itbl
                    , unsafe_link = (pts !! 0)
                    , unsafe_global_link = (pts !! 1)
                    , tsoStack = (pts !! 2)
                    , unsafe_trec = (pts !! 3)
                    , unsafe_blocked_exceptions = (pts !! 4)
                    , unsafe_bq = (pts !! 5)
                    , what_next = FFIClosures.tso_what_next fields
                    , why_blocked = FFIClosures.tso_why_blocked fields
                    , flags = FFIClosures.tso_flags fields
                    , threadId = FFIClosures.tso_threadId fields
                    , saved_errno = FFIClosures.tso_saved_errno fields
                    , tso_dirty = FFIClosures.tso_dirty fields
                    , alloc_limit = FFIClosures.tso_alloc_limit fields
                    , tot_stack_size = FFIClosures.tso_tot_stack_size fields
                    , prof = FFIClosures.tso_prof fields
                    }
                )
        STACK -> do
            unless (length pts == 1) $
                fail $ "Expected 1 ptr argument to STACK, found "
                        ++ show (length pts)

            allocaArray (length wds) (\ptr -> do
                pokeArray ptr wds

                fields <- FFIClosures.peekStackFields ptr

                pure $ StackClosure
                    { info = itbl
                    , stack_size = FFIClosures.stack_size fields
                    , stack_dirty = FFIClosures.stack_dirty fields
                    , unsafeStackPointer = (pts !! 0)
                    , unsafeStack  = FFIClosures.stack fields
#if __GLASGOW_HASKELL__ >= 811
                    , stack_marking = FFIClosures.stack_marking fields
#endif
                    }
                )
        _ ->
            pure $ UnsupportedClosure itbl

-- | Like 'getClosureDataX', but taking a 'Box', so it is easier to work with.
getBoxedClosureData :: Box -> IO Closure
getBoxedClosureData (Box a) = getClosureData a
