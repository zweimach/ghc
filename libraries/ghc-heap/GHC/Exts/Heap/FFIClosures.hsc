{-# LANGUAGE CPP #-}
module GHC.Exts.Heap.FFIClosures where

#include "Rts.h"

import Prelude
import Foreign
import GHC.Exts.Heap.ProfInfo.Types

-- TODO use sum type for what_next, why_blocked, flags?

data TSOFields = TSOFields {
    tso_what_next :: Word16,
    tso_why_blocked :: Word16,
    tso_flags :: Word32,
-- Unfortunately block_info is a union without clear discriminator.
--    block_info :: TDB,
    tso_threadId :: Word64,
    tso_saved_errno :: Word32,
    tso_dirty:: Word32,
    tso_alloc_limit :: Int64,
    tso_tot_stack_size :: Word32,
    tso_prof :: Maybe StgTSOProfInfo
}

-- | Get non-pointer fields from @StgTSO_@ (@TSO.h@)
peekTSOFields :: (Ptr tsoPtr -> IO (Maybe StgTSOProfInfo))
                -> Ptr tsoPtr
                -> IO TSOFields
peekTSOFields peekProfInfo ptr = do
    what_next' <- (#peek struct StgTSO_, what_next) ptr
    why_blocked' <- (#peek struct StgTSO_, why_blocked) ptr
    flags' <- (#peek struct StgTSO_, flags) ptr
    threadId' <- (#peek struct StgTSO_, id) ptr
    saved_errno' <- (#peek struct StgTSO_, saved_errno) ptr
    dirty' <- (#peek struct StgTSO_, dirty) ptr
    alloc_limit' <- (#peek struct StgTSO_, alloc_limit) ptr
    tot_stack_size' <- (#peek struct StgTSO_, tot_stack_size) ptr
    tso_prof' <- peekProfInfo ptr

    return TSOFields {
        tso_what_next = what_next',
        tso_why_blocked = why_blocked',
        tso_flags = flags',
        tso_threadId = threadId',
        tso_saved_errno = saved_errno',
        tso_dirty= dirty',
        tso_alloc_limit = alloc_limit',
        tso_tot_stack_size = tot_stack_size',
        tso_prof = tso_prof'
    }

data StackFields = StackFields {
    stack_size :: Word32,
    stack_dirty :: Word8,
#if __GLASGOW_HASKELL__ >= 811
    stack_marking :: Word8,
#endif
    stack :: [Word]
}

-- | Get non-closure fields from @StgStack_@ (@TSO.h@)
peekStackFields :: Ptr a -> IO StackFields
peekStackFields ptr = do
    stack_size' <- (#peek struct StgStack_, stack_size) ptr ::IO Word32
    dirty' <- (#peek struct StgStack_, dirty) ptr
#if __GLASGOW_HASKELL__ >= 811
    marking' <- (#peek struct StgStack_, marking) ptr
#endif

    let stackPtr = (#ptr struct StgStack_, stack) ptr
    stack' <- peekArray (fromIntegral stack_size') stackPtr

    return StackFields {
        stack_size = stack_size',
        stack_dirty = dirty',
#if __GLASGOW_HASKELL__ >= 811
        stack_marking = marking',
#endif
        stack = stack'
    }
