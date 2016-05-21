{- |
This module implements a simple float-in pass for combatting register
pressure.

The issue we are trying to address here is that the Core simplifier
is generally unwilling to float bindings to case branches if this would
require duplicating the binding's RHS in more than one branch. Consider,
for instance, this contrived example inspired by #10012,

@
write16Ints :: Bool -> (IO () -> IO r) -> (Int, Int, ..., Int) -> IO r
write16Ints cond (x0,x1,...,x15) = \cont ->
    let !f0  = x0 + 42
        !f1  = x1 + 13
       ...
        !f15 = x15 `mod` 3

        doWrite :: IO r
        doWrite = print f0 >> print f1 >> ... >> print f15 >> cont rng'
    in if cond
         then return $ BufferFull doWrite
         else doWrite
@

In particular, this was observed arising from rule rewriting done by the
@bytestring@ library, where @cond@ is a bounds check.

Without tis float-in pass, the above code can produce quite inefficient machine
code as the Core simplifier will not float the @fN@ towards their use-sites as
they are used in both case branches. Consequently, we end up with 16 live
variables, far more than we have registers on most machines. In order to produce
this code we must spill a significant amount of data out to memory.

We can avoid this by pushing the RHS down into each of the case branches at the
expense of some code bloat. For instance,

@
write16Ints :: Bool -> (IO () -> IO r) -> (Int, Int, ..., Int) -> IO r
write16Ints cond (x0,x1,...,x15) = \cont ->
    let !f0  = x0 + 42
        !f1  = x1 + 13
       ...
        !f15 = x15 `mod` 3

        doWrite :: IO r
        doWrite = print f0 >> print f1 >> ... >> print f15 >> cont rng'
    in if cond
         then return $ BufferFull doWrite
         else doWrite
@

The approach we take here is to look for bindings which occur only within case
branches and try to 

-}

module StgFloatIn ( stgFloatIn ) where

stgFloatIn :: DynFlags
           -> Module
           -> [StgBinding]
           -> IO [StgBinding]
stgFloatIn dflags this_mod binds = return binds'
  where
    binds' = undefined
