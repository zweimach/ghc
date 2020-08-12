import GHC.Exts.Heap.Closures
import GHC.Exts.Heap.FFIClosures
import TestUtils

main :: IO()
main = do
    assertEqual (parseTsoFlags 0) []
    assertEqual (parseTsoFlags 1) [TsoFlagsUnknownValue]
    assertEqual (parseTsoFlags 2) [TsoLocked]
    assertEqual (parseTsoFlags 4) [TsoBlockx]
    assertEqual (parseTsoFlags 8) [TsoInterruptible]
    assertEqual (parseTsoFlags 16) [TsoStoppedOnBreakpoint]
    assertEqual (parseTsoFlags 64) [TsoMarked]
    assertEqual (parseTsoFlags 128) [TsoSqueezed]
    assertEqual (parseTsoFlags 256) [TsoAllocLimit]

    assertEqual (parseTsoFlags 6) [TsoLocked, TsoBlockx]
