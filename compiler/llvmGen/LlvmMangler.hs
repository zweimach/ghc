{-# LANGUAGE CPP, MagicHash, UnboxedTuples #-}
#include "HsVersions.h"
-- -----------------------------------------------------------------------------
-- | GHC LLVM Mangler
--
-- This script processes the assembly produced by LLVM, rewriting all symbols
-- of type @function to @object. This keeps them from going through the PLT,
-- which would be bad due to tables-next-to-code. On x86_64,
-- it also rewrites AVX instructions that require alignment to their
-- unaligned counterparts, since the stack is only 16-byte aligned but these
-- instructions require 32-byte alignment.
--

module LlvmMangler ( llvmFixupAsm ) where

import DynFlags ( DynFlags )
import ErrUtils ( showPass )

import Control.Exception
import qualified Data.ByteString.Char8 as B
import System.IO

-- Search Predicates
isType :: B.ByteString -> Bool
isType = B.isPrefixOf (B.pack ".type")

-- | This rewrites @.type@ annotations of function symbols to @%object@.
-- This is done as the linker can relocate @%functions@ through the
-- Procedure Linking Table (PLT). This is bad since we expect that the
-- info table will appear directly before the symbol's location. In the
-- case that the PLT is used, this will be not an info table but instead
-- some random PLT garbage.
rewriteSymType :: B.ByteString -> [B.ByteString]
rewriteSymType string = [B.pack "\t", rewrite '@' $ rewrite '%' string]
  where
    rewrite :: Char -> B.ByteString -> B.ByteString
    rewrite prefix = replaceOnce funcType objType
      where
        funcType = prefix `B.cons` B.pack "function"
        objType  = prefix `B.cons` B.pack "object"

#if x86_64_TARGET_ARCH
rewriteVmovdqa :: B.ByteString -> [B.ByteString]
rewriteVmovdqa string = [B.pack "\tvmovdqu", length "vmovdqa" `B.drop` string]

rewriteVmovap :: B.ByteString -> [B.ByteString]
rewriteVmovap string = [B.pack "\tvmovup", length "vmovap" `B.drop` string]

isVmovap :: B.ByteString -> Bool
isVmovap = B.isPrefixOf (B.pack "vmovap")

isVmovdqa :: B.ByteString -> Bool
isVmovdqa = B.isPrefixOf (B.pack "vmovdqa")
#endif

-- | Read in assembly file and process
llvmFixupAsm :: DynFlags -> FilePath -> FilePath -> IO ()
llvmFixupAsm dflags f1 f2 = {-# SCC "llvm_mangler" #-} do
    showPass dflags "LLVM Mangler"
    r <- openBinaryFile f1 ReadMode
    w <- openBinaryFile f2 WriteMode
    go r w
    hClose r
    hClose w
    return ()
  where
    go :: Handle -> Handle -> IO ()
    go r w = do
      e_l <- (try (B.hGetLine r))::IO (Either IOError B.ByteString)
      let writeline a = B.hPutStrLn w (fixLine a) >> go r w
      case e_l of
        Right l -> writeline l
        Left _  -> return ()



-- | This function splits a line of assembly code into the label and the
-- rest of the code.
splitLine :: B.ByteString -> (# B.ByteString, B.ByteString #)
splitLine l = let isSpace ' ' = True
                  isSpace '\t' = True
                  isSpace _ = False
                  (symbol, rest) = B.span (not . isSpace) l
              in (# symbol, B.dropWhile isSpace rest #)

-- | This function fixes @.type@ directives. It also rewrites aligned AVX
-- instructions to their unaligned counterparts on x86-64. This is
-- necessary because the stack is not adequately aligned for aligned AVX
-- spills, so LLVM would emit code that adjusts the stack pointer
-- and disable tail call optimization. Both would be catastrophic
-- here so GHC tells LLVM that the stack is 32-byte aligned (even
-- though it isn't) and then rewrites the instructions in the
-- mangler.
fixLine :: B.ByteString -> B.ByteString
fixLine l = case splitLine l of
  (# symbol, rest #) | isType rest -> B.concat (symbol : rewriteSymType rest)
#if x86_64_TARGET_ARCH
                     | isVmovap rest -> B.concat (symbol : rewriteVmovap rest)
                     | isVmovdqa rest -> B.concat (symbol : rewriteVmovdqa rest)
#endif
                     | otherwise -> l

replaceOnce :: B.ByteString -> B.ByteString -> B.ByteString -> B.ByteString
replaceOnce matchBS replaceOnceBS = loop
  where
    loop :: B.ByteString -> B.ByteString
    loop cts =
        case B.breakSubstring matchBS cts of
          (hd,tl) | B.null tl -> hd
                  | otherwise -> hd `B.append` replaceOnceBS `B.append`
                                 B.drop (B.length matchBS) tl
