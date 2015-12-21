import Control.Concurrent.MVar
import Control.Exception
import Data.IORef
import Foreign.C.Error (throwErrnoIfMinus1Retry_)
import Foreign.Marshal.Alloc (alloca)
import Foreign.Storable
import System.Directory
import GHC.Event
import System.IO
--import System.IO.Temp
import System.Posix.IO
import System.Posix.Internals (c_close, c_read, c_write)
import System.Posix.Types (Fd(..))
import System.Posix.Files (createNamedPipe)

withSystemTempDirectory :: FilePath -> (FilePath -> IO ()) -> IO ()
withSystemTempDirectory name action = do
    tmpDir <- getTemporaryDirectory
    let path = tmpDir </> name
    createDirectory path
    action path
    removeDirectoryRecursive path

withTemporaryPipe :: ((OpenMode -> IO Fd) -> IO ()) -> IO ()
withTemporaryPipe action = withSystemTempDirectory "event.dir" $ \dir->do
    let path = dir </> "pipe"
    createNamedPipe path 0666
    action $ \mode->openFd path mode Nothing defaultFileFlags
    removeFile path

main = do
  Just mgr <- getSystemEventManager
  withTemporaryPipe $ \open -> do
    writeFd <- open WriteOnly
    readFd <- open ReadOnly
    let readCallback :: FdKey -> Event -> IO ()
        readCallback fdKey ev = putStrLn "callback"
    registerFd mgr readCallback readFd evtRead MultiShot
    fdWrite writeFd "hello world"
    fdWrite writeFd "mice"
    return ()

(</>) :: FilePath -> FilePath -> FilePath
a </> b = a ++ "/" ++ b
