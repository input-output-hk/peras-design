import Prelude

import Data.Maybe (
  fromJust,
 )
import Distribution.Simple (
  Args,
  UserHooks (..),
  defaultMainWithHooks,
  simpleUserHooks,
 )
import Distribution.Simple.LocalBuildInfo (
  LocalBuildInfo (..),
 )
import Distribution.Simple.Setup (
  BuildFlags (..),
  CleanFlags (..),
  ConfigFlags (..),
  fromFlag,
 )
import Distribution.Simple.UserHooks (
  UserHooks (..),
 )
import Distribution.Simple.Utils (
  maybeExit,
  rawSystemProc,
 )
import Distribution.Verbosity (Verbosity)
import System.Directory (
  doesDirectoryExist,
  getCurrentDirectory,
 )
import System.FilePath ((</>))
import System.Process (cwd, proc)

import qualified Distribution.PackageDescription as Pkg

perasRustDir = ".." </> "peras-rust"

main :: IO ()
main = do
  dir <- getCurrentDirectory -- Assume it's the directory containing the .cabal file
  let rustDir = dir </> perasRustDir
  perasRustExists <- doesDirectoryExist rustDir
  defaultMainWithHooks $
    if perasRustExists
      then
        simpleUserHooks
          { preConf = \_ flags -> buildRust (fromFlag $ configVerbosity flags)
          , confHook = rustConfHook
          , postClean = \_ flags _ _ -> cleanRust (fromFlag $ cleanVerbosity flags)
          }
      else simpleUserHooks

rustConfHook ::
  (Pkg.GenericPackageDescription, Pkg.HookedBuildInfo) ->
  ConfigFlags ->
  IO LocalBuildInfo
rustConfHook (description, buildInfo) flags = do
  localBuildInfo <- confHook simpleUserHooks (description, buildInfo) flags
  let packageDescription = localPkgDescr localBuildInfo
  let library = fromJust $ Pkg.library packageDescription
  let libraryBuildInfo = Pkg.libBuildInfo library
  dir <- getCurrentDirectory
  return
    localBuildInfo
      { localPkgDescr =
          packageDescription
            { Pkg.library =
                Just
                  library
                    { Pkg.libBuildInfo =
                        libraryBuildInfo
                          { Pkg.extraLibDirs = (dir </> perasRustDir </> "target/debug") : Pkg.extraLibDirs libraryBuildInfo
                          , Pkg.includes = "peras.h" : Pkg.includes libraryBuildInfo
                          , Pkg.includeDirs = (dir </> perasRustDir) : Pkg.includeDirs libraryBuildInfo
                          }
                    }
            }
      }

buildRust :: Verbosity -> IO Pkg.HookedBuildInfo
buildRust verbosity = do
  putStrLn "[rust] Compiling Rust dependencies..."
  putStrLn "[rust] cargo build"
  dir <- getCurrentDirectory -- Assume it's the directory containing the .cabal file
  let cargo = proc "cargo" ["build"]
  maybeExit $ rawSystemProc verbosity cargo{cwd = Just (dir </> perasRustDir)}
  pure Pkg.emptyHookedBuildInfo

cleanRust :: Verbosity -> IO ()
cleanRust verbosity = do
  dir <- getCurrentDirectory -- Assume it's the directory containing the .cabal file
  let cargo = proc "cargo" ["clean"]
  maybeExit $ rawSystemProc verbosity cargo{cwd = Just (dir </> perasRustDir)}
