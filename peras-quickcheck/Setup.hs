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
  ConfigFlags (..),
  fromFlag,
 )
import Distribution.Simple.UserHooks (
  UserHooks (..),
 )
import Distribution.Simple.Utils (
  rawSystemProc,
 )
import System.Directory (
  doesDirectoryExist,
  getCurrentDirectory,
 )
import System.FilePath ((</>))
import System.Process (cwd, proc)

import qualified Distribution.PackageDescription as Pkg

main :: IO ()
main = do
  dir <- getCurrentDirectory -- Assume it's the directory containing the .cabal file
  perasRustExists <- doesDirectoryExist $ dir </> "../peras-rust"
  defaultMainWithHooks $
    if perasRustExists
      then
        simpleUserHooks
          { confHook = rustConfHook
          , buildHook = rustBuildHook
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
                          { Pkg.extraLibDirs = (dir </> "../peras-rust/target/release") : Pkg.extraLibDirs libraryBuildInfo
                          , Pkg.includes = "peras.h" : Pkg.includes libraryBuildInfo
                          , Pkg.includeDirs = (dir </> "../peras-rust/") : Pkg.includeDirs libraryBuildInfo
                          }
                    }
            }
      }

rustBuildHook ::
  Pkg.PackageDescription ->
  LocalBuildInfo ->
  UserHooks ->
  BuildFlags ->
  IO ()
rustBuildHook description localBuildInfo hooks flags = do
  putStrLn "[rust] Compiling Rust dependencies..."
  putStrLn "[rust] cargo build --release"
  dir <- getCurrentDirectory -- Assume it's the directory containing the .cabal file
  let cargo = proc "cargo" ["build"]
  rawSystemProc (fromFlag $ buildVerbosity flags) cargo{cwd = Just (dir </> ".." </> "peras-rust")}
  buildHook simpleUserHooks description localBuildInfo hooks flags
