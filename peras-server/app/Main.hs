{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Main where

import Data.Text (Text)
import Data.Version (showVersion)
import Network.Wai.Handler.Warp (Port)
import qualified Options.Applicative as O
import Paths_peras_server (version)
import Peras.Server (runServer)

main :: IO ()
main = do
  Command{..} <- O.execParser commandParser
  runServer creds port

data Command = Command
  { port :: Port
  , creds :: [(Text, Text)]
  }
  deriving (Eq, Ord, Read, Show)

commandParser :: O.ParserInfo Command
commandParser =
  let commandOptions =
        Command
          <$> O.option
            O.auto
            (O.long "port" <> O.metavar "PORT" <> O.value 8091 <> O.help "Port on which the server listens.")
          <*> O.many credParser
      credParser =
        (,)
          <$> O.strOption (O.long "username" <> O.metavar "STRING" <> O.help "Authorized user.")
          <*> O.strOption (O.long "password" <> O.metavar "STRING" <> O.help "Password for authorized user.")
   in O.info
        ( O.helper
            <*> O.infoOption ("peras-server " <> showVersion version) (O.long "version" <> O.help "Show version.")
            <*> commandOptions
        )
        ( O.fullDesc
            <> O.progDesc "This server provides Peras simulations."
            <> O.header "peras-server: server Peras simulations"
        )
