{-# LANGUAGE OverloadedStrings #-}

module Peras.Server where

import Control.Monad (unless)
import qualified Data.ByteString.Char8 as BS8
import Data.Text (Text)
import qualified Data.Text as T
import qualified Network.Wai as Wai
import qualified Network.Wai.Handler.Warp as Warp
import qualified Network.Wai.Handler.WebSockets as WS
import Network.Wai.Middleware.HttpAuth (
  AuthSettings (authIsProtected),
  CheckCreds,
  basicAuth,
 )
import Network.Wai.Middleware.RequestLogger (logStdoutDev)
import Network.Wai.Middleware.Static (static)
import qualified Network.WebSockets as WS
import Peras.Server.App (wsapp)
import qualified Web.Scotty as Sc

runServer :: [(Text, Text)] -> Warp.Port -> IO ()
runServer authorizedCreds port =
  Warp.runSettings (Warp.setPort port Warp.defaultSettings)
    . WS.websocketsOr WS.defaultConnectionOptions wsapp
    =<< scottyApp authorizedCreds

scottyApp :: [(Text, Text)] -> IO Wai.Application
scottyApp authorizedCreds =
  Sc.scottyApp $ do
    unless (null authorizedCreds)
      . Sc.middleware
      $ checkCreds authorizedCreds `basicAuth` "Peras Realm"{authIsProtected = const $ pure True}

    Sc.middleware logStdoutDev

    Sc.get "/" $
      Sc.redirect "/index.html"

    Sc.middleware static

checkCreds :: [(Text, Text)] -> CheckCreds
checkCreds authorized username password =
  pure $ (T.pack $ BS8.unpack username, T.pack $ BS8.unpack password) `elem` authorized
