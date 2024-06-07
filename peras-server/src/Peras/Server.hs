{-# LANGUAGE OverloadedStrings #-}

module Peras.Server where

import qualified Network.Wai as Wai
import qualified Network.Wai.Handler.Warp as Warp
import qualified Network.Wai.Handler.WebSockets as WS
import Network.Wai.Middleware.RequestLogger (logStdoutDev)
import qualified Network.WebSockets as WS
import Peras.Server.App (wsapp)
import qualified Web.Scotty as Sc

runServer :: Warp.Port -> IO ()
runServer port =
  Warp.runSettings (Warp.setPort port Warp.defaultSettings)
    . WS.websocketsOr WS.defaultConnectionOptions wsapp
    =<< scottyApp

scottyApp :: IO Wai.Application
scottyApp =
  Sc.scottyApp $ do
    Sc.middleware logStdoutDev

    Sc.get "/" $
      Sc.redirect "/index.html"

    Sc.get "/index.html" $
      Sc.file "index.html"

    Sc.get "/index.js" $
      Sc.file "index.js"

    Sc.get "/peras.css" $
      Sc.file "peras.css"
