{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}

-- | The logger interface module. It should not define a specific
-- implementation.
module Control.Logger where

import GHC.Generics
import Control.Core.Composition
import Control.Core.Biparam
import Control.Monad.Reader
import Data.Functor.Adjunction
import Control.Comonad.Trans.Env
import Control.Comonad.Trans.Adjoint as W
import Control.Comonad
import Debug.Trace
import Data.Functor.Identity
import Prelude as P
import Data.Sequence as Seq
import System.Random
import System.IO
import Data.Hashable
import Data.HashSet as Set
import Data.HashMap.Lazy as Map
import Data.Tree as Tree
import Data.IntMap as IMap
import Data.Maybe
import Data.Graph.Inductive.PatriciaTree as G
import Data.Graph.Inductive.Graph as G
import Data.ByteString as B
import Data.Word
-- import Data.Aeson as Aeson
import Control.Monad.Trans.Adjoint as M
import Data.Functor.Adjunction
import Control.Monad.Reader
import Control.Monad
import Control.Exception
import Control.Comonad.Env
import Control.Monad.IO.Class
import Control.Concurrent.MVar
import Control.Concurrent
import GHC.Generics
import AI.BPANN
import Data.Monoid
import Control.Base.Comonad
import Control.Core.Biparam
import Control.Core.Composition
import Data.Functor.Identity
import Data.History
import Data.NodeHash
import Other.Utils

data LogLevel
  = Debug
  | Info
  | Warning
  | Error
  deriving (Show, Eq, Ord, Generic)

logDebug,logInfo,logWarning,logError :: LogLevel -> String -> String
logDebug ll s | ll <= Debug     = show Debug ++ ":" ++ s 
logDebug _ _= ""
logInfo ll s | ll <= Info       = show Info ++ ":" ++ s
logInfo _ _ = ""
logWarning ll s | ll <= Warning = show Warning ++ ":" ++ s 
logWarning _ _ =""
logError ll s | ll <= Error     = show Error ++ ":" ++ s  
logError _ _ = ""

-- | Concatenates a text and an instance of 'Show'. This is a
-- convenience function to make logger function applications more
-- concise:
--
-- > Log.logError (hLogger h) "The error code is " .< e
(.<) :: (Show a) => String -> a -> String
text .< a = text <> (show a)

class MonadLoger m where
  logDebugM :: String -> m ()
  logInfoM :: String -> m ()
  logWarningM :: String -> m ()
  logErrorM :: String -> m ()

type AdjLogL = (Env Handle) :.: (Env LogLevel)

type AdjLogR = (Reader LogLevel) :.: (Reader Handle) 

openHandleWrite :: (Monad m, MonadIO m) =>
  FilePath ->
  M.AdjointT 
    AdjLogL
    AdjLogR
    m ()
openHandleWrite fp = do
  h <- liftIO $ openFile fp WriteMode
  liftIO $ hPutStrLn h "Logger is open"
  s <- liftIO $ hShow h
  liftIO $ hPutStrLn h s
  traceShowM s
  b <- liftIO $ hIsWritable h
  traceShowM b 
  adjFst $ adjSetEnv h (Identity ())

instance (Monad m, MonadIO m) => MonadLoger (M.AdjointT AdjLogL AdjLogR m) where
  logDebugM str = do
    sl <- adjFst $ adjGetEnv
    ll <- adjSnd $ adjGetEnv
    liftIO $ hPutStrLn sl $ logDebug ll str 
  logInfoM str = do
    sl <- adjFst $ adjGetEnv
    ll <- adjSnd $ adjGetEnv
    liftIO $ hPutStrLn sl $ logInfo ll str 
  logWarningM str = do
    sl <- adjFst $ adjGetEnv
    ll <- adjSnd $ adjGetEnv
    liftIO $ hPutStrLn sl $ logWarning ll str
  logErrorM str = do
    sl <- adjFst $ adjGetEnv
    ll <- adjSnd $ adjGetEnv
    liftIO $ hPutStrLn sl $ logError ll str

instance (Monad m) => MonadLoger (M.AdjointT (Env LogLevel) (Reader LogLevel) m) where
  logDebugM str = do
    ll <- adjGetEnv
    if (not $ P.null str) 
      then traceShowM $ logDebug ll str
      else return ()
  logInfoM str = do
    ll <- adjGetEnv
    when (not $ P.null str) $
      traceShowM $ logInfo ll str
  logWarningM str = do
    ll <- adjGetEnv
    when (not $ P.null str) $
      traceShowM $ logWarning ll str
  logErrorM str = do
    ll <- adjGetEnv
    when (not $ P.null str) $
      traceShowM $ logError ll str

instance (MonadIO m, Monad m, Traversable f, Adjunction f g) => 
  MonadIO (M.AdjointT f g m) where
  liftIO = lift . liftIO
{-}
instance (MonadLoger m, Monad m, Traversable f, Adjunction f g) => 
  MonadLoger (M.AdjointT f g m) where
  logDebugM = lift . logDebugM
  logInfoM = lift . logInfoM
  logWarningM = lift . logWarningM
  logErrorM = lift . logErrorM
-}