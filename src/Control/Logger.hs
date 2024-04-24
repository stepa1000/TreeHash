{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

-- | The logger interface module. It should not define a specific
-- implementation.
module Class.Logger where

import Data.Yaml
import GHC.Generics
import Control.Concurrent.STM.TVar
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
import Data.Aeson as Aeson
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
import Data.Other.Utils

data LogLevel
  = Debug
  | Info
  | Warning
  | Error
  deriving (Show, Eq, Ord, Generic, ToJSON, FromJSON)

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

type AdjLogL = (Env String) :.: (Env LogLevel)

type AdjLogR = (Reader LogLevel) :.: (Reader String) 

instance Monad m => MonadLoger (M.AdjointT AdjLogL AdjLogR m) where
  logDebugM str = do
    sl <- adjFst $ adjGetEnv
    ll <- adjSnd $ adjGetEnv
    adjFst $ adjSetEnv (sl ++ "/n" ++ (logDebug ll str)) (Identity ())
  logInfoM str = do
    sl <- adjFst $ adjGetEnv
    ll <- adjSnd $ adjGetEnv
    adjFst $ adjSetEnv (sl ++ "/n" ++ (logInfo ll str)) (Identity ())
  logWarningM str = do
    sl <- adjFst $ adjGetEnv
    ll <- adjSnd $ adjGetEnv
    adjFst $ adjSetEnv (sl ++ "/n" ++ (logWarning ll str)) (Identity ())
  logErrorM str = do
    sl <- adjFst $ adjGetEnv
    ll <- adjSnd $ adjGetEnv
    adjFst $ adjSetEnv (sl ++ "/n" ++ (logError ll str)) (Identity ())