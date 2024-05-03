{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeFamilies #-}

module Control.NN.Base where

import Prelude as P
import Data.List as P
import Data.Foldable as P
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
-- import Data.Graph.Inductive.Monad.IOArray as G
-- import Data.Graph.Inductive.Monad as G
import Data.ByteString as B
import Data.Word
import Data.Aeson as Aeson
import Data.Time.Clock
import Debug.Trace
import Control.Monad.Trans.Adjoint as M
import Data.Functor.Adjunction
import Control.Monad.Reader
import Control.Monad
import Control.Applicative
import Control.Exception
import Control.Comonad.Env
import Control.Monad.IO.Class
import Control.Concurrent.MVar
import Control.Concurrent
import Control.Seq
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
import Control.Logger
import Data.Adj.Graph

type family SysHash sys -- = Int

type family SysContainer sys :: * -> *

type family SysNetwork sys

type SysCNetwork sys = SysContainer sys (SysNetwork sys) -- = [Network]

type family SysConfigNetwork sys -- Layers = [Int]

type AdjSysNetworkL sys = (Env (SysCNetwork sys)) :.: (Env (SysConfigNetwork sys))

type AdjSysNetworkR sys = (Reader (SysConfigNetwork sys)) :.: (Reader (SysCNetwork sys)) 

data HandlerSysGetNN sys = HandlerSysGetNN
	{ sysHashNetwork :: SysNetwork sys -> SysHash sys
	}
{-}
sysGetNN :: (Monad m, MonadIO m, MonadLoger m, Eq (SysHash sys)) =>
	HandlerSysGetNN sys ->
	SysHash sys -> 
	M.AdjointT 
		(AdjSysNetworkL sys) 
		(AdjSysNetworkR sys)
		m
		(Maybe (SysNetwork sys))
sysGetNN sys h = do
	--lift $ logDebugM "Start: getNN"
	ln <- adjFst $ adjGetEnv
	--lift $ logDebugM $ "Length list get NN: " .< (P.length ln) ==
	let mn = P.find (\n-> hash (packNetwork n) == h) ln
	let ln' = P.filter (\n-> not $ hash (packNetwork n) == h) ln
	--lift $ logDebugM $ "find NN: " .< (isJust mn)
	--lift $ logDebugM $ "Length list set NN: " .< (P.length ln')
	adjFst $ adjSetEnv ln' (Identity ())
	--lift $ logDebugM "End: getNN"
	return mn
-}