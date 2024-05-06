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
{-# LANGUAGE Arrows #-}
{-# LANGUAGE RankNTypes #-}

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
import Control.Arrow
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
import Data.NN

type family SysHash sys -- = Int

type family SysContainer sys :: * -> *

type family SysNetwork sys

type SysCNetwork sys = SysContainer sys (SysNetwork sys) -- = [Network]

type family SysConfigNetwork sys -- Layers = [Int]

type AdjSysNetworkL sys = (Env (SysCNetwork sys)) :.: (Env (SysConfigNetwork sys))

type AdjSysNetworkR sys = (Reader (SysConfigNetwork sys)) :.: (Reader (SysCNetwork sys)) 

type family ArrSys sys :: * -> * -> *

data HandlerSysGetNN sys = HandlerSysGetNN
	{ sysHashNetworkGNN :: ArrSys sys (SysNetwork sys) (SysHash sys)
	-- , sysLogDebugGNN :: ArrSys sys String ()
	, sysGetListNN :: ArrSys sys () (SysCNetwork sys)
	, sysSetListNN :: ArrSys sys (SysCNetwork sys) ()
	, sysLengthGNN :: forall a. ArrSys sys (SysContainer sys a) Int
	, sysFindGNN :: forall a. 
		ArrSys sys a Bool -> 
		ArrSys sys (SysContainer sys a) (Maybe a)
	, sysFilterGNN :: forall a.
		ArrSys sys a Bool ->
		ArrSys sys (SysContainer sys a) (SysContainer sys a)
	}

sysGetNN :: (Eq (SysHash sys), Arrow (ArrSys sys), ArrowApply (ArrSys sys)) =>
	HandlerSysGetNN sys ->
	ArrSys sys
		(SysHash sys) 
		(Maybe (SysNetwork sys))
sysGetNN he = proc ha -> do
	ln <- sysGetListNN he -< ()
	len <- sysLengthGNN he -< ln
	(ma,ln2) <- 
		((sysFindGNN he)
			(proc a -> do
				ha2 <- sysHashNetworkGNN he -< a
				returnA -< ha2 == ha)) &&&
		((sysFilterGNN he)
			(proc a -> do
				ha2 <- sysHashNetworkGNN he -< a
				returnA -< not $ ha2 == ha
			)) -<< ln
	len2 <- sysLengthGNN he -< ln2
	sysSetListNN he -< ln2
	returnA -< ma

type family SysSizeNN sys

type family SysLayers sys

type family SysSeed sys

data HandlerSysCreatRandomNetworks sys = HandlerSysCreatRandomNetworks
	{ sysGetLayers :: ArrSys sys () [SysLayers sys]
	, sysRandomSeed :: ArrSys sys () (SysSeed sys)
	, sysCreateRandomNetwork ::
		ArrSys sys 
			(SysSeed sys, [SysLayers sys]) 
			(SysNetwork sys)
	, sysFromList :: ArrSys sys [SysNetwork sys] (SysCNetwork sys)
	, sysSetCNetwork :: ArrSys sys (SysCNetwork sys) ()
}

unArrowMonad (ArrowMonad a) = a

sysCreatRandomNetworks :: 
	(Arrow (ArrSys sys), ArrowApply (ArrSys sys)) =>
	HandlerSysCreatRandomNetworks sys ->
	ArrSys sys
		(SysSizeNN sys)
		()
sysCreatRandomNetworks sysGetNN = proc snn -> do
	ll <- sysGetLayers sys -< ()
	ln <- unArrowMonad $ mapM (\_->ArrowMonad $ proc _ -> do
		s <- sysRandomSeed sys -< ()
		sysCreateRandomNetwork sys -< (s,ll)
		) [0..snn] -<< ()
	cn <- sysFromList sys -< ln
	sysSetCNetwork sys -< cn

type family SysAlfa sys

type family SysErrorTrain sys

type family SysTrainData sys

type family SysAttemptTrain sys

data HandlerSysTrain sys = HandlerSysTrain
	{ sysGetCNetwork :: ArrSys sys () (SysCNetwork sys)
	, sysSetCNetwork :: ArrSys sys (SysCNetwork sys) ()
	, sysTrain :: 
		ArrSys sys 
			( SysAttemptTrain sys
			, SysAlfa sys
			, SysErrorTrain sys
			, SysNetwork sys
			, [SysTrainData sys]
			)
			(Maybe (SysNetwork sys))
	, sysCatMaybes :: 
		ArrSys sys 
			(SysContainer sys (Maybe (SysNetwork sys))) 
			(SysCNetwork sys)
	, sysMapCN :: forall a b.
		ArrSys sys a b ->
		ArrSys sys (SysContainer sys a) (SysContainer sys b)
}

sysTrain :: 
	(Arrow (ArrSys sys), ArrowApply (ArrSys sys)) =>
	HandlerSysTrain sys ->
	ArrSys sys
		( SysAlfa sys
		, SysErrorTrain sys
		, SysAttemptTrain sys
		, [SysTrainData sys]
		)
		()
sysTrain sys = proc (alfa,errorT,attt,ld) -> do
	cn <- sysGetCNetwork sys -< ()
	cn2 <- sysCatMaybes sys <<< sysMapCN sys
		(proc n -> do
			sysTrain -< (attt,alfa,errorT,n,ld)
		) -<< cn
	sysSetCNetwork sys -< cn2

data HandlerSysTrainP sys = HandlerSysTrainP
	{ sysGetCNetworkTP :: ArrSys sys () (SysCNetwork sys)
	, sysSetCNetworkTP :: ArrSys sys (SysCNetwork sys) ()
	, sysTrainTP :: 
		ArrSys sys 
			( SysAttemptTrain sys
			, SysAlfa sys
			, SysErrorTrain sys
			, SysNetwork sys
			, [SysTrainData sys]
			)
			(Maybe (SysNetwork sys))
	, sysCatMaybesTP :: 
		ArrSys sys 
			(SysContainer sys (Maybe (SysNetwork sys))) 
			(SysCNetwork sys)
	, sysMapCNTP :: forall a b.
		ArrSys sys a b ->
		ArrSys sys (SysContainer sys a) (SysContainer sys b)
	, sysFromJust :: forall a .
		ArrSys sys (Maybe a) a
}

sysTrainP :: 
	(Arrow (ArrSys sys), ArrowApply (ArrSys sys), ArrowPlus (ArrSys sys)) =>
	HandlerSysTrainP sys ->
	ArrSys sys
		( SysAlfa sys
		, SysErrorTrain sys
		, SysAttemptTrain sys
		, [[SysTrainData sys]]
		)
		()
sysTrainP sys = proc (alfa,errorT,attt,lld) -> do
	cn <- sysGetCNetwork sys -< ()
	cn2 <- (sysCatMaybes sys) <<< (sysMapCN sys)
		(proc n -> do
			unArrowMonad $ P.foldrM (\ld mn'->ArrowMonad $ (proc _ -> do
					n2 <- sysFromJust sys -< mn'
					sysTrain -< (attt,alfa,errorT,n,ld)
				) <+> (proc _ -> do
					sysTrain -< (attt,alfa,errorT,n,ld)	
				)
				) (Just n) lld -<< ()
		) -<< cn
	sysSetCNetwork sys -< cn2

{-}
calculateAdj :: 
	(	Monad m, MonadIO m,
		MonadLoger m
	) => 
	[Double] ->
	M.AdjointT 
		AdjNetworkL 
		AdjNetworkR
		m 
		[(Hash,[Double])]
calculateAdj ld = do
	lnold <- adjFst $ adjGetEnv
	let lh = fmap (hash . packNetwork) lnold
	let lc = fmap (\n-> calculate n ld) lnold
	ll <- adjSnd $ adjGetEnv
	return $ P.zip lh lc
-}