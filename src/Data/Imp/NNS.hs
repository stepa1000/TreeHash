{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Data.Imp.NNS where

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
import Class.Logger
import Data.Imp.BSS

type NNAdjL a = 
	(ConfNNAdjL 
		(IMapNNRCAdjL 
			(NNSLPowAdjL 
				(NNSccListAdjL a)
				a)
	))

type NNAdjR a = 
	(ConfNNAdjR 
		(IMapNNRCAdjR
			(NNSLPowAdjR 
				(NNSccListAdjR a)
				a)
	))

type AdjunctorNN a = 
	M.AdjointT 
		(NNAdjL a) 
		(NNAdjR a)
		(M.AdjointT AdjLogL AdjLogR IO)

instance ClassConfNNAdj (NNAdjL a) (NNAdjR a) where
	liftConfNNAdj = adjFst

instance ClassIMapNNRAdj (NNAdjL a) (NNAdjR a) where
	liftIMapNNRAdj = adjSnd . adjFst

instance ClassMapGrAdj (NNAdjL a) (NNAdjR a) a where
	liftMapGrAdj = adjSnd . adjSnd . adjFst

instance ClassNNSLPowAdj (NNAdjL a) (NNAdjR a) a where
	liftNNSccListAdjGr = adjSnd . adjSnd . adjSnd . adjFst
	liftNNSccListAdjA = adjSnd . adjSnd . adjSnd . adjSnd

lernToNN :: MVar String -> SettingNN -> [(a,a)] -> AdjunctorNN a ()
lernToNN mvs spw lpw = do
	-- like lernToMemory
	mapM_ (\pw->do
		pr <- updateAPre $ fst pw
		updateAPost pw pr
		e <- liftIO $ tryTakeMVar mvs
		if e == (Just "s")
			then do				
				dm2 <- getDataNNSLPow
				lift $ encodeFile (fileForState spw) dm2
				lift $ print "safe sucsess"
			else return ()
		) lpw

data SettingNN = SettingNN 
	{ fileNNForRead :: FilePath
	, fileNNForState :: FilePath
}

initNNS :: SettingNN -> IO ()
initNNS spw = do
	m <- try @SomeException $ decodeFileStrict @(DataNNSLPow PWord) (fileNNForState spw)
	case m of
		(Right (Just _)) -> return ()
		_ -> encodeFile @(DataNNSLPow PWord) (fileNNForState spw) $ 
			DataNNSLPow 

startlTNN :: MVar String -> SettingNN -> AdjunctorNN a ()
startlTNN mvs spw = do
	(Just dm1) <- lift $ decodeFileStrict (fileNNForState spw) 
	setDataNNSLPow dm1

runAdjunctorNN = void .
	runAdjT [] .
	runAdjTfst [] .  
	runAdjTfst G.empty .
	runAdjTfst IMap.empty .