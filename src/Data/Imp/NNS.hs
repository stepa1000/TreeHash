{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Data.Imp.NNS where

import Prelude as P
import Data.Foldable as P
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
import Data.Graph.Inductive.Dot
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
import Other.Utils
import Control.Logger
import Data.Imp.BSS
import Data.NN

type NNAdjL a = 
	(ConfNNAdjL 
		(IMapNNRCAdjL 
			(MapGrAdjL 
				(NNSLPowAdjL 
					(NNSccListAdjL a) 
					a)
				a)
	))

type NNAdjR a = 
	(ConfNNAdjR 
		(IMapNNRCAdjR
			(MapGrAdjR
				(NNSLPowAdjR 
					(NNSccListAdjR a) 
					a)
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

instance NNSccListAdj (NNAdjL a) (NNAdjR a) a where
	liftNNSccListAdj = liftNNSccListAdjA

lernToNN :: (Hashable a, Show a, ToJSON a, ListDoubled a) => 
	MVar String -> SettingNN -> [(a,a)] -> AdjunctorNN a ()
lernToNN mvs spw lpw = do
	-- like lernToMemory
	mapM_ (\(npw::(a,a))->do
		(pr :: ( AllResult a, ConsequenceResult a)) <- updateAPre $ fst npw
		lift $ logInfoM $ "answer:" .< snd npw
		lift $ logInfoM $ "consequence:" .< (Map.keys $ snd pr)
		updateAPost npw pr
		e <- liftIO $ tryTakeMVar mvs
		if e == (Just "s")
			then do				
				dm2 <- getDataNNSLPow $ fst npw
				liftIO $ encodeFile (fileNNForState spw) dm2
				mapM (\gr->do
					liftIO $ P.writeFile ((fileNNGr spw) ++ ("/") ++ (show $ hash gr) ++ ".dot") $
						showDot $ fglToDotUnlabeled gr
					) $ Map.keys $ hmrcgr dm2
				liftIO $ print "safe sucsess"
				return ()
			else return ()
		) lpw

data SettingNN = SettingNN 
	{ fileNNForRead :: FilePath
	, fileNNForState :: FilePath
	, fileNNLog :: FilePath
	, fileNNGr :: FilePath
}

initNNS :: SettingNN -> IO ()
initNNS spw = do
	m <- try @SomeException $ decodeFileStrict @(DataNNSLPow PWord) (fileNNForState spw)
	case m of
		(Right (Just _)) -> return ()
		_ -> encodeFile @(DataNNSLPow PWord) (fileNNForState spw) $ 
			DataNNSLPow 
				(DataNN [7,7,7] IMap.empty)
				(DataNN [1,1,1] IMap.empty)
				Map.empty
				IMap.empty
				(ConfNN 
					(0.5,1.5)
					(0.5,1.5)
					10
					2
					3
					2
					2
					)

instance ListDoubled Word8 where
	toLD a = [[fromIntegral a]]
	fromLD (x:[]) _ = round x

startlTNN :: MVar String -> SettingNN -> AdjunctorNN Word8 ()
startlTNN mvs spw = do
	lift $ openHandleWrite $ fileNNLog spw
	(Just dm1) <- liftIO $ decodeFileStrict @(DataNNSLPow Word8) (fileNNForState spw) 
	setDataNNSLPow dm1
	pw <- liftIO $ B.readFile (fileNNForRead spw) 
	lernToNN mvs spw $ bsToPW pw

runNNSccListAdj :: Monad m =>
	M.AdjointT 
		(NNSccListAdjL a) 
		(NNSccListAdjR a)
		m b ->
	m ()
runNNSccListAdj = void .
	runAdjT [] .
	runAdjTfst [] .  
	runAdjTfst G.empty .
	runAdjTfst IMap.empty .
	runAdjT Seq.empty .
	runAdjTfst 0 .
	subAdjSnd

runAdjunctorNN :: AdjunctorNN b c -> IO ()
runAdjunctorNN = void .
	runAdjT Control.Logger.Info .
	runAdjTfst stdout .
	runNNSccListAdj .
	runNNSccListAdj .
	subAdjSnd .
	runAdjTfst Map.empty .
	runAdjTfst IMap.empty .
	runAdjTfst 
		( ConfNN (0,0) (0,0) 0 0 0 0 0) 

runLTNN :: SettingNN -> IO () 
runLTNN snn = do
	mvs <- newEmptyMVar 
	forkIO $ runAdjunctorNN $ 
		startlTNN mvs snn
	str <- P.getLine
	f mvs str
	where
		f mvs str = do
			putMVar mvs str
			str2 <- P.getLine
			f mvs str2
