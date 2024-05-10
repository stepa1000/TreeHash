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
{-# LANGUAGE StarIsType #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE IncoherentInstances #-}

module Data.NN where

import Prelude as P
import Data.List as P
import Data.Foldable as P
import Data.Sequence as Seq 
import System.Random
import Data.Hashable
import Data.HashSet as Set
import Data.HashMap.Lazy as Map
import Data.Map as OMap
import Data.Tree as Tree
import Data.IntMap as IMap
import Data.Maybe
import Data.Either
import Data.Either.Combinators
import Data.Graph.Inductive.PatriciaTree as G
import Data.Graph.Inductive.Graph as G
-- import Data.Graph.Inductive.Monad.IOArray as G
-- import Data.Graph.Inductive.Monad as G
import Data.ByteString as B
import Data.Word
import Data.Aeson as Aeson
import Data.Time.Clock
import Data.Semigroup
import Data.Proxy as P
import Data.Typeable as T
import Data.Type.Equality as T
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
import Control.Monad.Trans.Free -- Control.Monad.Trans.Free.Church
import GHC.Generics
import GHC.TypeNats
import AI.BPANN
import AI.BPANN.Async
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

type Hash = Int

type LNetwork = [Network]

type Layers = [Int]

type AdjNetworkL = (Env LNetwork) :.: (Env Layers)

type AdjNetworkR = (Reader Layers) :.: (Reader LNetwork) 

getNN :: (Monad m, MonadIO m, MonadLoger m) =>
	Hash -> 
	M.AdjointT 
		AdjNetworkL 
		AdjNetworkR
		m
		(Maybe Network)
getNN h = do
	--lift $ logDebugM "Start: getNN"
	ln <- adjFst $ adjGetEnv
	--lift $ logDebugM $ "Length list get NN: " .< (P.length ln) ==
	let mn = P.find (\n-> hash (packNetwork n) == h) ln
	--lift $ logDebugM $ "find NN: " .< (isJust mn)
	--lift $ logDebugM $ "Length list set NN: " .< (P.length ln')
	--lift $ logDebugM "End: getNN"
	return mn

setNN :: (Monad m, MonadIO m, MonadLoger m) =>
	Network -> 
	M.AdjointT 
		AdjNetworkL 
		AdjNetworkR
		m
		()
setNN n = do
	ln <- adjFst $ adjGetEnv
	adjFst $ adjSetEnv (n:ln) (Identity ())

deleteNN :: (Monad m, MonadIO m, MonadLoger m) =>
	Hash -> 
	M.AdjointT 
		AdjNetworkL 
		AdjNetworkR
		m
		(Maybe Network)
deleteNN h = do
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

lnnull :: (Monad m, MonadIO m) => 
	M.AdjointT 
		AdjNetworkL 
		AdjNetworkR
		m
		Bool
lnnull = fmap P.null $ adjFst $ adjGetEnv

type SizeNN = Int

creatRandomNetworksAdj :: (Monad m, MonadIO m) => 
	SizeNN ->
	M.AdjointT 
		AdjNetworkL 
		AdjNetworkR
		m 
		LNetwork
creatRandomNetworksAdj j = do
	l <- adjSnd $ adjGetEnv
	mapM (\x->do
		i <- liftIO $ randomIO
		liftIO $ createRandomNetworkIO i l
		) [0..j]

creatRandomNetworksAdj_ :: (Monad m, MonadIO m, MonadLoger m) => 
	SizeNN ->
	M.AdjointT 
		AdjNetworkL 
		AdjNetworkR
		m 
		()
creatRandomNetworksAdj_ j = do
	--lift $ logDebugM "*** Start: creatRandomNetworksAdj_"
	ln <- creatRandomNetworksAdj j
	{-lift $ logDebugM "Start: Neiron desctiptions"
	mapM_ (\l2-> mapM_ (\l1-> mapM_ (\(n,_)->do
		lift $ logDebugM $ "fun0: " .< ((fun n) 0)
		lift $ logDebugM $ "fun0.5: " .< ((fun n) 0.5)
		lift $ logDebugM $ "fun1: " .< ((fun n) 1)
		lift $ logDebugM $ "w: " .< (ws n)
		) l1) l2) ln-}
	--lift $ logDebugM "End: Neiron desctiptions"
	--lift $ logDebugM "*** End: creatRandomNetworksAdj_"
	-- lnold <- adjFst $ adjGetEnv
	adjFst $ adjSetEnv ln (Identity ())

trainAdj :: (Monad m, MonadIO m,MonadLoger m) => 
	(Double,Double) ->
	(Double,Double) ->
	[([Double], [Double])] ->
	M.AdjointT 
		AdjNetworkL 
		AdjNetworkR
		m 
		()
trainAdj p pe ldd = do
	--lift $ logDebugM "Start: trainAdj"
	i <- liftIO $ randomRIO p
	e <- liftIO $ randomRIO pe
	lnold <- adjFst $ adjGetEnv
	--lift $ logDebugM $ "Length list NN:" .< (P.length lnold)
	ln <- fmap catMaybes $ P.mapM (\n-> liftIO $ trainIO 100000 i e n ldd) lnold
	--lift $ logDebugM $ "Length list result NN:" .< (P.length ln)
	--lift $ logDebugM $ "Input train:" .< ldd
	--lift $ logDebugM "Start: Neiron desctiptions in trainAdj"
	{-mapM_ (\l2-> mapM_ (\l1-> mapM_ (\(n,_)->do
		lift $ logDebugM $ "fun0: " .< ((fun n) 0)
		lift $ logDebugM $ "fun0.5: " .< ((fun n) 0.5)
		lift $ logDebugM $ "fun1: " .< ((fun n) 1)
		lift $ logDebugM $ "w: " .< (ws n)
		) l1) l2) ln-}
	--lift $ logDebugM "End: Neiron desctiptions in trainAdj"
	adjFst $ adjSetEnv ln (Identity ())
	--lift $ logDebugM "End: trainAdj"

trainAdjP :: (Monad m, MonadIO m) => 
	(Double,Double) ->
	(Double,Double) ->
	[[([Double], [Double])]] ->
	M.AdjointT 
		AdjNetworkL 
		AdjNetworkR
		m 
		()
trainAdjP p pe lldd = do
	i <- liftIO $ randomRIO p
	e <- liftIO $ randomRIO pe
	lnold <- adjFst $ adjGetEnv
	ln <- fmap catMaybes $ P.mapM (\n-> P.foldrM (\ ldd mn'-> fmap join $
			mapM (\n'-> liftIO $ trainIO 100000 i e n' ldd) mn'
		) (Just n) lldd
		) lnold
	adjFst $ adjSetEnv ln (Identity ())

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
	--lift $ logDebugM "Start: calculateAdj"
	lnold <- adjFst $ adjGetEnv
	--lift $ logDebugM $ "Length list NN: " .< (P.length lnold)
	--lift $ logDebugM "Start: Neiron desctiptions"
	{-mapM_ (\l2-> mapM_ (\l1-> mapM_ (\(n,_)->do
		lift $ logDebugM $ "fun0: " .< ((fun n) 0)
		lift $ logDebugM $ "fun0.5: " .< ((fun n) 0.5)
		lift $ logDebugM $ "fun1: " .< ((fun n) 1)
		lift $ logDebugM $ "w: " .< (ws n)
		) l1) l2) lnold-}
	--lift $ logDebugM "End: Neiron desctiptions"
	lh <- mapM (fmap hash . liftIO . packNetworkIO) lnold
	lc <- mapM (\n-> liftIO $ calculateIO n ld) lnold
	ll <- adjSnd $ adjGetEnv
	--lift $ logDebugM $ "List layers: " .< ll
	--lift $ logDebugM $ "Input to calculate" .< ld
	--lift $ logDebugM $ "List result calculate: " .< lc
	--lift $ logDebugM "End: calculateAdj"
	return $ P.zip lh lc

class ListDoubled a where
	toLD :: a -> [[Double]]
	fromLD :: [Double] -> a -> a

calculateAdjLD :: 
	(	Monad m, MonadIO m, ListDoubled a,
		MonadLoger m
	) => 
	a ->
	M.AdjointT 
		AdjNetworkL 
		AdjNetworkR
		m
		[(HashNN,a)]
calculateAdjLD a = do
	--lift $ logDebugM "Start:calculateAdjLD"
	llhld <- mapM calculateAdj $ toLD a
	--lift $ logDebugM $ "List hashes: " .< ((fmap . fmap) fst llhld)
	--lift $ logDebugM $ "Length list calculate: " .< (P.length llhld)
	-- lift $ logDebugM $ "Elements calculate:" .< 
	let llhEa = (fmap . fmap) (\(h,ld)->(h,Endo $ fromLD ld)) llhld
	let lha = P.foldr1 f llhEa
	--lift $ logDebugM $ "Length list calculate result: " .< (P.length lha)
	let r = fmap (\(h,ea)->(h,(appEndo ea) a)) lha
	--lift $ logDebugM $ "List hashes: " .< (fmap fst r)
	--lift $ logDebugM $ "Length list endo applayed: " .< (P.length r)
	--lift $ logDebugM "End:calculateAdjLD"
	return r
	where
		f !xl !yl = fmap g $ P.zip xl yl
		g = (\((!hx,!ax),(!hy,!ay))->
			if hx == hy 
				then (hx,ax <> ay) 
				else error "hash not eq"
			)

calculateAdjLDL :: (Monad m, MonadIO m, ListDoubled a, MonadLoger m) => 
	[a] ->
	M.AdjointT 
		AdjNetworkL 
		AdjNetworkR
		m
		[[(HashNN,a)]]
calculateAdjLDL = mapM calculateAdjLD

trainAdjLD :: 
	(	Monad m, MonadIO m, Hashable a, ListDoubled a, Eq a,
		MonadLoger m
	) => 
	(Double,Double) ->
	(Double,Double) ->
	(a, a) ->
	Replicate ->
	M.AdjointT 
		AdjNetworkL 
		AdjNetworkR
		m 
		()
trainAdjLD p pe (x,y) i = do
	mapM_ (trainAdj p pe) $ P.replicate i (P.zip (toLD x) (toLD y))

trainAdjLDL :: 
	(	Monad m, MonadIO m, Hashable a, ListDoubled a, Eq a,
		MonadLoger m
	) => 
	(Double,Double) ->
	(Double,Double) ->
	[(a, a)] ->
	M.AdjointT 
		AdjNetworkL 
		AdjNetworkR
		m 
		()
trainAdjLDL p pe lp = do
	--lift $ logDebugM "Start: trainAdjLDL"
	--lift $ logDebugM $ "Length list data: " .< (P.length lp)
	mapM_ (trainAdj p pe) $ fmap (\(x,y)-> P.zip (toLD x) (toLD y)) lp
	--lift $ logDebugM "End: trainAdjLDL"

type HashNN = Hash

type NNGrAdjL a = (Env (Gr (Hashed a) HashNN)) :.: AdjNetworkL

type NNGrAdjR a = AdjNetworkR :.: (Reader (Gr (Hashed a) HashNN))
  
getSccArtPoint :: (Monad m, MonadIO m, Hashable a, Eq a) => 
	M.AdjointT 
		(NNGrAdjL a) 
		(NNGrAdjR a)
		m 
		[Gr (Hashed a) HashNN]
getSccArtPoint = do
	gr <- adjFst $ adjGetEnv
	return $ sccArtPoint gr

upNNGr :: (Monad m, MonadIO m, Hashable a, ListDoubled a, Eq a, MonadLoger m) => 
	M.AdjointT 
		(NNGrAdjL a) 
		(NNGrAdjR a)
		m 
		()
upNNGr = do
	lift $ logDebugM "Start: upNNGr"
	gr <- adjFst $ adjGetEnv
	lift $ logDebugM "Pre: get graph"
	gct1 <- liftIO getCurrentTime 
	let ln = withStrategy (seqList rseq) $ G.labNodes gr
	lift $ logDebugM $ "Length list node graph: " .< (P.length ln)
	gct2 <- liftIO getCurrentTime 
	lift $ logDebugM $ "diff time on labNodes: " .< (diffUTCTime gct2 gct1)
	rnode <- liftIO $ getRandomElementList ln
	let ma = fmap snd rnode
	mapM_ (\a-> do
		lr <- adjSnd $ calculateAdjLD $ unhashed a
		let lnewNodes = newNodes (P.length lr) gr
		lift $ logDebugM "Post: calculateAdjLD"
		adjFst $ adjSetEnv 
			(withStrategy rseq $ P.foldr 
				(\(nn,(h,a)) b-> id $!
					(maybe id (\(rn,_)-> insEdge (rn,nn,h)) rnode . insNode (nn, hashed a)) b
				) gr $ P.zip lnewNodes lr
			) (Identity ())
		) ma
	lift $ logDebugM "End: upNNGr"

type Replicate = Int

type SerchInt = Int

updatingNNGr :: (Monad m, MonadIO m, Hashable a, Eq a, ListDoubled a, MonadLoger m) => 
	SerchInt ->
	M.AdjointT 
		(NNGrAdjL a) 
		(NNGrAdjR a)
		m 
		()
updatingNNGr si = do
	-- adjSnd $ trainAdjLD p pe pa i
	mapM_ (\i->do
		upNNGr
		lift $ logDebugM $ "Post: upNNGr: index: " .< i
		) [0,1..si]

type UpgradingInt = Int

onlyScc :: (Monad m, MonadIO m, Hashable a, Eq a) => 
	M.AdjointT 
		(NNGrAdjL a) 
		(NNGrAdjR a)
		m 
		()
onlyScc = do
	ln <- adjFst $ fmap join $ getSccGrNode
	gr <- adjFst $ adjGetEnv
	adjFst $ adjSetEnv (subgraph ln gr) (Identity ())

upgradingNNGr :: 
	(	Monad m, MonadIO m, Hashable a, ListDoubled a, Eq a, 
		MonadLoger m
	) => 
	(Double,Double) ->
	(Double,Double) ->
	(a,a) ->
	Replicate ->
	SerchInt ->
	UpgradingInt ->
	M.AdjointT 
		(NNGrAdjL a) 
		(NNGrAdjR a)
		m 
		()
upgradingNNGr d1 d2 pa r si ui = do
	lift $ logInfoM "Start: upgradingNNGr"  -- logDebugM
	adjSnd $ trainAdjLD d1 d2 pa r
	lift $ logInfoM "Post: trainAdjLD"
	gr <- adjFst $ adjGetEnv
	adjFst $ adjSetEnv 
		(P.foldr (\i b->insNode (i,hashed $ snd pa) b) gr $ newNodes 1 gr) (Identity ())
	mapM_ (\i-> do
		onlyScc
		updatingNNGr si
		lift $ logDebugM $ "Post: updatingNNGr: index: " .< i  -- logDebugM
		) [0,1..ui]
	lift $ logInfoM "End: upgradingNNGr"  -- logDebugM

onlyInGr :: (Monad m, MonadIO m, Hashable a, Eq a) => 
	M.AdjointT 
		(NNGrAdjL a) 
		(NNGrAdjR a)
		m 
		()
onlyInGr = do
	gr <- adjFst $ adjGetEnv
	let se = P.fold $ fmap (\(_,_,x)-> Set.singleton x) $ G.labEdges gr
	ln <- adjSnd $ adjFst $ adjGetEnv
	adjSnd $ adjFst $ adjSetEnv 
		(P.filter (\n-> Set.member (hash $ packNetwork n) se) ln) (Identity ())

type HashSccGr = Hash

type IntMapPrimeNN = IntMap ([[PackedNeuron]],[HashSccGr]) -- Prime

type NNPrimeAdjL a = (Env IntMapPrimeNN) :.: (NNGrAdjL a)

type NNPrimeAdjR a = (NNGrAdjR a) :.: (Reader IntMapPrimeNN)

getNNMI :: (Monad m, MonadIO m, MonadLoger m) =>
	Hash -> 
	M.AdjointT 
		(NNPrimeAdjL a) 
		(NNPrimeAdjR a)
		m
		(Maybe ([[PackedNeuron]],[HashSccGr]))
getNNMI h = do
	ln <- adjFst $ adjGetEnv
	return $ IMap.lookup h ln

safeNNScc :: (Monad m, MonadIO m, Hashable a, Eq a) => 
	M.AdjointT 
		(NNPrimeAdjL a) 
		(NNPrimeAdjR a)
		m 
		()
safeNNScc = do
	adjSnd $ onlyScc
	adjSnd $ onlyInGr
	ln <- adjSnd $ adjSnd $ adjFst $ adjGetEnv
	impnn <- fmap P.fold $ mapM (\n->do
		lgr <- adjSnd $ adjFst $ getSccGrGraph
		let pnn = packNetwork n
		return $ IMap.singleton (hash pnn) 
			(pnn,catMaybes $ fmap (\gr-> if or $ fmap (\(_,_,b)->b==(hash pnn)) $ labEdges gr
				then Just $ hash gr
				else Nothing
				) lgr)
		) ln
	im <- adjFst $ adjGetEnv
	adjFst $ adjSetEnv (IMap.union im impnn) (Identity ())

safeCalculate :: 
	(	Monad m, MonadIO m, Hashable a, ListDoubled a, Eq a, 
		MonadLoger m
	) => 
	a ->
	M.AdjointT 
		(NNPrimeAdjL a) 
		(NNPrimeAdjR a)
		m 
		[(HashNN,a)]
safeCalculate a = do
	lpn <- fmap P.fold $ (fmap . fmap) (\(pn,_)-> [unpackNetwork pn]) $ adjFst $ adjGetEnv
	ln <- adjSnd $ adjSnd $ adjFst $ adjGetEnv
	adjSnd $ adjSnd $ adjFst $ adjSetEnv lpn (Identity ())
	lha <- adjSnd $ adjSnd $ calculateAdjLD a
	adjSnd $ adjSnd $ adjFst $ adjSetEnv ln (Identity ())
	return lha

getMapNN :: 
	(	Monad m, MonadIO m, Eq a, ListDoubled a,
		MonadLoger m, Hashable a
	) => 
	(a,a) ->
	M.AdjointT 
		(NNPrimeAdjL a) 
		(NNPrimeAdjR a)
		m 
		(Map Double [[PackedNeuron]])
getMapNN (x,y) = do
	lhy <- fmap (P.filter (\(h,r)->r == y)) $ safeCalculate x
	mlpn <- fmap catMaybes $ mapM (\(h,_)-> (fmap . fmap) fst $ getNNMI h) lhy
	return $ P.fold $ fmap (\pn-> OMap.singleton 
		(sum $ fmap (\pn2-> metric pn pn2) mlpn)
		pn
		) mlpn

getLikeNN :: 
	(	Monad m, MonadIO m, Eq a, ListDoubled a,
		MonadLoger m, Hashable a
	) => 
	M.AdjointT 
		(NNPrimeAdjL a) 
		(NNPrimeAdjR a)
		m 
		(Map Double (HashNN,HashNN))  -- IMap, ListNetwork
getLikeNN = do
	mi <- adjFst adjGetEnv
	ln <- adjSnd $ adjSnd $ adjFst adjGetEnv
	return $ P.fold $ fmap (\(pn,_)-> P.fold $ 
		fmap (\n-> OMap.singleton 
			(metric (packNetwork n) pn) 
			(hash pn, hash (packNetwork n))
			) ln
		) mi

-- MemAdjL ???
type NNSccListAdjL a = (HistoryAdjL [(Gr (Hashed a) HashNN)]) :.: (NNPrimeAdjL a) 

type NNSccListAdjR a = (NNPrimeAdjR a) :.: (HistoryAdjR [(Gr (Hashed a) HashNN)])

class NNSccListAdj f g a where
	liftNNSccListAdj :: (Monad m, Hashable a, Eq a) =>
		M.AdjointT 
			(NNSccListAdjL a) 
			(NNSccListAdjR a)
			m 
			b ->
		M.AdjointT f g m b

adjNNSLliftLN :: Monad m =>
	M.AdjointT 
		(Env LNetwork)
		(Reader LNetwork)
		m
		b -> 
	M.AdjointT 
		(NNSccListAdjL a) 
		(NNSccListAdjR a)
		m
		b
adjNNSLliftLN = adjSnd . adjSnd . adjSnd . adjFst

adjNNSLliftLayers :: Monad m =>
	M.AdjointT 
		(Env Layers)
		(Reader Layers)
		m
		b -> 
	M.AdjointT 
		(NNSccListAdjL a) 
		(NNSccListAdjR a)
		m
		b
adjNNSLliftLayers = adjSnd . adjSnd . adjSnd . adjSnd

adjNNSLliftAdjNetworkL :: Monad m =>
	M.AdjointT 
		AdjNetworkL
		AdjNetworkR
		m
		b -> 
	M.AdjointT 
		(NNSccListAdjL a) 
		(NNSccListAdjR a)
		m
		b
adjNNSLliftAdjNetworkL = adjSnd . adjSnd . adjSnd

adjNNSLliftNNGr :: Monad m =>
	M.AdjointT 
		(Env (Gr (Hashed a) HashNN))
		(Reader (Gr (Hashed a) HashNN))
		m
		b -> 
	M.AdjointT 
		(NNSccListAdjL a) 
		(NNSccListAdjR a)
		m
		b
adjNNSLliftNNGr = adjSnd . adjSnd . adjFst

adjNNSLliftAdjNNGr :: Monad m =>
	M.AdjointT 
		(NNGrAdjL a)
		(NNGrAdjR a)
		m
		b -> 
	M.AdjointT 
		(NNSccListAdjL a) 
		(NNSccListAdjR a)
		m
		b
adjNNSLliftAdjNNGr = adjSnd . adjSnd

adjNNSLliftIntMapPrimeNN :: Monad m =>
	M.AdjointT 
		(Env IntMapPrimeNN)
		(Reader IntMapPrimeNN)
		m
		b -> 
	M.AdjointT 
		(NNSccListAdjL a) 
		(NNSccListAdjR a)
		m
		b
adjNNSLliftIntMapPrimeNN = adjSnd . adjFst

adjNNSLliftAdjNNPrime :: Monad m =>
	M.AdjointT 
		(NNPrimeAdjL a)
		(NNPrimeAdjR a)
		m
		b -> 
	M.AdjointT 
		(NNSccListAdjL a) 
		(NNSccListAdjR a)
		m
		b
adjNNSLliftAdjNNPrime = adjSnd

adjNNSLliftHAG :: Monad m =>
	M.AdjointT 
		(HistoryAdjL [(Gr (Hashed a) HashNN)])
		(HistoryAdjR [(Gr (Hashed a) HashNN)])
		m
		b -> 
	M.AdjointT 
		(NNSccListAdjL a) 
		(NNSccListAdjR a)
		m
		b
adjNNSLliftHAG = adjFst

addToHSccList :: (Monad m, MonadIO m, Hashable a, Eq a, Hashable (Gr (Hashed a) HashNN)) => 
	[HashScc] ->
	M.AdjointT 
		(NNSccListAdjL a) 
		(NNSccListAdjR a)
		m 
		()
addToHSccList lh = do
	(lscc :: [Gr (Hashed a) HashNN]) <- adjNNSLliftAdjNNGr getSccArtPoint
	adjNNSLliftHAG $ addToLHistoryLeft $ P.filter (\scc-> P.elem (hash $ scc) lh) lscc
	return ()

newtype ShortDL a = ShortDL a deriving ()

unShortDL (ShortDL a) = a

pointSDL (x,y) = (ShortDL x, ShortDL y)

unPointSDL (x,y) = (unShortDL x, unShortDL y)

type SizeNNShort = Int

type SizeNNRePrime = Int

type HashScc = Hash

restorationNNSccLPrimer :: 
	(	Monad m, MonadIO m, Hashable a, ListDoubled a,Eq a,
		MonadLoger m
	) => 
	(Double,Double) ->
	(Double,Double) ->
	(a, a) ->
	M.AdjointT 
		(NNSccListAdjL a) 
		(NNSccListAdjR a)
		m 
		[(Gr (Hashed a) HashNN,Network)]
restorationNNSccLPrimer p pe pa = do
	--lift $ logDebugM "Start: restorationNNSccLPrimer"
	--mlgr <- adjFst $ viewHistoryLeft
	lgr <- adjNNSLliftAdjNNGr getSccArtPoint
	--let lgr = join $ maybeToList mlgr
	mgr <- liftIO $ getRandomElementList lgr
	rp <- fmap (join . maybeToList) $ mapM randomPath mgr
	let plrp = pairing $ fmap unhashed rp
	--lift $ logDebugM "Pre: trainAdjLDL"
	adjNNSLliftAdjNetworkL $ trainAdjLDL p pe plrp
	(lr :: [(HashNN,a)]) <- adjNNSLliftAdjNetworkL $ calculateAdjLD $ fst pa
	--lift $ logDebugM $ "Length pre result: " .< (P.length lr)
	nl <- adjNNSLliftLayers adjGetEnv
	--lift $ logDebugM $ "Layers NN: " .< nl
	let fl = P.filter (\(h,a)-> a == (snd pa)) lr
	--lift $ logDebugM $ "Length result: " .< (P.length fl)
	rnnslp <- fmap catMaybes $ mapM (\x-> do 
		(mn :: Maybe Network) <- adjNNSLliftAdjNetworkL $ getNN $ fst x
		return $ do
			gr <- mgr
			n <- mn
			return (gr,n)
		) fl
	--lift $ logDebugM "End: restorationNNSccLPrimer"
	return rnnslp

type RestorationCycle = Int 

restorationNNSccLPrimerUp' :: 
	(Monad m, MonadIO m, Hashable a, ListDoubled a, Eq a, MonadLoger m, Show a) => 
	(Double,Double) ->
	(Double,Double) ->
	(a,a) ->
	RestorationCycle ->
	SizeNN ->
	Replicate ->
	SerchInt ->
	UpgradingInt ->
	M.AdjointT 
		(NNSccListAdjL a) 
		(NNSccListAdjR a)
		m 
		(IntMap ([[PackedNeuron]],[Gr (Hashed a) HashNN]))
restorationNNSccLPrimerUp' p pe pa rc snn r si ui = do
	lift $ logInfoM "Start: restorationNNSccLPrimerUp'"
	hnn <- fmap unionScc
		$ mapM (\_-> do
		(b :: Bool) <- adjNNSLliftAdjNetworkL lnnull
		lift $ logInfoM "Pre: restorationNNSccLPrimer"
		lhscchnn <- restorationNNSccLPrimer p pe pa
		lift $ logInfoM "Post: restorationNNSccLPrimer"  -- logDebugM
		when (b || (P.null lhscchnn)) $ do
			adjNNSLliftAdjNetworkL $ creatRandomNetworksAdj_ snn
			adjNNSLliftNNGr $ adjSetEnv G.empty (Identity ())
			lift $ logInfoM "Pre: upgradingNNGr"
			adjNNSLliftAdjNNGr $ upgradingNNGr p pe pa r si ui
		hnn' <- fmap unionScc $ mapM (\(hscc,hnn)->do
			let n = packNetwork hnn
			return (IMap.singleton (hash $ n) (n,[hscc]))
			) lhscchnn
		lift $ logInfoM $ "Result cyckle:" .< (IMap.size hnn')
		return hnn'
		) [0..rc]
	--lift $ logInfoM "Pre: onlyInGr'"
	adjNNSLliftAdjNNGr $ onlyInGr
	lift $ logInfoM "End: restorationNNSccLPrimerUp'"
	return $ hnn

unionScc = P.foldr (IMap.unionWith (\(x1,y1) (_,y2)->(x1,y1++y2))) IMap.empty

restorationNNSccLPrimerUpSafe :: 
	(Monad m, MonadIO m, MonadLoger m, Hashable a, ListDoubled a, Eq a) => 
	(IntMap ([[PackedNeuron]],[Gr (Hashed a) HashNN])) ->
	M.AdjointT 
		(NNSccListAdjL a) 
		(NNSccListAdjR a)
		m 
		()
restorationNNSccLPrimerUpSafe impngr = do
	lift $ logInfoM "Start: restorationNNSccLPrimerUpSafe"
	sequenceA_ $ IMap.mapWithKey (\knn (pn,hscc)->do
		im <- adjSnd $ adjFst $ adjGetEnv
		let im' = IMap.insertWith (\(x1,y1) (_,y2)->(x1,y1++y2)) knn (pn,[hash hscc]) im
		adjSnd $ adjFst $ adjSetEnv im' (Identity ())
		return [hash hscc]
		) impngr
	lgr <- fmap (fmap snd . IMap.toList . P.fold) $ mapM (\(pn,gr)->do
		return $ IMap.singleton (hash gr) gr
		) impngr
	lift $ logInfoM $ "!!! Length list scc:" .< (P.length lgr)
	adjFst $ addToLHistoryLeft $ join lgr
	adjSnd $ adjSnd $ adjFst $ adjSetEnv G.empty (Identity ())
	lift $ logInfoM "End: restorationNNSccLPrimerUpSafe"

type PowGr a = Gr a [[PackedNeuron]]

toPowGr :: (Monad m, MonadIO m, Hashable a, ListDoubled a, Eq a, MonadLoger m) => 
	Gr (Hashed a) HashNN ->
	M.AdjointT 
		(NNSccListAdjL a) 
		(NNSccListAdjR a)
		m 
		(PowGr a)
toPowGr gr = do
	ufold (\(adjL,i,a,adjR) mg->do
		g <- mg
		adjL' <- mapM (\(mb,j)->do
			b <- mb
			return (maybe [] id b,j)
			) adjL
		adjR' <- mapM (\(mb,j)->do
			b <- mb
			return (maybe [] id b,j)
			) adjR
		return $ G.insert (adjL',i,a,adjR') g
		) (return G.empty) $ 
		nemap unhashed (\h->do
			nn <- adjNNSLliftAdjNetworkL $ getNN h
			return $ fmap packNetwork nn
		) gr

type NNSLPowAdjL f a = (NNSccListAdjL (PowGr a)) :.: f -- (NNSccListAdjL a) 

type NNSLPowAdjR g a = g :.: (NNSccListAdjR (PowGr a)) -- (NNSccListAdjR a)

instance ListDoubled [[PackedNeuron]] where
	toLD a = join $ fmap 
			(\(x,l)-> 
				fmap (\(y,ld)-> join $
					fmap (\(z,d)-> 
						((fromIntegral x):
						((fromIntegral y):
						((fromIntegral z):
						[d])))) $ P.zip [0..] ld) {-[[Double]]-} l) -- [[[Double]]]
		$ P.zip [0..] $ fmap (P.zip [0..]) a
	fromLD (x:y:z:(dl::[Double])) a = toxy (round x) (round y) (round z) a
		where 
			toxy :: Int -> Int -> Int -> [[PackedNeuron]] -> [[PackedNeuron]] -- [[[Double]]]
			toxy x y z l
				| x > 0 && not (P.null l) = (P.head l) : (toxy (x-1) y z (P.tail l))
				| x > 0 && P.null l = [] : (toxy (x-1) y z l)
				| x == 0 && not (P.null l) = (toy y z (P.head l)) : (P.tail l)
				| x == 0 && P.null l = [toy y z []]
			toy :: Int -> Int -> [PackedNeuron] -> [PackedNeuron] -- [[Double]]
			toy y z l 
				| y > 0 && not (P.null l) = (P.head l) : (toy (y - 1) z (P.tail l)) 
				| y > 0 && P.null l = [] : (toy (y-1) z l)
				| y == 0 && not (P.null l) = (toz z (P.head l)) : (P.tail l)
				| y == 0 && P.null l = [toz z []]
			toz :: Int -> PackedNeuron -> PackedNeuron -- [Double]
			toz z l 
				| z > 0 && not (P.null l) = (P.head l) : (toz (z - 1) (P.tail l)) 
				| z > 0 && P.null l = 0 : (toz (z-1) l)
				| z == 0 && not (P.null l) = dl ++ (P.tail l)
				| z == 0 && P.null l = dl

instance ListDoubled a => ListDoubled (PowGr a) where
	-- toLD :: a -> [[Double]]
	toLD a = ufold 
		(\(adjL,i,v,adjR) c-> 
			(fmap (\ld-> 0:((fromIntegral i):(0:(addLengthV v ld)))) $ toLD v) ++
			(fmap (\(ld,n)-> 1:
				((fromIntegral i):
				((fromIntegral n):
				(addLengthPN v ld)))) $ join $ fmap (\(lld,n)->fmap (\x->(x,n)) lld) $ 
					P.zip (fmap (toLD . fst) adjL) (fmap snd adjL)) ++
			(fmap (\(ld,n)-> 2:
				((fromIntegral i):
				((fromIntegral n):
				(addLengthPN v ld)))) $ join $ fmap (\(lld,n)->fmap (\x->(x,n)) lld) $ 
					P.zip (fmap (toLD . fst) adjR) (fmap snd adjR)) ++
			c 
			) [] a
		where
			addLengthPN :: a -> [Double] -> [Double]
			addLengthPN v lpn
				| (lle v) > 4 = lpn ++ (P.replicate ((lle v) - 4) 0)
			addLengthPN _ lpn = lpn
			addLengthV :: a -> [Double] -> [Double]
			addLengthV v l 
				| (lle v) < 4 = l ++ (P.replicate (4 - (lle v)) 0)
			addLengthV _ l = l
			lle v = P.foldr1 (\x y-> 
				if x == y 
					then x 
					else error "ListDoubled a not eq"
				) $ fmap P.length $ toLD v
	-- fromLD :: [Double] -> a -> a
	fromLD (i:di:dj:ld) gr = case i of 
			0 -> maybe gr id $
				fmap (\(ladj,i,a,radj)-> G.insert (ladj,i,fromLD ld a,radj) gr') mc
			1 -> maybe gr id $
				fmap (\(ladj,i,a,radj)-> G.insert (f (round dj) ladj,i,a,radj) gr') mc
			2 -> maybe gr id $
				fmap (\(ladj,i,a,radj)-> G.insert (ladj,i,a,f (round dj) radj) gr') mc
			_ -> gr
		where
			f j l = (maybeToList $ fmap (\(x,y)-> (fromLD ld x,y)) md) ++ l'
				where
					md = listToMaybe $ P.filter (\(d,i)->i == j) l
					l' = P.filter (\(d,i)->i /= j) l
			(mc,gr') = match (round di) gr
	fromLD _ gr = gr

class ClassNNSLPowAdj f g a where
	liftNNSccListAdjGr :: (Monad m) =>
		M.AdjointT 
			(NNSccListAdjL (PowGr a))
			(NNSccListAdjR (PowGr a))
			m 
			b ->
		M.AdjointT f g m b
	liftNNSccListAdjA :: (Monad m) =>
		M.AdjointT 
			(NNSccListAdjL a) 
			(NNSccListAdjR a)
			m 
			b ->
		M.AdjointT f g m b

-- forse
restorationPow :: 
	(	Monad m, MonadIO m, Hashable a, ListDoubled a,Eq a,
		ClassNNSLPowAdj f g a, Adjunction f g, Traversable f,
		MonadLoger m, Show a
	) => 
	(Double,Double) ->
	(Double,Double) ->
	a ->
	RestorationCycle ->
	SizeNN ->
	Replicate ->
	SerchInt ->
	UpgradingInt ->
	M.AdjointT f g m ()
restorationPow p pe (ta :: a) rc snn r si ui = do
	lift $ logDebugM "Start: restorationPow"
	(mplhl :: Maybe ([(Gr (Hashed a) HashNN)],[(Gr (Hashed a) HashNN)])) <- 
		liftNNSccListAdjA $ adjNNSLliftHAG $ adjSnd viewHPairLeft -- viewHistoryLeft
	s <- liftNNSccListAdjA @_ @_ @a $ adjNNSLliftHAG $ adjSnd adjGetEnv 
	lift $ logDebugM $ "Seq list length scc:" .< (fmap P.length s)
	--mlhgr <- liftNNSccListAdjGr $ adjNNSLliftHAG $ viewHistoryLeft
	mapM_ (\((xl::[(Gr (Hashed a) HashNN)]),(yl::[(Gr (Hashed a) HashNN)]))-> do
		let lp = join $ fmap (\y->fmap (\x->(x,y)) xl) yl
		(limpngr :: [IntMap ([[PackedNeuron]],[Gr (Hashed (PowGr a)) HashNN])]) <- 
			mapM (\(x,y)->do 
				x' <- liftNNSccListAdjA $ toPowGr x
				y' <- liftNNSccListAdjA $ toPowGr y
				let plgr = (x',y')
				liftNNSccListAdjGr $ restorationNNSccLPrimerUp' p pe plgr rc snn r si ui -- ???
			) lp
		impngr <- if not (P.null limpngr) 
			then return $ P.toList $ unionScc limpngr
			else return [([],[])]
		im <- fmap ((\(x,y,t)->(x,y)) . P.foldr1 (\(x1,y1,t1) (x2,y2,t2)-> 
				if t1 < t2
					then (x1,y1,t1)
					else (x2,y2,t2)
				)) $
			mapM (\(pn,lgr)->do
			sm <- fmap P.sum $ mapM (\(pn2,lgr2)->do
				return $ metric pn pn2
				) impngr 
			return (pn,lgr,sm)
			) impngr
		let rl = P.filter (\x-> IMap.member (hash $ fst im) x) limpngr
		lift $ logDebugM $ "List result restorationPow: " .< (P.length rl)
		mr <- liftIO $ getRandomElementList rl
		mapM_ (\r-> do
			{-r' <- mapM (\(x,yl)->do
				yl' <- mapM (\y->do
					liftNNSccListAdjA $ toPowGr y
					) yl
				return (x,yl')
				) r-}
			liftNNSccListAdjGr @_ @_ @a $ restorationNNSccLPrimerUpSafe r
			) mr
		) mplhl
	lift $ logDebugM "End: restorationPow"

restorationPowUp :: 
	(	Monad m, MonadIO m, Hashable a, ListDoubled a,Eq a,
		ClassNNSLPowAdj f g a, Adjunction f g, Traversable f,
		MonadLoger m, Show a
	) => 
	(Double,Double) ->
	(Double,Double) ->
	(a,a) ->
	RestorationCycle ->
	SizeNN ->
	Replicate ->
	SerchInt ->
	UpgradingInt ->
	M.AdjointT f g m ()
restorationPowUp p pe pa rc snn r si ui = do
	lift $ logInfoM "Start: restorationPowUp"
	lr <- liftNNSccListAdjA $ 
		restorationNNSccLPrimerUp' p pe pa rc snn r si ui
	liftNNSccListAdjA $ restorationNNSccLPrimerUpSafe lr
	lift $ logInfoM "Post: restorationNNSccLPrimerUp'"
	restorationPow p pe (fst pa) rc snn r si ui
	lift $ logInfoM "End: restorationPowUp"

type HashNNGr = HashNN

-- force
assumption' :: 
	(	Monad m, MonadIO m, Hashable a, ListDoubled a,Eq a,
		ClassNNSLPowAdj f g a, Adjunction f g, MonadLoger m
	) =>
	a ->
	M.AdjointT f g m 
		[(HashNNGr,PowGr a,PowGr a)] -- (Gr (Hashed a) HashNN))
		-- just Gr (Hashed a) ()
assumption' (ta :: a) = do
	-- lmgr <- liftNNSccListAdjGr $ adjNNSLliftHAG $ viewHistoryLeft -- liftNNSccListAdjGr $ 
	(lmgr :: Maybe [(Gr (Hashed a) HashNN)]) <- 
		liftNNSccListAdjA $ adjNNSLliftHAG $ adjSnd viewHistoryLeft
	fmap (join . maybeToList . fmap join) $ mapM (\lgr->do
		mapM (\gr->do
			gr' <- liftNNSccListAdjA $ toPowGr gr
			(hgr :: [(HashNN,PowGr a)]) <- 
				liftNNSccListAdjGr $ adjNNSLliftAdjNNPrime $ safeCalculate gr'
			return $ fmap (\(h,g)-> (h,gr',g)) hgr
			) lgr
		) lmgr -- (join $ fmap topsort' lmgr)

assumptionRestoration :: 
	(	Monad m, MonadIO m, Hashable a, ListDoubled a,Eq a,
		MonadLoger m
	) =>
	(Double,Double) ->
	(Double,Double) ->
	a ->
	[(HashNNGr,PowGr a,PowGr a)] ->
	M.AdjointT 
		(NNSccListAdjL a) 
		(NNSccListAdjR a)
		-- (NNSLPowAdjL f a) 
		-- (NNSLPowAdjR g a)
		m 
		[(PowGr a,PowGr a,HashNNGr,HashNN,a)] -- !!!
assumptionRestoration p pe a lhgr = do
	-- like restorationNNSccLPrimer
	(mrhgr :: Maybe (HashNNGr,PowGr a,PowGr a)) <- liftIO $ getRandomElementList lhgr
	fmap (join . maybeToList) $ mapM (\(rh, grr, gr)->do
		rp <- liftIO $ randomPath gr
		let plrp = pairing rp 
		adjNNSLliftAdjNetworkL $ trainAdjLDL p pe plrp
		ha <- adjNNSLliftAdjNetworkL $ calculateAdjLD a
		return $ fmap (\(h,x)->(grr,gr,rh,h,x)) ha
		) mrhgr

type SizeAssumptionRestoration = Int

assumptionRestorationUp :: 
	(	Monad m, MonadIO m, Hashable a, ListDoubled a,Eq a,
		NNSccListAdj f g a, Adjunction f g, ClassNNSLPowAdj f g a,
		MonadLoger m
	) =>
	(Double,Double) ->
	(Double,Double) ->
	a ->
	SizeNN ->
	Replicate ->
	SerchInt ->
	UpgradingInt ->
	SizeAssumptionRestoration -> 
	[(HashNNGr,PowGr a,PowGr a)] ->
	M.AdjointT f g m 
		(HashMap a ([(PowGr a,PowGr a, HashNNGr,[[[PackedNeuron]]])]))
assumptionRestorationUp p pe (a :: a) snn r si ui sar lhgr = do
	-- like restorationNNSccLPrimerUp'
	liftNNSccListAdjA  @_ @_ @a $ adjNNSLliftAdjNetworkL $ creatRandomNetworksAdj_ snn
	fmap f $ mapM (\_->do
		b <- liftNNSccListAdjA @_ @_ @a $ adjNNSLliftAdjNetworkL $ lnnull
		-- lhgr <- assumption'
		lhscchnn <- liftNNSccListAdjA @_ @_ @a $ assumptionRestoration p pe a lhgr
		when (b || (P.null lhscchnn)) $ do -- evretime False
			liftNNSccListAdjA @_ @_ @a $ adjNNSLliftAdjNetworkL $ creatRandomNetworksAdj_ snn
			-- liftNNSccListAdjA $ adjNNSLliftNNGr $ adjSetEnv G.empty (Identity ()) -- ???
			-- liftNNSccListAdjA $ adjNNSLliftNNGr $ upgradingNNGr p pe pa r si ui -- ??? 
			-- because assumption
		fmap f $ mapM (\(gr1,gr2,hgr,hnn,x)->do
			nn <- liftNNSccListAdjA  @_ @_ @a $ adjNNSLliftAdjNetworkL $ getNN hgr
			let n = fmap packNetwork nn
			return (Map.singleton x ([(gr1,gr2,hgr,maybeToList n)]))
			) lhscchnn
		) [0..sar]
	where
		f = P.foldr (Map.unionWith (\l1 l2-> l1 ++ l2
			)) Map.empty
		-- foldr (Map.unionWith (\(x1) (x2)->(x1++x2,y1++y2))) Map.empty

resultAssumptionTrue :: Eq a =>
	a ->
	HashMap a ([(PowGr a,PowGr a, HashNNGr,[[[PackedNeuron]]])]) ->
	HashMap a ([(PowGr a,PowGr a, HashNNGr,[[[PackedNeuron]]])])
resultAssumptionTrue a hm = Map.filterWithKey (\k _ -> k == a) hm

type ReasonGr a = PowGr a

type ConsequenceGr a = PowGr a

type MapGr a = HashMap (ReasonGr a) [(ConsequenceGr a,HashNNGr)] -- HashA ?

type MapGrAdjL f a = (Env (MapGr a)) :.: f -- (NNSccListAdjL a) 

type MapGrAdjR g a = g :.: (Reader (MapGr a)) -- (NNSccListAdjR a)

type HashSccR = HashScc -- ReasonGr a

type HashSccC = HashScc -- ConsequenceGr a

class ClassMapGrAdj f g a where
	liftMapGrAdj :: (Monad m, Hashable a, Eq a) =>
		M.AdjointT  (Env (MapGr a)) (Reader (MapGr a)) m b ->
		M.AdjointT f g m b

safeTrueAssumptuon :: 
	(	Monad m, MonadIO m, Hashable a, ListDoubled a,Eq a,
		NNSccListAdj f g a, ClassMapGrAdj f g a, MonadLoger m,
		Adjunction f g, Traversable f, ClassNNSLPowAdj f g a,
		Show a
	) =>
	a ->
	HashMap a ([(PowGr a,PowGr a, HashNNGr,[[[PackedNeuron]]])]) ->
	M.AdjointT f g m (IntMap [(HashSccR,HashSccC)])
safeTrueAssumptuon (ta :: a) hma = do
	lift $ logInfoM "Start: safeTrueAssumptuon"
	lift $ logInfoM $ "Length list assumptions: " .< (Map.size hma)
	--lift $ logInfoM $ "true value: " .< ta
	let thma = resultAssumptionTrue ta hma
	hm <- fmap (f . fmap snd . Map.toList) $ mapM (\l-> do
		--lift $ logInfoM "safe assumptions"
		fmap f $ mapM (\ (gr1, gr2, nngr, lpn) -> do
			mgr <- liftMapGrAdj $ adjGetEnv
			let mgr' = Map.insertWith (++) gr1 [(gr2,hash nngr)] mgr
			liftMapGrAdj $ adjSetEnv mgr' (Identity ())
			mapM_ (\pn->do
				im <- liftNNSccListAdjA  @_ @_ @a $ adjNNSLliftIntMapPrimeNN $ adjGetEnv
				let im' = IMap.insertWith (\(x1,y1) (_,y2)->(x1,y1++y2)) (hash pn) (pn,[hash gr2]) im
				liftNNSccListAdjA  @_ @_ @a $ adjNNSLliftIntMapPrimeNN $ adjSetEnv im' (Identity ())
				) lpn
			return $ IMap.singleton (hash nngr) [(hash gr1, hash gr2)]
			) l
		) thma
	lift $ logInfoM "End: safeTrueAssumptuon"
	return hm
	where
		f = P.foldr (IMap.unionWith (\y1 y2->y1++y2)) IMap.empty

memoriAssumption :: 
	(	Monad m, MonadIO m, Hashable a, ListDoubled a,Eq a,
		ClassNNSLPowAdj f g a, ClassMapGrAdj f g a, Adjunction f g,
		MonadLoger m
	) => 
	M.AdjointT f g m [(ConsequenceGr a,HashNNGr)]
memoriAssumption = do
	lmgr <- liftNNSccListAdjA $ adjNNSLliftHAG $ adjSnd viewHistoryLeft
	mgr <- liftMapGrAdj $ adjGetEnv
	fmap (join . maybeToList) $ mapM (\lgr->do
		fmap (join . catMaybes) $ mapM (\gr->do
			gr' <- liftNNSccListAdjA $ toPowGr gr
			return $ Map.lookup gr' mgr
			) lgr
		) lmgr

type IMapNNRC = IntMap [(HashSccR,HashSccC)]

type IMapNNRCAdjL f = (Env IMapNNRC) :.: f -- (NNSccListAdjL a) 

type IMapNNRCAdjR g = g :.: (Reader IMapNNRC) -- (NNSccListAdjR a)

safeTrueAssumptuonNNRC :: 
	(	Monad m, MonadIO m
		-- NNSccListAdj f g a
	) =>
	IntMap [(HashSccR,HashSccC)] ->
	M.AdjointT (Env IMapNNRC) (Reader IMapNNRC) m ()
safeTrueAssumptuonNNRC imnnrc = do
	imrc <- adjGetEnv
	let imrc' = IMap.unionWith (++) imrc imnnrc
	adjSetEnv imrc' (Identity ())

class ClassIMapNNRAdj f g where
	liftIMapNNRAdj :: (Monad m) =>
		M.AdjointT (Env IMapNNRC) (Reader IMapNNRC) m b ->
		M.AdjointT f g m b

safeTrueAssumptuonFull :: 
	(	Monad m, MonadIO m, Hashable a, ListDoubled a,Eq a,
		ClassNNSLPowAdj f g a, ClassMapGrAdj f g a, ClassIMapNNRAdj f g,
		MonadLoger m, Adjunction f g, NNSccListAdj f g a, Traversable f,
		Show a
	) => 
	a ->
	HashMap a ([(PowGr a,PowGr a, HashNNGr,[[[PackedNeuron]]])]) ->
	M.AdjointT f g m ()
safeTrueAssumptuonFull ta hma = do
	--lift $ logInfoM "Start: safeTrueAssumptuonFull"
	o <- safeTrueAssumptuon ta hma
	liftIMapNNRAdj $ safeTrueAssumptuonNNRC o
	--lift $ logInfoM "End: safeTrueAssumptuonFull"

type AllResult a = 
	HashMap a ([(PowGr a,PowGr a, HashNNGr,[[[PackedNeuron]]])])

type ConsequenceResult a = 
	HashMap a ([(PowGr a,PowGr a, HashNNGr,[[[PackedNeuron]]])])

updateAssumptionPre :: 
	(	Monad m, MonadIO m, Hashable a, ListDoubled a,Eq a,
		ClassNNSLPowAdj f g a, ClassMapGrAdj f g a, ClassIMapNNRAdj f g,
		MonadLoger m, Adjunction f g, NNSccListAdj f g a, Traversable f
	) => 
	(Double,Double) ->
	(Double,Double) ->
	a ->
	SizeNN ->
	Replicate ->
	SerchInt ->
	UpgradingInt ->
	SizeAssumptionRestoration -> 
	M.AdjointT f g m 
		( AllResult a
		, ConsequenceResult a
		)
updateAssumptionPre p pe a snn r si ui sar = do
	lift $ logInfoM "Start: updateAssumptionPre"
	lhngr <- assumption' a
	(hmagr :: HashMap a ([(PowGr a,PowGr a, HashNNGr,[[[PackedNeuron]]])])) <- 
		assumptionRestorationUp p pe a snn r si ui sar lhngr
	lc <- memoriAssumption
	lift $ logInfoM $ "Assumption size: " .< (P.length lhngr)
	lift $ logInfoM "End: updateAssumptionPre"
	return 
		( hmagr
		, Map.filter 
			(\lgr-> or $ 
				fmap (\(grr,grc,_,pn)-> isJust $ P.lookup grc lc) lgr
			) 
			hmagr
		)

updateAssumptionPost :: 
	(	Monad m, MonadIO m, Hashable a, ListDoubled a,Eq a,
		ClassNNSLPowAdj f g a, ClassMapGrAdj f g a, ClassIMapNNRAdj f g,
		MonadLoger m, Adjunction f g, Traversable f, NNSccListAdj f g a,
		Show a
	) => 
	(Double,Double) ->
	(Double,Double) ->
	(a,a) ->
	SizeNN ->
	Replicate ->
	SerchInt ->
	UpgradingInt ->
	SizeAssumptionRestoration -> 
	( AllResult a
	, ConsequenceResult a
	) ->
	M.AdjointT f g m ()
updateAssumptionPost p pe pa snn r si ui sar pr = do
	lift $ logInfoM "Start: updateAssumptionPost"
	safeTrueAssumptuonFull (snd pa) (fst pr)
	lift $ logInfoM "Post: safeTrueAssumptuonFull"
	restorationPowUp p pe pa sar snn r si ui 
	lift $ logInfoM "End: updateAssumptionPost"

type Recion0AdjL a =
	IMapNNRCAdjL 
		(MapGrAdjL 
			( NNSLPowAdjL 
				( NNSccListAdjL a
				) 
				a
			) 
			a)

type Recion0AdjR a =
	IMapNNRCAdjR
		(MapGrAdjR
			( NNSLPowAdjR 
				( NNSccListAdjR a
				) 
				a
			) 
			a)

{-
newtype Recion0AdjL a = Recion0AdjL
	(IMapNNRCAdjL 
		(MapGrAdjL 
			( NNSLPowAdjL 
				( NNSccListAdjL a
				) 
				a
			) 
			a)) deriving

newtype Recion0AdjR a = Recion0AdjR
	(IMapNNRCAdjR
		(MapGrAdjR
			( NNSLPowAdjR 
				( NNSccListAdjR a
				) 
				a
			) 
			a)) deriving
-}

type RecionNAdjL f a = 
	IMapNNRCAdjL 
		(MapGrAdjL 
			( NNSLPowAdjL 
				f
				a -- n + 1 :: PowGr a
			) 
			a) -- n + 1 :: PowGr a

type RecionNAdjR g a = 
	IMapNNRCAdjR
		(MapGrAdjR
			( NNSLPowAdjR 
				g
				a
			) 
			a)

type family RecoinPowGr (b :: Bool) (n :: Nat) a

type instance RecoinPowGr True n a = a

type instance RecoinPowGr False n a = PowGr (RecoinPowGr (n <=? 0) (n - 1) a)

type family FRecionAdjL (b :: Bool) (n :: Nat) a :: * -> *

type family FRecionAdjR (b :: Bool) (n :: Nat) a :: * -> *

type instance FRecionAdjL True n a = Recion0AdjL (RecoinPowGr (n <=? 0) n a)

type instance FRecionAdjL False n a = 
	RecionNAdjL 
		(FRecionAdjL 
			((n - 1) <=? 0) 
			(n - 1) 
			a
		)
		(RecoinPowGr 
			((n + 1) <=? 0) 
			n 
			a)

type instance FRecionAdjR True n a = Recion0AdjR a

type instance FRecionAdjR False n a = 
	RecionNAdjR 
		(FRecionAdjR 
			((n - 1) <=? 0) 
			(n - 1) 
			a) 
		(RecoinPowGr 
			((n + 1) <=? 0) 
			n 
			a)

type RecoinPowGrT1 n a = 
	(RecoinPowGr 
		((n + 1) <=? 0) 
		n 
		a)

type FRecionAdjRT1 n a = 
	(FRecionAdjR 
		(n <=? 0) 
		n 
		a)

type FRecionAdjLT1 n a = 
	(FRecionAdjL
		(n <=? 0) 
		n
		a)

liftRecion :: 
	(	Monad m, KnownNat n,
		Adjunction (FRecionAdjL (n <=? 0) n a) (FRecionAdjR (n <=? 0) n a), 
		Adjunction (FRecionAdjL ((n + 1) <=? 0) (n + 1) a) (FRecionAdjR ((n + 1) <=? 0) (n + 1) a),
		(FRecionAdjRT1 (n + 1) a) ~ 
			RecionNAdjR 
				(FRecionAdjR (n <=? 0) 
					n
					a) 
				(RecoinPowGr 
					((n + 1 + 1) <=? 0) 
					(n + 1) 
					a),
		(FRecionAdjLT1 (n + 1) a) ~ 
			RecionNAdjL 
				(FRecionAdjL (n <=? 0) 
					n 
					a) 
				(RecoinPowGr 
					(((n + 1) + 1) <=? 0) 
					(n + 1) 
					a)
	) => 
	Proxy a ->
	SNat n ->
	M.AdjointT 
		(FRecionAdjLT1 n a) 
		(FRecionAdjRT1 n a)
		m b ->
	M.AdjointT 
		(FRecionAdjLT1 (n + 1) a) 
		(FRecionAdjRT1 (n + 1) a)
		m b
liftRecion (pa :: Proxy a) (sn :: SNat n) (m :: M.AdjointT (FRecionAdjLT1 n a) (FRecionAdjRT1 n a) m b)
	= do
	(return () :: M.AdjointT 
		(FRecionAdjLT1 (n + 1) a) 
		(FRecionAdjRT1 (n + 1) a)
		m ())
	adjSnd $ adjSnd $ adjSnd m 

-- instance ClassIMapNNRAdj (FRecionAdjL b n a) (FRecionAdjR b n a) where
instance Adjunction f g => ClassIMapNNRAdj (RecionNAdjL f a) (RecionNAdjR g a) where
	liftIMapNNRAdj = adjFst
		{-:: (Monad m) =>
		M.AdjointT (Env IMapNNRC) (Reader IMapNNRC) m b ->
		M.AdjointT f g m b-}
instance ClassIMapNNRAdj (Recion0AdjL a) (Recion0AdjR a) where
	liftIMapNNRAdj = adjFst

instance Adjunction f g => ClassMapGrAdj (RecionNAdjL f a) (RecionNAdjR g a) a where
	liftMapGrAdj = adjSnd . adjFst

instance ClassMapGrAdj (Recion0AdjL a) (Recion0AdjR a) a where
	liftMapGrAdj = adjSnd . adjFst

instance (ClassNNSLPowAdj f g a, Adjunction f g) => 
	ClassNNSLPowAdj (RecionNAdjL f (PowGr a)) (RecionNAdjR g (PowGr a)) (PowGr a) where
	liftNNSccListAdjGr = adjSnd . adjSnd . adjFst
	liftNNSccListAdjA = adjSnd . adjSnd . adjSnd . liftNNSccListAdjGr

instance ClassNNSLPowAdj (Recion0AdjL a) (Recion0AdjR a) a where
	liftNNSccListAdjGr = adjSnd . adjSnd . adjFst
	liftNNSccListAdjA = adjSnd . adjSnd . adjSnd

instance (ClassNNSLPowAdj f g a, Adjunction f g) => 
	NNSccListAdj (RecionNAdjL f (PowGr a)) (RecionNAdjR g (PowGr a)) (PowGr a) where
	liftNNSccListAdj = liftNNSccListAdjA -- ???

type NAllResult n a = 
	HashMap 
		(RecoinPowGrT1 n a) 
		(	[(RecoinPowGrT1 (n + 1) a,
			RecoinPowGrT1 (n + 1) a, 
			HashNNGr,[[[PackedNeuron]]])
		])

type NConsequenceResult n a = 
	HashMap 
		(RecoinPowGrT1 n a) 
		(	[(RecoinPowGrT1 (n + 1) a,
			RecoinPowGrT1 (n + 1) a, 
			HashNNGr,[[[PackedNeuron]]])
		])

type family ListNRC (b :: Bool) (n :: Nat) a

type instance ListNRC True n a = (NAllResult n a, NConsequenceResult n a)

type instance ListNRC False n a = 
	(	NAllResult n a, 
		NConsequenceResult n a, 
		ListNRC ((n - 1) <=? 0) (n - 1) a)

type ListNRCT n a = ListNRC (n <=? 0) n a

type family ListMInputGr (b :: Bool) (n :: Nat) a

type instance ListMInputGr True n a = (RecoinPowGrT1 n a)

type instance ListMInputGr False n a = (Maybe (RecoinPowGrT1 n a), ListMInputGr ((n - 1) <=? 0) (n - 1) a)

type ListMInputGrT n a = ListMInputGr (n <=? 0) n a
{-}
type family FunUpdateRecoinPre (b :: Bool) (n :: Nat) m a where
	FunUpdateRecoinPre False 0 m a = InputUpdateRecoinPre 0 a -> 
		M.AdjointT 
			(FRecionAdjLT1 0 a) 
			(FRecionAdjRT1 0 a)
			m (ListNRCT 0 a)
	FunUpdateRecoinPre True n m a =
		InputUpdateRecoinPre n a -> 
			M.AdjointT 
			(FRecionAdjLT1 n a) 
			(FRecionAdjRT1 n a)
			m (ListNRCT n a)
-}
{-}	InputUpdateRecoinPre n a -> 
	(ListNRCT n a -> c) -> 
	FInputUpdateRecoinPre n a c
-}
{-}	InputUpdateRecoinPre n a -> 
	M.AdjointT 
		(FRecionAdjLT1 n a) 
		(FRecionAdjRT1 n a)
		m (ListNRCT n a)
-}
-- type instance FunUpdateRecoinPre True 0 a = FunFIURPN0 -- FInputUpdateRecoinPre 0 a (ListNRCT 0 a)
{-\ iurp -> updateRecoinPre'2
	pa (SNat @0) 
	(alfaIURP iurp) 
	(errorIURP iurp) 
	((listLMIGT iurp) :: a) 
	(sizeNN iurp) 
	(replicateIURP iurp) 
	(searchIntIURP iurp) 
	(upgradingIntIURP iurp) 
	(sarIURP iurp)
-}
--type instance FunUpdateRecoinPre False n a = FunFIURPN
{-\ iurp -> do
	liftRecion $ (FunUpdateRecoinPre ((n - 1) <=? 0) (n - 1) a)
	updateRecoinPre'1
-}

type FunIURP n m a = InputUpdateRecoinPre n a -> 
			M.AdjointT 
			(FRecionAdjLT1 n a) 
			(FRecionAdjRT1 n a)
			m (ListNRCT n a)

nextFunIURP :: (ListMInputGrT (n + 1) a ~ 
	(Maybe (RecoinPowGrT1 (n + 1) a), ListMInputGr (n <=? 0) n a),
	KnownNat n,
	Adjunction (FRecionAdjL (n <=? 0) n a) (FRecionAdjR (n <=? 0) n a), 
	Adjunction (FRecionAdjL ((n + 1) <=? 0) (n + 1) a) (FRecionAdjR ((n + 1) <=? 0) (n + 1) a),
	(FRecionAdjRT1 (n + 1) a) ~ 
		RecionNAdjR 
			(FRecionAdjR (n <=? 0) 
				n
				a) 
			(RecoinPowGr 
				(((n + 1) + 1) <=? 0) 
				(n + 1) 
				a),
	(FRecionAdjLT1 (n + 1) a) ~ 
		RecionNAdjL 
			(FRecionAdjL (n <=? 0) 
				n 
				a) 
			(RecoinPowGr 
				(((n + 1) + 1) <=? 0) 
				(n + 1) 
				a),
	ListNRCT (n + 1) a ~ (NAllResult (n + 1) a, 
		NConsequenceResult (n+1) a, 
		ListNRC (n <=? 0) n a), -- RecoinPowGr False n a = PowGr (RecoinPowGr (n <=? 0) (n - 1) a)
	RecoinPowGrT1 ((n + 1) + 1) a ~ PowGr (RecoinPowGr (((n + 1) + 1) <=? 0) (n + 1) a),
	RecoinPowGr (((n + 1) + 1) <=? 0) (n + 1) a ~ PowGr (RecoinPowGr ((n + 1) <=? 0) n a),
	MonadIO m, Monad m, Hashable (RecoinPowGrT1 ((n + 1) + 1) a), Hashable (RecoinPowGrT1 n a),
	ListDoubled (RecoinPowGrT1 n a), 
	ClassNNSLPowAdj (FRecionAdjLT1 n a) (FRecionAdjRT1 n a) (RecoinPowGrT1 n a),
	MonadLoger m, NNSccListAdj (FRecionAdjLT1 n a) (FRecionAdjRT1 n a) (RecoinPowGrT1 n a),
	Traversable (FRecionAdjLT1 n a)
	-- PowGr (PowGr (RecoinPowGr ((n + 1) <=? 0) (n + 1) a))
	)
	=>
	FunIURP n m a -> 
	FunIURP (n + 1) m a
nextFunIURP (f :: FunIURP n m a) iurp = do
	(return () :: M.AdjointT 
		(FRecionAdjLT1 (n + 1) a) 
		(FRecionAdjRT1 (n + 1) a)
		m ())
	(lnect :: ListNRCT n a) <- liftRecion (proxyIURP iurp) (SNat @n) $ f (nextIURP iurp)
	mxy <- mapM (\gra->updateAssumptionPre 
		(alfaIURP iurp)
		(errorIURP iurp)
		gra
		(sizeNN iurp)
		(replicateIURP iurp)
		(searchIntIURP iurp)
		(upgradingIntIURP iurp)
		(sarIURP iurp)) (fst $ (listLMIGT iurp :: ListMInputGrT (n + 1) a)) 
	return @_ @(ListNRCT (n + 1) a) $ maybe (Map.empty, Map.empty, lnect) (\(x,y)->(x,y,lnect)) mxy

data InputUpdateRecoinPre n a = InputUpdateRecoinPre
	{
	proxyIURP :: Proxy a,
	snatIURP :: SNat n ,
	alfaIURP :: (Double,Double),
	errorIURP :: (Double,Double),
	listLMIGT :: ListMInputGrT n a,
	sizeNN :: SizeNN ,
	replicateIURP :: Replicate,
	searchIntIURP :: SerchInt,
	upgradingIntIURP :: UpgradingInt,
	sarIURP :: SizeAssumptionRestoration}

nextIURP :: (ListMInputGrT (n + 1) a ~ 
	(Maybe (RecoinPowGrT1 (n + 1) a), ListMInputGr (n <=? 0) n a),
	KnownNat n)
	=> InputUpdateRecoinPre (n + 1) a -> InputUpdateRecoinPre n a
nextIURP (iurp :: InputUpdateRecoinPre (n + 1) a) = InputUpdateRecoinPre
	(proxyIURP iurp)
	(SNat @n)
	(alfaIURP iurp)
	(errorIURP iurp)
	((\(_,x)->x) $ (listLMIGT iurp :: ListMInputGrT (n + 1) a))
	(sizeNN iurp)
	(replicateIURP iurp)
	(searchIntIURP iurp)
	(upgradingIntIURP iurp)
	(sarIURP iurp)

data FInputUpdateRecoinPre (n :: Nat) a b where
	LiftFIURP :: FInputUpdateRecoinPre n a b -> FInputUpdateRecoinPre (n + 1) a b
	FunFIURPN0 :: InputUpdateRecoinPre 0 a -> (ListNRCT 0 a -> b) -> FInputUpdateRecoinPre 0 a b
	HeadListMInputGrT :: 
		ListMInputGrT (n + 1) a -> 
		((Maybe (RecoinPowGrT1 n a), ListMInputGr (n <=? 0) n a) -> b) ->
		FInputUpdateRecoinPre n a b
	{-FunFIURPN :: 
		InputUpdateRecoinPre n a -> 
		(ListNRCT n a -> b) -> 
		FInputUpdateRecoinPre n a b-}
{-}
instance Functor (FInputUpdateRecoinPre n a) where
	fmap f (LiftFIURP g) = LiftFIURP $ fmap f g
	fmap f (FunFIURPN0 i g) = FunFIURPN0 i $ (f . g)
	--fmap f (FunFIURPN i g) = FunFIURPN i $ (f . g)
-}
-- type FreeIURP n a = Free (FInputUpdateRecoinPre n a)
{-}
runFIURP ::	
	(	Monad m, KnownNat n, Typeable n
	) =>
	Proxy a ->
	SNat n ->
	FreeIURP n a b -> 
	M.AdjointT 
		(FRecionAdjLT1 n a) 
		(FRecionAdjRT1 n a)
		m
		b
runFIURP (pa :: Proxy a) (sn :: SNat n) = hoistMAdj (\(Identity x)->return x) $ iterTM (f sn)
	where
		f (snn :: SNat n2) (LiftFIURP fiurp) = liftRecion $ f (SNat @(n2 - 1)) fiurp
		f (snn :: SNat 0) (FunFIURPN0 iurp g) = 
			fmap g $ updateRecoinPre'2 pa (SNat @0) 
				(alfaIURP iurp) 
				(errorIURP iurp) 
				((listLMIGT iurp) :: a) 
				(sizeNN iurp) 
				(replicateIURP iurp) 
				(searchIntIURP iurp) 
				(upgradingIntIURP iurp) 
				(sarIURP iurp)
		f (snn :: SNat (n2 + 1)) (FunFIURPN iurp g) = 
			fmap g $ do
				mxy <- mapM (\gra->updateAssumptionPre 
					(alfaIURP iurp) 
					(errorIURP iurp) 
					gra 
					(sizeNN iurp) 
					(replicateIURP iurp) 
					(searchIntIURP iurp) 
					(upgradingIntIURP iurp) 
					(sarIURP iurp) ) $ (\(x,_,_)->x) (listLMIGT iurp :: ListMInputGrT (n2 + 1) a) 
				return $ maybe (Map.empty, Map.empty) (\(x,y)->(x,y)) mxy
				{- updateRecoinPre'1 pa (SNat @n2) 
				(alfaIURP iurp) 
				(errorIURP iurp) 
				((listLMIGT iurp) :: ListMInputGrT n2 a) 
				(sizeNN iurp) 
				(replicateIURP iurp) 
				(searchIntIURP iurp) 
				(upgradingIntIURP iurp) 
				(sarIURP iurp) -}
-}
{-}
updateRecoinPre'1 :: 
	(	Monad m, KnownNat n, Typeable n{-,  (n <=? 0) ~ False,
		Adjunction (FRecionAdjL (n <=? 0) n a) (FRecionAdjR (n <=? 0) n a),
		NAllResult 0 a ~ AllResult a, NConsequenceResult 0 a ~ ConsequenceResult a,
		ListNRCT 0 a ~ (NAllResult 0 a, NConsequenceResult 0 a),
		ListMInputGrT 0 a ~ a-}
	) =>
	Proxy a ->
	SNat n ->
	(Double,Double) ->
	(Double,Double) ->
	ListMInputGrT (n+1) a ->
	SizeNN ->
	Replicate ->
	SerchInt ->
	UpgradingInt ->
	SizeAssumptionRestoration -> 
	M.AdjointT 
		(FRecionAdjLT1 (n+1) a) 
		(FRecionAdjRT1 (n+1) a)
		m 
		(NAllResult (n+1) a, NConsequenceResult (n+1) a)
updateRecoinPre'1 (pa :: Proxy a) (sn :: SNat n) p pe ((mgra,l) :: ListMInputGrT (n + 1) a) snn r si ui sar
	| fromSNat (SNat @(n + 1)) > 0 = do
		(return () :: M.AdjointT 
			(FRecionAdjLT1 (n + 1) a) 
			(FRecionAdjRT1 (n + 1) a)
			m ())
		{-lnrct <- fromJust $ (do
			n0 <- leftToMaybe $ decT @(SNat (n - 1)) @(SNat 0)
			return $ liftRecion pa (SNat @(n - 1)) $ 
				updateRecoinPre'1 pa (SNat @(n - 1)) p pe l snn r si ui sar) <|>
			(do
			n0 <- eqT @(SNat (n - 1)) @(SNat 0)
			return $ liftRecion pa (SNat @0) $ 
				updateRecoinPre'2 pa (SNat @0) p pe l snn r si ui sar
			)-}
		mxy <- mapM (\gra->updateAssumptionPre p pe gra snn r si ui sar) mgra 
		return $ maybe (Map.empty, Map.empty) (\(x,y)->(x,y)) mxy
-}
updateRecoinPre'2 ::
	(	Monad m, KnownNat 0, Typeable 0, MonadIO m, Hashable a,
		Adjunction (FRecionAdjL (0 <=? 0) 0 a) (FRecionAdjR (0 <=? 0) 0 a),
		NAllResult 0 a ~ AllResult a, NConsequenceResult 0 a ~ ConsequenceResult a,
		ListNRCT 0 a ~ (NAllResult 0 a, NConsequenceResult 0 a),
		ListMInputGrT 0 a ~ a, Typeable a, ListDoubled a, MonadLoger m,
		NNSccListAdj (Recion0AdjL a) (Recion0AdjR a) a
	) =>
	Proxy a ->
	SNat 0 ->
	(Double,Double) ->
	(Double,Double) ->
	ListMInputGrT 0 a ->
	SizeNN ->
	Replicate ->
	SerchInt ->
	UpgradingInt ->
	SizeAssumptionRestoration -> 
	M.AdjointT 
		(FRecionAdjLT1 0 a) 
		(FRecionAdjRT1 0 a)
		m 
		(ListNRCT 0 a)
updateRecoinPre'2 (pa :: Proxy a) (sn :: SNat 0) p pe (a :: ListMInputGrT 0 a) snn r si ui sar
	| 	fromSNat sn == 0 && 
		(isJust $ eqT @(SNat 0) @(SNat 0)) &&
		(isJust $ eqT @(ListMInputGrT 0 a) @(ListMInputGrT 0 a)) -- &&
		--(isLeft $ decT @a @(Maybe _,ListMInputGrT (0-1) a))
		= do
		{-(return () :: Monad m =>
			(	M.AdjointT (FRecionAdjLT1 0 a) (FRecionAdjRT1 0 a) m () ~
				M.AdjointT (FRecionAdjLT1 0 a) (FRecionAdjRT1 0 a) m ()
				) 
			=> M.AdjointT 
				(FRecionAdjLT1 0 a) 
				(FRecionAdjRT1 0 a)
				m ())-}
		let n0 = fromJust $ eqT @(SNat 0) @(SNat 0)
		(r :: (AllResult a, ConsequenceResult a)) <- 
			updateAssumptionPre p pe a snn r si ui sar
		return @_ @(ListNRCT 0 a) r
{-}			((gcastWith @_ @(SNat n) @(SNat 0) @(AllResult a, ConsequenceResult a) :: 
				((SNat n) :~: (SNat 0)) -> ((SNat n) ~ (SNat 0) => (AllResult a, ConsequenceResult a))) 
				n0 
				r )-}

type ReturnTLR n a = (	n ~ 0,
				a ~ ListMInputGrT 0 a,
				ListNRCT 0 a ~
				(NAllResult 0 a, NConsequenceResult 0 a),
				(NAllResult 0 a, NConsequenceResult 0 a) ~ 
				(AllResult a, ConsequenceResult a) 
				)

data ConfNN = ConfNN 
	{ confLRA :: (Double,Double)
	, confMEE :: (Double,Double)
	, confSNN :: SizeNN
	, confReplication :: Replicate
	, confSerchInt :: SerchInt
	, confUpgradingInt :: UpgradingInt
	, confSAR :: SizeAssumptionRestoration
} deriving (Generic, ToJSON, FromJSON)

type ConfNNAdjL f = (Env ConfNN) :.: f -- (NNSccListAdjL a) 

type ConfNNAdjR g = g :.: (Reader ConfNN) -- (NNSccListAdjR a)

class ClassConfNNAdj f g where
	liftConfNNAdj :: (Monad m) =>
		M.AdjointT (Env ConfNN) (Reader ConfNN) m b ->
		M.AdjointT f g m b

getConfNN :: (Monad m, ClassConfNNAdj f g) =>
	M.AdjointT f g m ConfNN
getConfNN = liftConfNNAdj $ adjGetEnv

setConfNN :: (Monad m, ClassConfNNAdj f g) =>
	ConfNN ->
	M.AdjointT f g m ()
setConfNN dm = do
	liftConfNNAdj $ adjSetEnv dm (Identity ())

updateAPre :: 
	(	Monad m, MonadIO m, Hashable a, ListDoubled a,Eq a,
		ClassNNSLPowAdj f g a, ClassMapGrAdj f g a, ClassIMapNNRAdj f g,
		MonadLoger m, Adjunction f g, ClassConfNNAdj f g, NNSccListAdj f g a,
		Traversable f
	) =>
	a -> 
	M.AdjointT f g m 
		( AllResult a
		, ConsequenceResult a
		)
updateAPre a = do
	cnn <- getConfNN
	updateAssumptionPre 
		(confLRA cnn)
		(confMEE cnn)
		a
		(confSNN cnn)
		(confReplication cnn)
		(confSerchInt cnn)
		(confUpgradingInt cnn)
		(confSAR cnn)

updateAPost :: 
	(	Monad m, MonadIO m, Hashable a, ListDoubled a,Eq a,
		ClassNNSLPowAdj f g a, ClassMapGrAdj f g a, ClassIMapNNRAdj f g,
		MonadLoger m, Adjunction f g, ClassConfNNAdj f g, Traversable f,
		NNSccListAdj f g a, Show a
	) =>
	(a,a) -> 
	( AllResult a
	, ConsequenceResult a
	) ->
	M.AdjointT f g m ()
updateAPost pa pr = do
	cnn <- getConfNN
	updateAssumptionPost 
		(confLRA cnn)
		(confMEE cnn)
		pa
		(confSNN cnn)
		(confReplication cnn)
		(confSerchInt cnn)
		(confUpgradingInt cnn)
		(confSAR cnn)
		pr


data DataNN = DataNN
	{ nnLayers :: Layers
	, nnMap :: IntMapPrimeNN
	, nnHistoryLength :: Int
} deriving (Generic, ToJSON, FromJSON)

getDataNN :: (Monad m, Hashable a, Eq a) =>
	M.AdjointT 
		(NNSccListAdjL a) 
		(NNSccListAdjR a)
		m 
		DataNN
getDataNN = do 
	l <- adjNNSLliftLayers $ adjGetEnv
	im <- adjNNSLliftIntMapPrimeNN $ adjGetEnv
	hl <- adjFst $ adjFst adjGetEnv
	return $ DataNN l im hl

setDataNN :: (Monad m, Hashable a, Eq a) =>
	DataNN ->
	M.AdjointT 
		(NNSccListAdjL a) 
		(NNSccListAdjR a)
		m 
		()
setDataNN dm = do
	adjNNSLliftLayers $ adjSetEnv (nnLayers dm) (Identity ())
	adjNNSLliftIntMapPrimeNN $ adjSetEnv (nnMap dm) (Identity ())
	adjFst $ adjFst $ adjSetEnv (nnHistoryLength dm) (Identity ())

instance (ToJSON a, ToJSON b) => ToJSONKey (Gr a b)
instance (FromJSON a, FromJSON b) => FromJSONKey (Gr a b)

instance (Ord b, Hashable b, Eq a, Hashable a) => Hashable (Gr a b)

data DataNNSLPow a = DataNNSLPow
	{ dnnGr :: DataNN
	, dnnA :: DataNN
	, hmrcgr :: MapGr a
	, imrcnn :: IMapNNRC
	, nnslpConf :: ConfNN
} deriving (Generic, ToJSON, FromJSON)

unionDNNSLP :: Eq a => DataNNSLPow a -> DataNNSLPow a -> DataNNSLPow a
unionDNNSLP d1 d2 = DataNNSLPow
	( DataNN 
		(nnLayers $ dnnGr d1)
		(IMap.unionWith (\(x,lx) (y,ly)->(x,lx++ly)) 
			(nnMap $ dnnGr d1) (nnMap $ dnnGr d2))
		(nnHistoryLength $ dnnGr d1)
	)
	( DataNN 
		(nnLayers $ dnnA d1)
		(IMap.unionWith (\(x,lx) (y,ly)->(x,lx++ly)) 
			(nnMap $ dnnA d1) (nnMap $ dnnA d2))
		(nnHistoryLength $ dnnA d1)
	)
	( Map.unionWith (\lx ly->lx++ly) (hmrcgr d1) (hmrcgr d2)
	)
	(IMap.unionWith (\lx ly->lx++ly) 
			(imrcnn d1) (imrcnn d2)
	)
	(nnslpConf d1)

getDataNNSLPow :: 
	(	Monad m, MonadIO m, Hashable a, ListDoubled a,Eq a,
		ClassNNSLPowAdj f g a, ClassMapGrAdj f g a, ClassIMapNNRAdj f g,
		Adjunction f g, ClassConfNNAdj f g
	) => 
	a ->
	M.AdjointT f g m (DataNNSLPow a)
getDataNNSLPow (a::a) = do 
	dnngr <- liftNNSccListAdjGr  @_ @_ @a $ getDataNN
	dnna <- liftNNSccListAdjA  @_ @_ @a $ getDataNN
	mgr <- liftMapGrAdj $ adjGetEnv
	im <- liftIMapNNRAdj $ adjGetEnv
	c <- liftConfNNAdj $ adjGetEnv
	return $ DataNNSLPow dnngr dnna mgr im c

setDataNNSLPow :: 
	(	Monad m, MonadIO m, Hashable a, ListDoubled a,Eq a,
		ClassNNSLPowAdj f g a, ClassMapGrAdj f g a, ClassIMapNNRAdj f g,
		Adjunction f g, ClassConfNNAdj f g
	) => 
	DataNNSLPow a ->
	M.AdjointT f g m ()
setDataNNSLPow (dm :: DataNNSLPow a) = do
	liftNNSccListAdjGr @_ @_ @a $ setDataNN (dnnGr dm)
	liftNNSccListAdjA @_ @_ @a $ setDataNN (dnnA dm)
	liftMapGrAdj $ adjSetEnv (hmrcgr dm) (Identity ())
	liftIMapNNRAdj $ adjSetEnv (imrcnn dm) (Identity ())
	liftConfNNAdj $ adjSetEnv (nnslpConf dm) (Identity ())