{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Data.NN where

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
import Data.Adj.Graph

type Hash = Int

type LNetwork = [Network]

type Layers = [Int]

type AdjNetworkL = (Env LNetwork) :.: (Env Layers)

type AdjNetworkR = (Reader Layers) :.: (Reader LNetwork) 

getNN :: (Monad m, MonadIO m) =>
	Hash -> 
	M.AdjointT 
		AdjNetworkL 
		AdjNetworkR
		m
		(Maybe Network)
getNN h = do
	ln <- adjFst $ adjGetEnv
	let mn = P.find (\n-> hash (packNetwork n) == h) ln
	let ln' = P.filter (\n-> not $ hash (packNetwork n) == h) ln
	adjFst $ adjSetEnv ln' (Identity ())
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
		return $ createRandomNetwork i l
		) [0..j]

creatRandomNetworksAdj_ :: (Monad m, MonadIO m) => 
	Int ->
	M.AdjointT 
		AdjNetworkL 
		AdjNetworkR
		m 
		()
creatRandomNetworksAdj_ j = do
	ln <- creatRandomNetworksAdj j
	lnold <- adjFst $ adjGetEnv
	adjFst $ adjSetEnv (ln ++ lnold) (Identity ())

trainAdj :: (Monad m, MonadIO m) => 
	(Double,Double) ->
	(Double,Double) ->
	[([Double], [Double])] ->
	M.AdjointT 
		AdjNetworkL 
		AdjNetworkR
		m 
		()
trainAdj p pe ldd = do
	i <- liftIO $ randomRIO p
	e <- liftIO $ randomRIO pe
	lnold <- adjFst $ adjGetEnv
	let ln = P.map (\n-> train i e n ldd) lnold
	adjFst $ adjSetEnv ln (Identity ())


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
	let ln = P.map (\n-> P.foldr (\ ldd n'-> train i e n' ldd) n lldd) lnold
	adjFst $ adjSetEnv ln (Identity ())

calculateAdj :: (Monad m, MonadIO m) => 
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
	return $ P.zip lh lc

class ListDoubled a where
	toLD :: a -> [[Double]]
	fromLD :: [Double] -> a -> a

calculateAdjLD :: (Monad m, MonadIO m, ListDoubled a) => 
	a ->
	M.AdjointT 
		AdjNetworkL 
		AdjNetworkR
		m
		[(HashNN,a)]
calculateAdjLD a = do
	llhld <- mapM calculateAdj $ toLD a
	let llhEa = (fmap . fmap) (\(h,ld)->(h,Endo $ fromLD ld)) llhld
	let lha = P.foldr1 f llhEa
	return $ fmap (\(h,ea)->(h,(appEndo ea) a)) lha
	where
		f xl yl = fmap g $ P.zip xl yl
		g = (\((hx,ax),(hy,ay))->
			if hx == hy 
				then (hx,ax <> ay) 
				else error "hash not eq"
			)

calculateAdjLDL :: (Monad m, MonadIO m, ListDoubled a) => 
	[a] ->
	M.AdjointT 
		AdjNetworkL 
		AdjNetworkR
		m
		[[(HashNN,a)]]
calculateAdjLDL = mapM calculateAdjLD

trainAdjLD :: (Monad m, MonadIO m, Hashable a, ListDoubled a, Eq a) => 
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

trainAdjLDL :: (Monad m, MonadIO m, Hashable a, ListDoubled a, Eq a) => 
	(Double,Double) ->
	(Double,Double) ->
	[(a, a)] ->
	M.AdjointT 
		AdjNetworkL 
		AdjNetworkR
		m 
		()
trainAdjLDL p pe lp = do
	mapM_ (trainAdj p pe) $ fmap (\(x,y)-> P.zip (toLD x) (toLD y)) lp

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

upNNGr :: (Monad m, MonadIO m, Hashable a, ListDoubled a, Eq a) => 
	M.AdjointT 
		(NNGrAdjL a) 
		(NNGrAdjR a)
		m 
		()
upNNGr = do
	gr <- adjFst $ adjGetEnv
	let ln = G.labNodes gr
	rnode <- liftIO $ getRandomElementList ln
	let ma = fmap snd rnode
	mapM_ (\a-> do
		lr <- adjSnd $ calculateAdjLD $ unhashed a
		let lnewNodes = newNodes (P.length lr) gr
		adjFst $ adjSetEnv 
			(P.foldr 
				(\(nn,(h,a)) b-> 
					(maybe id (\(rn,_)-> insEdge (rn,nn,h)) rnode . insNode (nn, hashed a)) b
				) gr $ P.zip lnewNodes lr
			) (Identity ())
		) ma

type Replicate = Int

type SerchInt = Int

updatingNNGr :: (Monad m, MonadIO m, Hashable a, Eq a, ListDoubled a) => 
	SerchInt ->
	M.AdjointT 
		(NNGrAdjL a) 
		(NNGrAdjR a)
		m 
		()
updatingNNGr si = do
	-- adjSnd $ trainAdjLD p pe pa i
	mapM_ (\_->upNNGr) [0..si]

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

upgradingNNGr :: (Monad m, MonadIO m, Hashable a, ListDoubled a, Eq a) => 
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
	adjSnd $ trainAdjLD d1 d2 pa r
	gr <- adjFst $ adjGetEnv
	adjFst $ adjSetEnv 
		(P.foldr (\i b->insNode (i,hashed $ snd pa) b) gr $ newNodes 1 gr) (Identity ())
	mapM_ (\_-> do
		onlyScc
		updatingNNGr si
		) [0..ui]

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

safeCalculate :: (Monad m, MonadIO m, Hashable a, ListDoubled a, Eq a) => 
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

restorationNNSccLPrimer :: (Monad m, MonadIO m, Hashable a, ListDoubled a,Eq a) => 
	(Double,Double) ->
	(Double,Double) ->
	(a, a) ->
	M.AdjointT 
		(NNSccListAdjL a) 
		(NNSccListAdjR a)
		m 
		[(Gr (Hashed a) HashNN,Network)]
restorationNNSccLPrimer p pe pa = do
	--mlgr <- adjFst $ viewHistoryLeft
	lgr <- adjNNSLliftAdjNNGr getSccArtPoint
	--let lgr = join $ maybeToList mlgr
	mgr <- liftIO $ getRandomElementList lgr
	rp <- fmap (join . maybeToList) $ mapM randomPath mgr
	let plrp = pairing $ fmap unhashed rp
	adjNNSLliftAdjNetworkL $ trainAdjLDL p pe plrp
	(lr :: [(HashNN,a)]) <- adjNNSLliftAdjNetworkL $ calculateAdjLD $ fst pa
	let fl = P.filter (\(h,a)->a == (snd pa)) lr
	fmap catMaybes $ mapM (\x-> do 
		(mn :: Maybe Network) <- adjNNSLliftAdjNetworkL $ getNN $ fst x
		return $ do
			gr <- mgr
			n <- mn
			return (gr,n)
		) fl

type RestorationCycle = Int 

restorationNNSccLPrimerUp' :: (Monad m, MonadIO m, Hashable a, ListDoubled a, Eq a) => 
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
	hnn <- fmap unionScc
		$ mapM (\_-> do
		(b :: Bool) <- adjNNSLliftAdjNetworkL lnnull
		lhscchnn <- restorationNNSccLPrimer p pe pa
		when (b || (P.null lhscchnn)) $ do
			adjNNSLliftAdjNetworkL $ creatRandomNetworksAdj_ snn
			adjNNSLliftNNGr $ adjSetEnv G.empty (Identity ())
			adjNNSLliftAdjNNGr $ upgradingNNGr p pe pa r si ui
		fmap unionScc $ mapM (\(hscc,hnn)->do
			let n = packNetwork hnn
			return (IMap.singleton (hash $ n) (n,[hscc]))
			) lhscchnn
		) [0..rc]
	adjNNSLliftAdjNNGr $ onlyInGr
	return $ hnn

unionScc = P.foldr (IMap.unionWith (\(x1,y1) (_,y2)->(x1,y1++y2))) IMap.empty

restorationNNSccLPrimerUpSafe :: (Monad m, MonadIO m, Hashable a, ListDoubled a, Eq a) => 
	(IntMap ([[PackedNeuron]],[Gr (Hashed a) HashNN])) ->
	M.AdjointT 
		(NNSccListAdjL a) 
		(NNSccListAdjR a)
		m 
		()
restorationNNSccLPrimerUpSafe impngr = do
	sequenceA_ $ IMap.mapWithKey (\knn (pn,hscc)->do
		im <- adjSnd $ adjFst $ adjGetEnv
		let im' = IMap.insertWith (\(x1,y1) (_,y2)->(x1,y1++y2)) knn (pn,[hash hscc]) im
		adjSnd $ adjFst $ adjSetEnv im' (Identity ())
		return [hash hscc]
		) impngr
	lgr <- fmap (fmap snd . IMap.toList . P.fold) $ mapM (\(pn,gr)->do
		return $ IMap.singleton (hash gr) gr
		) impngr
	adjFst $ addToLHistoryLeft $ join lgr
	adjSnd $ adjSnd $ adjFst $ adjSetEnv G.empty (Identity ())

type PowGr a = Gr a [[PackedNeuron]]

toPowGr :: (Monad m, MonadIO m, Hashable a, ListDoubled a, Eq a) => 
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
		where
			f j l = (maybeToList $ fmap (\(x,y)-> (fromLD ld x,y)) md) ++ l'
				where
					md = listToMaybe $ P.filter (\(d,i)->i == j) l
					l' = P.filter (\(d,i)->i /= j) l
			(mc,gr') = match (round di) gr

class ClassNNSLPowAdj f g a where
	liftNNSccListAdjGr :: (Monad m, Hashable a, Eq a) =>
		M.AdjointT 
			(NNSccListAdjL (PowGr a))
			(NNSccListAdjR (PowGr a))
			m 
			b ->
		M.AdjointT f g m b
	liftNNSccListAdjA :: (Monad m, Hashable a, Eq a) =>
		M.AdjointT 
			(NNSccListAdjL a) 
			(NNSccListAdjR a)
			m 
			b ->
		M.AdjointT f g m b

-- forse
restorationPow :: 
	(	Monad m, MonadIO m, Hashable a, ListDoubled a,Eq a,
		ClassNNSLPowAdj f g a, Adjunction f g, Traversable f
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
	(mplhl :: Maybe ([(Gr (Hashed a) HashNN)],[(Gr (Hashed a) HashNN)])) <- 
		liftNNSccListAdjA $ adjNNSLliftHAG $ adjSnd viewHPairLeft -- viewHistoryLeft
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

restorationPowUp :: 
	(	Monad m, MonadIO m, Hashable a, ListDoubled a,Eq a,
		ClassNNSLPowAdj f g a, Adjunction f g, Traversable f
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
	liftNNSccListAdjA $ 
		restorationNNSccLPrimerUp' p pe pa rc snn r si ui
	restorationPow p pe (fst pa) rc snn r si ui

type HashNNGr = HashNN

-- force
assumption' :: 
	(	Monad m, MonadIO m, Hashable a, ListDoubled a,Eq a,
		ClassNNSLPowAdj f g a, Adjunction f g
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
	(	Monad m, MonadIO m, Hashable a, ListDoubled a,Eq a
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
		NNSccListAdj f g a, Adjunction f g, ClassNNSLPowAdj f g a
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

type HashSccR = HashScc

type HashSccC = HashScc

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
	lift $ logInfoM $ "true value: " .< ta
	let thma = resultAssumptionTrue ta hma
	hm <- fmap (f . fmap snd . Map.toList) $ mapM (\l-> do
		lift $ logInfoM "safe assumptions"
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
		ClassNNSLPowAdj f g a, ClassMapGrAdj f g a, Adjunction f g
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
	o <- safeTrueAssumptuon ta hma
	liftIMapNNRAdj $ safeTrueAssumptuonNNRC o

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
	safeTrueAssumptuonFull (snd pa) (fst pr)
	restorationPowUp p pe pa sar snn r si ui 

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
	return $ DataNN l im

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