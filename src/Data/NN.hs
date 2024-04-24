{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Data.NN where

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
	let mn = P.finde (\n-> hash (packNetwork n) == h) ln
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
		LNetwork
creatRandomNetworksAdj_ j = do
	ln <- creatRandomNetworksAdj j
	lnold <- adjFst $ adjGetEnv
	adjFst $ adjSetEnv (ln ++ lnold) (Identity ())

trainAdj :: (Monad m, MonadIO m, Hashable a, Eq a) => 
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


trainAdjP :: (Monad m, MonadIO m, Hashable a, Eq a) => 
	(Double,Double) ->
	(Double,Double) ->
	[[([Double], [Double])]] ->
	M.AdjointT 
		AdjNetworkL 
		AdjNetworkR
		m 
		()
trainAdjP p pe ldd = do
	i <- liftIO $ randomRIO p
	e <- liftIO $ randomRIO pe
	lnold <- adjFst $ adjGetEnv
	let ln = P.map (\n-> train i e n ldd) lnold
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
	retrun $ P.zip lh lc

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
	llhld <- fmap calculateAdj $ toLD a
	let llhEa = (fmap . fmap) (\(h,ld)->(h,Endo $ fromLD ld)) llhld
	let lha = foldr1 f llhEa
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
	fmap (trainAdj p pe) $ P.replicate i (P.zip (toLD x) (toLD y))

trainAdjLDL :: (Monad m, MonadIO m, Hashable a, ListDoubled a, Eq a) => 
	(Double,Double) ->
	(Double,Double) ->
	[(a, a)] ->
	Replicate ->
	M.AdjointT 
		AdjNetworkL 
		AdjNetworkR
		m 
		()
trainAdjLDL p pe lp i = do
	fmap (trainAdj p pe) $ fmap (\(x,y)-> (toLD x, toLD y)) lp

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

upNNGr :: (Monad m, MonadIO m, Hashable a, Eq a) => 
	M.AdjointT 
		(NNGrAdjL a) 
		(NNGrAdjR a)
		m 
		()
upNNGr = do
	gr <- adjFst $ adjGetEnv
	let ln = G.labNodes gr
	rnode <- liftIO $ getRandomElementList ln
	let ma = G.lab gr rnode
	mapM (\a-> do
		lr <- adjSnd $ calculateAdjLD $ unhashed a
		let lnewNodes = newNodes (P.length lr) gr`
		adjFst $ adjSetEnv 
			(foldr 
				(\(nn,(h,a)) b-> 
					(insEdge (rnode,nn,h) . insNode (nn,hashed a)) b
				) gr $ P.zip lnewNodes lr
			) (Identity ())
		) ma

type Replicate = Int

type SerchInt = Int

updatingNNGr :: (Monad m, MonadIO m, Hashable a, Eq a) => 
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

upgradingNNGr :: (Monad m, MonadIO m, Hashable a, Eq a) => 
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
	adlSnd $ trainAdjLD d1 d2 pa r
	gr <- adjFst $ adjGetEnv
	adjFst $ adjSetEnv 
		(foldr (\i b->insNode (i,snd pa) b) gr $ newNodes 1 gr) (Identity ())
	mapM (\_-> do
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
	let se = fold $ fmap (\(_,_,x)-> Set.singelton x) $ G.labEdges gr
	ln <- adjSnd $ adjFst $ adjGetEnv
	adjSnd $ adjFst $ adjSetEnv (P.filter (\n-> Set.member (hash $ packNetwork n) se) ln) (Identity ())

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
	impnn <- fmap fold $ mapM (\n->do
		let pnn = packNetwork n
		return $ IMap.singleton (hash pnn) pnn
		)
	im <- adjFst $ adjGetEnv
	adjFst $ adjSetEnv (IMap.union im impnn) (Identity ())

safeCalculate :: (Monad m, MonadIO m, Hashable a, Eq a) => 
	a ->
	M.AdjointT 
		(NNPrimeAdjL a) 
		(NNPrimeAdjR a)
		m 
		[(HashNN,a)]
safeCalculate a = do
	lpn <- fmap fold $ (fmap . fmap) (\(pn,_)-> [unpackNetwork pn]) $ adjFst $ adjGetEnv
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
		a -> 
	M.AdjointT 
		(NNSccListAdjL a) 
		(NNSccListAdjR a)
		m
		a
adjNNSLliftLN = adjSnd . adjSnd . adjFst

adjNNSLliftLayers :: Monad m =>
	M.AdjointT 
		(Env Layers)
		(Reader Layers)
		m
		a -> 
	M.AdjointT 
		(NNSccListAdjL a) 
		(NNSccListAdjR a)
		m
		a
adjNNSLliftLayers = adjSnd . adjSnd . adjSnd . adjSnd

adjNNSLliftAdjNetworkL :: Monad m =>
	M.AdjointT 
		AdjNetworkL
		AdjNetworkR
		m
		a -> 
	M.AdjointT 
		(NNSccListAdjL a) 
		(NNSccListAdjR a)
		m
		a
adjNNSLliftAdjNetworkL = adjSnd . adjSnd . adjSnd

adjNNSLliftNNGr :: Monad m =>
	M.AdjointT 
		(Env (Gr (Hashed a) HashNN))
		(Reader (Gr (Hashed a) HashNN))
		m
		a -> 
	M.AdjointT 
		(NNSccListAdjL a) 
		(NNSccListAdjR a)
		m
		a
adjNNSLliftNNGr = adjSnd . adjSnd . adjFst

adjNNSLliftAdjNNGr :: Monad m =>
	M.AdjointT 
		(NNGrAdjL a)
		(NNGrAdjR a)
		m
		a -> 
	M.AdjointT 
		(NNSccListAdjL a) 
		(NNSccListAdjR a)
		m
		a
adjNNSLliftAdjNNGr = adjSnd . adjSnd

adjNNSLliftIntMapPrimeNN :: Monad m =>
	M.AdjointT 
		(Env IntMapPrimeNN)
		(Reader IntMapPrimeNN)
		m
		a -> 
	M.AdjointT 
		(NNSccListAdjL a) 
		(NNSccListAdjR a)
		m
		a
adjNNSLliftIntMapPrimeNN = adjSnd . adjFst

adjNNSLliftAdjNNPrime :: Monad m =>
	M.AdjointT 
		(NNPrimeAdjL a)
		(NNPrimeAdjR a)
		m
		a -> 
	M.AdjointT 
		(NNSccListAdjL a) 
		(NNSccListAdjR a)
		m
		a
adjNNSLliftAdjNNPrime = adjSnd

adjNNSLliftHAG :: Monad m =>
	M.AdjointT 
		(HistoryAdjL [(Gr (Hashed a) HashNN)])
		(HistoryAdjR [(Gr (Hashed a) HashNN)])
		m
		a -> 
	M.AdjointT 
		(NNSccListAdjL a) 
		(NNSccListAdjR a)
		m
		a
adjNNSLliftHAG = adjFst

addToHSccList :: (Monad m, MonadIO m, Hashable a, Eq a) => 
	[HashScc]
	M.AdjointT 
		(NNSccListAdjL a) 
		(NNSccListAdjR a)
		m 
		()
addToHSccList lh = do
	lscc <- adjSnd getSccArtPoint
	adjFst $ addToLHistoryLeft $ P.filter (\scc-> P.elem (hash scc) lh) lscc

newtype ShortDL a = ShortDL a deriving

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
	lgr <- adjSnd getSccArtPoint
	--let lgr = join $ maybeToList mlgr
	mgr <- liftIO $ getRandomElementList lgr
	rp <- fmap (join . maybeToList) $ mapM randomPath mgr
	let plrp = pairing rp
	adjSnd $ adjSnd $ trainAdjLDL p pe plrp
	lr <- adjSnd $ adjSnd $ calculateAdjLD $ fst pa
	let fl = P.filter (\(h,a)->a == (snd pa)) $ lr
	fmap catMaybes $ mapM (\x-> do 
		mn <- adjSnd $ adjSnd $ getNN $ fst x
		return $ do
			gr <- mgr
			n <- mn
			(gr,n)
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
		b <- adjSnd $ adjSnd $ lnnull
		lhscchnn <- restorationNNSccLPrimer p pe pa
		when (b || (P.null lhscchnn)) $ do
			adjSnd $ adjSnd $ creatRandomNetworksAdj_ snn
			adjSnd $ adjFst $ adjSetEnv G.empty (Identity ())
			adjSnd $ upgradingNNGr p pe pa r si ui
		fmap (unionScc . catMaybes) $ mapM (\(hscc,hnn)->do
			let n = packNetwork hnn
			return (IMap.singelton (hash $ n) (n,hscc))
			) lhscchnn
		) [0..rc]
	adjSnd $ onlyInGr
	return $ hnn

unionScc = foldr (IMap.unionWith (\(x1,y1) (_,y2)->(x1,y1++y2))) IMap.empty

restorationNNSccLPrimerUpSafe :: (Monad m, MonadIO m, Hashable a, ListDoubled a, Eq a) => 
	(IntMap ([[PackedNeuron]],[Gr (Hashed a) HashNN])) ->
	M.AdjointT 
		(NNSccListAdjL a) 
		(NNSccListAdjR a)
		m 
		()
restorationNNSccLPrimerUpSafe impngr =
	sequenceA $ fold $ IMap.mapWithKey (\knn (pn,hscc)->do
		im <- adjSnd $ adjFst $ adjGetEnv
		let im' = IMap.insertWith (\(x1,y1) (_,y2)->(x1,y1++y2)) knn (pn,[hash hscc])
		adjSnd $ adjFst $ adjSetEnv im' (Identity ())
		return $ [hash hscc]
		) impngr
	lgr <- fmap (IMap.toList . fold) $ mapM (\(pn,gr)->do
		return $ IMap.singleton (hash gr) gr
		) impngr
	adjFst $ addToLHistoryLeft lgr
	adjSnd $ adjSnd $ adjFst $ adjSetEnv G.empty (Identity ())

type NNSLPowAdjL f a = (NNSccListAdjL (Gr (Hashed a) HashNN)) :.: f -- (NNSccListAdjL a) 

type NNSLPowAdjR g a = g :.: (NNSccListAdjR (Gr (Hashed a) HashNN)) -- (NNSccListAdjR a)

instance ListDoubled a => ListDoubled (Gr (Hashed a) HashNN) where
	-- toLD :: a -> [[Double]]
	toDl a = ufold (\(_,i,v,_) c-> (fmap (\ld-> (fromIntegral i):ld), toDl v) ++ c ) [] a
	-- fromLD :: [Double] -> a -> a
	fromLD (di:ld) gr = maybe gr id $
		fmap (\(ladj,i,a,radj)-> insert (ladj,i,fromLD ld a,radj) gr') mc
		where
			(mc,gr') <- match (round di) gr

class ClassNNSLPowAdj f g a where
	liftNNSccListAdjGr :: (Monad m, Hashable a, Eq a) =>
		M.AdjointT 
			(NNSccListAdjL (Gr (Hashed a) HashNN)) 
			(NNSccListAdjR (Gr (Hashed a) HashNN))
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
		ClassNNSLPowAdj f g a
	) => 
	(Double,Double) ->
	(Double,Double) ->
	-- (a,a) ->
	RestorationCycle ->
	SizeNN ->
	Replicate ->
	SerchInt ->
	UpgradingInt ->
	M.AdjointT f g m ()
restorationPow p pe rc snn r si ui = do
	mplhl <- liftNNSccListAdjA $ adjNNSLliftHAG $ viewHPairLeft -- viewHistoryLeft
	--mlhgr <- liftNNSccListAdjGr $ adjNNSLliftHAG $ viewHistoryLeft
	mapM (\(xl,yl)-> do
		let lp = join $ fmap (\y->fmap (\x->(x,y)) xl) yl
		limpngr <- mapM (\plgr->do 
			liftNNSccListAdjGr $ restorationNNSccLPrimerUp' p pe plgr rc snn r si ui -- ???
			) lp
			return (x,y)
		impngr <- if not (P.null limpngr) 
			then return $ unionScc limpngr
			else return ([],[])
		im <- fmap (foldr1 (\(x1,y1,t1) (x2,y2,t2)-> 
				if t1 < t2
					then (x1,y1)
					else (x2,y2)
				)) $
			mapM (\(pn,lgr)->do
			sm <- fmap P.sum $ mapM (\(pn2,lgr2)->do
				return $ metric pn pn2
				) impmgr 
			return (pn,lgr,sm)
			) impngr
		let rl = P.filter (\x-> IMap.member (hash $ fst im) x) limpngr
		mr <- liftIO $ getRandomElementList rl
		mapM_ (\r-> do
			liftNNSccListAdjGr $ restorationNNSccLPrimerUpSafe r
			) mr
		) $ do
			(lx,ly) <- mplhl
			--lx <- mlhgr
			--ly <- mlhl
			return (lx,ly) --v join $ fmap topsort'

restorationPowUp :: 
	(	Monad m, MonadIO m, Hashable a, ListDoubled a,Eq a,
		ClassNNSLPowAdj f g a
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
		adjNNSLliftHAG $ 
			restorationNNSccLPrimerUp p pe pa rc snn r si ui
	restorationPow p pe rc snn r si ui

type HashNNGr = HashNN

-- force
assumption' :: 
	(	Monad m, MonadIO m, Hashable a, ListDoubled a,Eq a,
		ClassNNSLPowAdj f g a
	) =>
	M.AdjointT f g m 
		[(HashNNGr,(Gr (Hashed a) HashNN),(Gr (Hashed a) HashNN))] -- (Gr (Hashed a) HashNN))
		-- just Gr (Hashed a) ()
assumption' = do
	-- lmgr <- liftNNSccListAdjGr $ adjNNSLliftHAG $ viewHistoryLeft -- liftNNSccListAdjGr $ 
	lmgr <- liftNNSccListAdjA $ adjNNSLliftHAG $ viewHistoryLeft
	fmap (join . maybeToList) $ mapM (\lgr->do
		mapM (\gr->do
			hgr <- liftNNSccListAdjGr $ adjNNSLliftIntMapPrimeNN $ safeCalculate gr
			return $ fmap (\(h,g)->(h,gr,g)) hgr
			) lgr
		) lmgr -- (join $ fmap topsort' lmgr)

assumptionRestoration :: 
	(	Monad m, MonadIO m, Hashable a, ListDoubled a,Eq a,
		NNSccListAdj f g a
	) =>
	(Double,Double) ->
	(Double,Double) ->
	a ->
	[(HashNNGr,(Gr (Hashed a) HashNN),(Gr (Hashed a) HashNN))] ->
	M.AdjointT 
		(NNSccListAdjL a) 
		(NNSccListAdjR a)
		-- (NNSLPowAdjL f a) 
		-- (NNSLPowAdjR g a)
		m 
		[(Gr (Hashed a) HashNN),(Gr (Hashed a) HashNN),HashNNGr,HashNN,a)] -- !!!
assumptionRestoration p pe a lhgr = do
	-- like restorationNNSccLPrimer
	mrhgr <- liftIO $ getRandomElementList lhgr
	fmap (join $ maybeToList) $ mapM (\(rh, grr, gr)->do
		rp <- liftIO $ randomPath gr
		let plrp = pairing rp 
		adjSnd $ adjSnd $ trainAdjLDL p pe plrp
		ha <- adjSnd $ adjSnd $ calulateAdjLD a
		return $ fmap (\(h,x)->(grr,gr,rh,h,x)) ha
		) mrhgr

type SizeAssumptionRestoration = Int

assumptionRestorationUp :: 
	(	Monad m, MonadIO m, Hashable a, ListDoubled a,Eq a,
		NNSccListAdj f g a
	) =>
	(Double,Double) ->
	(Double,Double) ->
	a ->
	SizeNN ->
	Replicate ->
	SerchInt ->
	UpgradingInt ->
	SizeAssumptionRestoration -> 
	[(HashNNGr,(Gr (Hashed a) HashNN),(Gr (Hashed a) HashNN))] ->
	M.AdjointT f g m 
		(HashMap a ([(Gr (Hashed a) HashNN,Gr (Hashed a) HashNN, HashNNGr,[[[PackedNeuron]]])]))
assumptionRestorationUp p pe pa snn r si ui sar lhgr = do
	-- like restorationNNSccLPrimerUp'
	liftNNSccListAdjA $ adjNNSLliftAdjNetworkL $ creatRandomNetworksAdj_ snn
	fmap f $ mapM (\_->do
		b <- liftNNSccListAdjA $ adjNNSLliftLN $ lnnull
		-- lhgr <- assumption'
		lhscchnn <- liftNNSccListAdjA $ assumptionRestoration p pe a lhgr
		when (b || (P.null lhscchnn)) $ do -- evretime False
			liftNNSccListAdjA $ adjNNSLliftAdjNetworkL $ creatRandomNetworksAdj_ snn
			-- liftNNSccListAdjA $ adjNNSLliftNNGr $ adjSetEnv G.empty (Identity ()) -- ???
			-- liftNNSccListAdjA $ adjNNSLliftNNGr $ upgradingNNGr p pe pa r si ui -- ??? 
			-- because assumption
		fmap (f . catMaybes) $ mapM (\(gr1,gr2,hgr,hnn,x)->do
			nn <- liftNNSccListAdjA $ adjNNSLliftLN $ getNN hgr
			let n = packNetwork nn
			return (Map.singelton x ([(gr1,gr2,hgr,[n])]))
			) lhscchnn
		) [0..sar]
	where
		f = foldr (Map.unionWith (\l1 l2-> l1 ++ l2
			) Map.empty
		-- foldr (Map.unionWith (\(x1) (x2)->(x1++x2,y1++y2))) Map.empty
{-}
resultAssumption :: Hashable a =>
	[(Gr (Hashed a) HashNN,Gr (Hashed a) HashNN, [[PackedNeuron]])] ->
	HashMap a ([(Gr (Hashed a) HashNN,Gr (Hashed a) HashNN, [[PackedNeuron]])],[HashNN])
resultAssumption = unionRA . fmap (\(gr,rh,h,a) -> Map.singleton a ([(gr,rh)],[h]))
	where
		unionRA = foldr (Map.unionWith (\(x1,y1) (x2,y2)->(x1++x2,y1++y2))) Map.empty
-}
resultAssumptionTrue :: Eq a =>
	a ->
	HashMap a ([(Gr (Hashed a) HashNN,Gr (Hashed a) HashNN, HashNNGr,[[[PackedNeuron]]])]) ->
	HashMap a ([(Gr (Hashed a) HashNN,Gr (Hashed a) HashNN, HashNNGr,[[[PackedNeuron]]])])
resultAssumptionTrue a hm = Map.filterWithKey (\k _ -> k == a) hm

type ReasonGr a = Gr (Hashed a) HashNN

type ConsequenceGr a = Gr (Hashed a) HashNN

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
		NNSccListAdj f g a, ClassMapGrAdj f g a
	) =>
	a ->
	HashMap a ([(Gr (Hashed a) HashNN,Gr (Hashed a) HashNN, HashNNGr,[[[PackedNeuron]]])]) ->
	M.AdjointT f g m (IntMap [(HashSccR,HashSccC)])
safeTrueAssumptuon ta hma = do
	let thma = resultAssumptionTrue ta hma
	fmap f $ mapM (\l->
		fmap f $ mapM (\ (gr1, gr2, nngr, lpn) -> do
			mgr <- liftMapGrAdj $ adjGetEnv
			let mgr' = Map.insertWith (++) gr1 [(gr2,hash nngr)]
			liftMapGrAdj $ adjSetEnv mgr' (Identity ())
			mapM_ (\pn->do
				im <- liftNNSccListAdjA $ adjNNSLliftIntMapPrimeNN $ adjGetEnv
				let im' = IMap.insertWith (\(x1,y1) (_,y2)->(x1,y1++y2)) knn (pn,[hash gr2])
				liftNNSccListAdjA $ adjNNSLliftIntMapPrimeNN $ adjSetEnv im' (Identity ())
				) lpn
			return $ IMap.singleton (hash nngr) [(hash gr1, hash gr2)]
			) l
		) thma
	where
		f = foldr (IMap.unionWith (\y1 y2->y1++y2) IMap.empty

memoriAssumption :: 
	(	Monad m, MonadIO m, Hashable a, ListDoubled a,Eq a,
		ClassNNSLPowAdj f g a, ClassMapGrAdj f g a
	) => 
	M.AdjointT f g m [(ConsequenceGr a,HashNNGr)]
memoriAssumption = do
	lmgr <- liftNNSccListAdjA $ adjNNSLliftHAG $ viewHistoryLeft
	mgr <- liftMapGrAdj $ adjGetEnv
	fmap (join . maybeToList) $ mapM (\lgr->do
		fmap (join . catMaybes) $ mapM (\gr->do
			mlch <- Map.lookup gr mgr
			return mlch
			) lgr
		) lmgr

type IMapNNRC = IntMap [(HashSccR,HashSccC)]

type IMapNNRCAdjL f = (Env IMapNNRC) :.: f -- (NNSccListAdjL a) 

type IMapNNRCAdjR g = g :.: (Reader IMapNNRC) -- (NNSccListAdjR a)

safeTrueAssumptuonNNRC :: 
	(	Monad m, MonadIO m, Hashable a, ListDoubled a,Eq a,
		-- NNSccListAdj f g a
	) =>
	IntMap [(HashSccR,HashSccC)] ->
	M.AdjointT (Env IMapNNRC) (Reader IMapNNRC) m ()
safeTrueAssumptuonNNRC imnnrc = do
	imrc <- adjGetEnv
	let imrc' = Map.unionWith (++) imrc imnnrc
	adjSetEnv imrc' (Identity ())

class ClassIMapNNRAdj f g where
	liftIMapNNRAdj :: (Monad m, Hashable a, Eq a) =>
		M.AdjointT (Env IMapNNRC) (Reader IMapNNRC) m b ->
		M.AdjointT f g m b

safeTrueAssumptuonFull :: 
	(	Monad m, MonadIO m, Hashable a, ListDoubled a,Eq a,
		ClassNNSLPowAdj f g a, ClassMapGrAdj f g a, ClassIMapNNRAdj f g
	) => 
	a ->
	HashMap a (([(Gr (Hashed a) HashNN,Gr (Hashed a) HashNN),[[PackedNeuron]])],[HashNN]) ->
	M.AdjointT f g m ()
safeTrueAssumptuonFull ta hma = do
	o <- liftMapGrAdj $ safeTrueAssumptuon ta hma
	liftIMapNNRAdj $ safeTrueAssumptuonNNRC o

type AllResult a = 
	HashMap a (([(Gr (Hashed a) HashNN,Gr (Hashed a) HashNN),[[PackedNeuron]])],[HashNN])

type ConsequenceResult a = 
	HashMap a (([(Gr (Hashed a) HashNN,Gr (Hashed a) HashNN),[[PackedNeuron]])],[HashNN])

updateAssumptionPre :: 
	(	Monad m, MonadIO m, Hashable a, ListDoubled a,Eq a,
		ClassNNSLPowAdj f g a, ClassMapGrAdj f g a, ClassIMapNNRAdj f g,
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
	M.AdjointT f g m 
		( AllResult a
		, ConsequenceResult a
		)
updateAssumptionPre p pe a snn r si ui sar = do
	lift $ logInfoM "Start: updateAssumptionPre"
	lhngr <- assumption'
	hmagr <- assumptionRestorationUp p pe a snn r si ui sar lhngr
	lc <- memoriAssumption
	lift $ logInfoM $ "Assumption size: " .< (P.length lhngr)
	lift $ logInfoM "End: updateAssumptionPre"
	return 
		( hmagr
		, Map.filter 
			(\(lgr,_)-> or $ 
				fmap (\(grr,grc,pn)-> isJust $ P.lookup (hash grc) lc) lgr
			) 
			hmagr
		)

updateAssumptionPost :: 
	(	Monad m, MonadIO m, Hashable a, ListDoubled a,Eq a,
		ClassNNSLPowAdj f g a, ClassMapGrAdj f g a, ClassIMapNNRAdj f g
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
	M.AdjointT f g m 
		( AllResult a
		, ConsequenceResult a
		)
updateAssumptionPost p pe pa snn r si ui sar pr = do
	safeTrueAssumptuonFull (snd pa) (fst pr)
	restorationPowUp p pe pa snn r si ui sar

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
	liftConfNNAdj :: (Monad m, Hashable a, Eq a) =>
		M.AdjointT (Env ConfNN) (Reader ConfNN) m b ->
		M.AdjointT f g m b

getConfNN :: (Monad m, Hashable a, Eq a, ClassConfNNAdj f g) =>
	M.AdjointT f g m ConfNN
getConfNN = liftConfNNAdj $ adjGetEnv

setConfNN :: (Monad m, Hashable a, Eq a) =>
	ConfNN ->
	M.AdjointT f g m ()
setConfNN dm = do
	liftConfNNAdj $ adjSetEnv dm (Identity ())

data DataNN = DataNN
	{ nnLayers :: Layers
	, nnMap :: IntMapPrimeNN
} deriving (Generic, ToJSON, FromJSON)

getDataNN :: (Monad m, Hashable a, Eq a, ClassConfNNAdj f g) =>
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
	l <- adjNNSLliftLayers $ adjSetEnv (nnLayers dm) (Identity ())
	im <- adjNNSLliftIntMapPrimeNN $ adjSetEnv (nnMap dm) (Identity ())

data DataNNSLPow a = DataNNSLPow
	{ dnnGr :: DataNN
	, dnnA :: DataNN
	, hmrcgr :: MapGr a
	, imrcnn :: IMapNNRC
} deriving (Generic, ToJSON, FromJSON)

getDataNNSLPow :: 
	(	Monad m, MonadIO m, Hashable a, ListDoubled a,Eq a,
		ClassNNSLPowAdj f g a, ClassMapGrAdj f g a, ClassIMapNNRAdj f g
	) => 
	M.AdjointT f g m DataNNSLPow
getDataNNSLPow = do 
	dnngr <- liftNNSccListAdjGr $ adjGetEnv
	dnna <- liftNNSccListAdjA $ adjGetEnv
	mgr <- liftMapGrAdj $ adjGetEnv
	im <- liftIMapNNRAdj $ adjGetEnv
	return $ DataNNSLPow dnngr dnna mgr im

setDataNNSLPow :: 
	(	Monad m, MonadIO m, Hashable a, ListDoubled a,Eq a,
		ClassNNSLPowAdj f g a, ClassMapGrAdj f g a, ClassIMapNNRAdj f g
	) => 
	DataNNSLPow ->
	M.AdjointT f g m ()
setDataNNSLPow dm = do
	liftNNSccListAdjGr $ adjSetEnv (dnnGr dm) (Identity ())
	liftNNSccListAdjA $ adjSetEnv (dnnA dm) (Identity ())
	liftMapGrAdj $ adjSetEnv (hmrcgr dm) (Identity ())
	liftIMapNNRAdj $ adjSetEnv (imrcnn dm) (Identity ())