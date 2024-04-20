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

-- (Monad m, MonadIO m, Hashable a, Eq a) => 
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
	--mapM (\lhld-> do
	--	return $ foldr (\(h,ld)) (_,b)-> (h, fmap (\x-> fromLD x b) ld) ) (undefined,a) lhld
	---	) llhld
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

unionScc = foldr (IMap.unionWith (\(x1,y1) (_,y2)->(x1,y1++y2))) Map.empty

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

type ShortLayers = Layers

generationNNSccListShort :: (Monad m, MonadIO m, Hashable a, ListDoubled (ShortDL a),Eq a) => 
	(Double,Double) ->
	(Double,Double) ->
	ShortLayers ->
	SizeNNShort ->
	M.AdjointT 
		(NNSccListAdjL a) 
		(NNSccListAdjR a)
		m 
		(HashScc,HashScc,[Bool])
generationNNSccListShort p pe sl snns = do
	pl <- adjSnd $ adjSnd $ adjSnd $ adjSnd adjGetEnv
	adjSnd $ adjSnd $ adjSnd $ adjSnd $ adjSetEnv sl (Identity ())
	mp <- adjFst $ viewHPairLeft
	lb <- fmap join $ mapM (\(xl,yl)-> do
		mx <- liftIO $ getRandomElementList xl
		my <- liftIO $ getRandomElementList yl
		lb <- mapM (\(x,y)-> do
			let xtop = topsort' x
			let ytop = topsort' y
			let ptop = P.zip xtop ytop
			adjSnd $ adjSnd $ adjSnd $ creatRandomNetworksAdj_ snns
			adjSnd $ adjSnd $ adjSnd $ trainAdjLDL p pe (pointSDL ptop)
			llr <- adjSnd $ adjSnd $ adjSnd $ calculateAdjLDL (ShortDL xtop)
			return $ 
				foldl 
					(\b (lx,y)-> and [b,and $ fmap ((== y) . snd) lx]) 
					True $ 
				P.zip llr (ShortDL ytop)
			) $ do
			x <- mx
			y <- my
			return (x,y)
		return (do
			x <- mx
			y <- my
			lb' <- lb
			return (x,y,lb'))
		) mp
	adjSnd $ adjSnd $ adjSnd $ adjSnd $ adjSetEnv pl (Identity ())
	return lb

{-}
restorationGoGeneration :: (Monad m, MonadIO m, Hashable a, ListDoubled (ShortDL a),Eq a) => 
	(Double,Double) ->
	(Double,Double) ->
	(a,a) ->
	RestorationCycle ->
	SizeNN ->
	Replicate ->
	SerchInt ->
	UpgradingInt ->
	ShortLayers ->
	SizeNNShort ->
	M.AdjointT 
		(NNSccListAdjL a) 
		(NNSccListAdjR a)
		m 
		[Bool]
restorationGoGeneration p pe pa rc snn r si ui sl snns = do
	restorationNNSccLPrimerUp p pe pa rc snn r si ui
	lb <- generationNNSccListShort p pe sl snns
	return (hs,lb)
-}
{-}
type HashShortNN = Hash

type IntMapShortNN = IntMap ([[PackedNeuron]],[(HashSccGr,HashSccGr)]) --Short

type NNShortAdjL a = (Env IntMapShortNN) :.: (NNSccListAdjL a)

type NNShortAdjR a = (NNSccListAdjR a) :.: (Reader IntMapShortNN)

adjNNSliftLN :: Monad m =>
	M.AdjointT 
		(Env LNetwork)
		(Reader LNetwork)
		m
		a -> 
	M.AdjointT 
		(NNShortAdjL a) 
		(NNShortAdjR a)
		m
		a
adjNNSliftLN = adjSnd . adjSnd . adjSnd . adjSnd . adjFst

adjNNSliftLayers :: Monad m =>
	M.AdjointT 
		(Env Layers)
		(Reader Layers)
		m
		a -> 
	M.AdjointT 
		(NNShortAdjL a) 
		(NNShortAdjR a)
		m
		a
adjNNSliftLayers = adjSnd . adjSnd . adjSnd . adjSnd . adjSnd

adjNNSliftAdjNetworkL :: Monad m =>
	M.AdjointT 
		AdjNetworkL
		AdjNetworkR
		m
		a -> 
	M.AdjointT 
		(NNShortAdjL a) 
		(NNShortAdjR a)
		m
		a
adjNNSliftAdjNetworkL = adjSnd . adjSnd . adjSnd . adjSnd

adjNNSliftNNGr :: Monad m =>
	M.AdjointT 
		(Env (Gr (Hashed a) HashNN))
		(Reader (Gr (Hashed a) HashNN))
		m
		a -> 
	M.AdjointT 
		(NNShortAdjL a) 
		(NNShortAdjR a)
		m
		a
adjNNSliftNNGr = adjSnd . adjSnd . adjSnd . adjFst

adjNNSliftAdjNNGr :: Monad m =>
	M.AdjointT 
		(NNGrAdjL a)
		(NNGrAdjR a)
		m
		a -> 
	M.AdjointT 
		(NNShortAdjL a) 
		(NNShortAdjR a)
		m
		a
adjNNSliftAdjNNGr = adjSnd . adjSnd . adjSnd

adjNNSliftIntMapPrimeNN :: Monad m =>
	M.AdjointT 
		(Env IntMapPrimeNN)
		(Reader IntMapPrimeNN)
		m
		a -> 
	M.AdjointT 
		(NNShortAdjL a) 
		(NNShortAdjR a)
		m
		a
adjNNSliftIntMapPrimeNN = adjSnd . adjSnd . adjFst

adjNNSliftAdjNNPrime :: Monad m =>
	M.AdjointT 
		(NNPrimeAdjL a)
		(NNPrimeAdjR a)
		m
		a -> 
	M.AdjointT 
		(NNShortAdjL a) 
		(NNShortAdjR a)
		m
		a
adjNNSliftAdjNNPrime = adjSnd . adjSnd

adjNNSliftHAG :: Monad m =>
	M.AdjointT 
		(HistoryAdjL [(Gr (Hashed a) HashNN)])
		(HistoryAdjR [(Gr (Hashed a) HashNN)])
		m
		a -> 
	M.AdjointT 
		(NNShortAdjL a) 
		(NNShortAdjR a)
		m
		a
adjNNSliftHAG = adjSnd . adjFst

adjNNSliftNNSccListAdjL :: Monad m =>
	M.AdjointT 
		(NNSccListAdjL a)
		(NNSccListAdjR a)
		m
		a -> 
	M.AdjointT 
		(NNShortAdjL a) 
		(NNShortAdjR a)
		m
		a
adjNNSliftNNSccListAdjL = adjSnd

adjNNSliftNNSccListAdjL :: Monad m =>
	M.AdjointT 
		(Env IntMapShortNN)
		(Reader IntMapShortNN)
		m
		a -> 
	M.AdjointT 
		(NNShortAdjL a) 
		(NNShortAdjR a)
		m
		a
adjNNSliftIntMapShortNN = adjFst

type SizeGeneration = Int 

generationShortUp :: (Monad m, MonadIO m, Hashable a, ListDoubled (ShortDL a),Eq a) => 
	(Double,Double) ->
	(Double,Double) ->
	ShortLayers ->
	SizeNNShort ->
	SizeGeneration ->
	M.AdjointT 
		(NNShortAdjL a) 
		(NNShortAdjR a)
		m 
		()
generationShortUp p pe sl snns sg = do
	mapM_ (\_-> do
		(hx,hy,_) <- adjNNSliftNNSccListAdjL $ generationNNSccListShort p pe sl snns
		ln <- adjNNSliftLN adjGetEnv
		im <- adjFst $ adjGetEnv
		imn <- fmap (foldr (IMap.unionWith (\(x1,y1) (_,y2)->(x1,y1++y2))) Map.empty) $ 
			mapM (\n->do
				let pnn = packNetwork n
				return $ IMap.singleton (hash pnn) (pnn,[(hx,hy)])
				) ln
		adjFst $ adjSetEnv 
			(IMap.unionWith (\(x1,y1) (_,y2)->(x1,y1++y2)) im impnn) (Identity ())
		) [0.. sg]
-}
-- forse	
{-}	
calculateAdjShort :: (Monad m, MonadIO m, Hashable a, ListDoubled (ShortDL a),Eq a) =>
	M.AdjointT 
		(NNShortAdjL a) 
		(NNShortAdjR a)
		m 
		()
calculateAdjShort = do
	ln <- adjNNSliftLN adjGetEnv
	im <- adjFst $ adjGetEnv
	let limn = fmap (unpackNetwork  . fst) im
	adjNNSliftLN $ adjSetEnv limn (Identity ())
	mlgr <- adjNNSliftHAG $ viewHistoryLeft
	calculateAdjLD
-}
{-}
type IntMapSccNN = IntMap [HashNN] -- Prime

type IMSccAdjL a = (Env IntMapSccNN) :.: (NNPrimeAdjL a)

type IMSccAdjR a = (NNPrimeAdjR a) :.: (Reader IntMapSccNN)
-}

type NNSLPowAdjL f a = (NNSccListAdjL (Gr (Hashed a) HashNN)) :.: f -- (NNSccListAdjL a) 

type NNSLPowAdjR g a = g :.: (NNSccListAdjR (Gr (Hashed a) HashNN)) -- (NNSccListAdjR a)

--adjNNSLPowliftNNSccListAdjL = 

-- forse
restorationPow :: 
	(	Monad m, MonadIO m, Hashable a, ListDoubled a,Eq a,
		NNSccListAdj f g a
	) => 
	(Double,Double) ->
	(Double,Double) ->
	-- (a,a) ->
	RestorationCycle ->
	SizeNN ->
	Replicate ->
	SerchInt ->
	UpgradingInt ->
	M.AdjointT 
		(NNSLPowAdjL f a) 
		(NNSLPowAdjR g a)
		m 
		()
restorationPow p pe rc snn r si ui = do
	mlhl <- adjSnd $ liftNNSccListAdj $ adjNNSLliftHAG $ viewHistoryLeft
	mlhgr <- adjFst $ adjNNSLliftHAG $ viewHistoryLeft
	mapM (\(xl,yl)-> do
		let lp = join $ fmap (\y->fmap (\x->(x,y)) xl) yl
		limpngr <- mapM (\plgr->do 
			adjFst $ restorationNNSccLPrimerUp' p pe plgr rc snn r si ui
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
			adjFst $ restorationNNSccLPrimerUpSafe r
			) mr
		) $ do
			lx <- mlhgr
			ly <- mlhl
			return (join $ fmap topsort' lx,ly) -- ???!!!

restorationPowUp :: 
	(	Monad m, MonadIO m, Hashable a, ListDoubled a,Eq a,
		NNSccListAdj f g a
	) => 
	(Double,Double) ->
	(Double,Double) ->
	(a,a) ->
	RestorationCycle ->
	SizeNN ->
	Replicate ->
	SerchInt ->
	UpgradingInt ->
	M.AdjointT 
		(NNSLPowAdjL f a) 
		(NNSLPowAdjR g a)
		m 
		()
restorationPowUp p pe pa rc snn r si ui = do
	adjSnd $ 
		liftNNSccListAdj $ 
			adjNNSLliftHAG $ 
				restorationNNSccLPrimerUp p pe pa rc snn r si ui
	restorationPow p pe rc snn r si ui

-- force
assumption' :: 
	(	Monad m, MonadIO m, Hashable a, ListDoubled a,Eq a,
		NNSccListAdj f g a
	) =>
	M.AdjointT 
		(NNSLPowAdjL f a) 
		(NNSLPowAdjR g a)
		m 
		[(HashNN,(Gr (Hashed a) HashNN))]
assumption' = do
	lmgr <- adjFst $ adjNNSLliftHAG $ viewHistoryLeft
	imp <- adjFst $ adjNNSLliftIntMapPrimeNN $ adjGetEnv
	fmap (join . maybeToList) $ mapM (\gr->do
		adjFst $ adjNNSLliftIntMapPrimeNN $ safeCalculate gr
		) (join $ fmap topsort' lmgr)

assumptionRestoration :: 
	(	Monad m, MonadIO m, Hashable a, ListDoubled a,Eq a,
		NNSccListAdj f g a
	) =>
	[(HashNN,(Gr (Hashed a) HashNN))] ->
	M.AdjointT 
		(NNSLPowAdjL f a) 
		(NNSLPowAdjR g a)
		m 
		[([HashScc],a))]
assumptionRestoration lhgr = do
	-- like restorationNNSccLPrimer
	mrhgr <- liftIO $ getRandomElementList lhgr

{-
	mapM (\_-> do
		(hx,hy,_) <- adjNNSLliftNNSccListAdjL $ generationNNSccListShort p pe sl snns
		ln <- adjNNSLliftLN adjGetEnv
		im <- adjFst $ adjGetEnv
		fmap (foldr (IMap.unionWith (\(x1,y1) (_,y2)->(x1,y1++y2))) Map.empty) $ 
			mapM (\n->do
				let pnn = packNetwork n
				return $ IMap.singleton (hash pnn) (pnn,[(hx,hy)])
				) ln
		) [0.. sg]
}
-}