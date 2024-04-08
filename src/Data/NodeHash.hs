{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Data.NodeHash where

import Prelude as P
import Data.Sequence as Seq
import System.Random
import Data.Hashable
import Data.HashSet as Set
import Data.HashMap.Lazy as Map
import Data.Tree as Tree
import Data.Maybe
import Data.Foldable
import Data.Graph.Inductive.PatriciaTree as G
import Data.Graph.Inductive.Graph as G
import Data.Graph.Inductive.Query.ArtPoint as G
import Data.Graph.Inductive.Query.DFS as G
import Data.Aeson as Aeson
import Control.Monad.Trans.Adjoint as M
import Control.Monad.Reader
import Control.Monad
import Control.Comonad.Env
import Control.Monad.IO.Class
import GHC.Generics
import Control.Base.Comonad
import Control.Core.Biparam
import Control.Core.Composition
import Data.Functor.Identity
import Data.History

data NodeHash a = NodeH (HashSet (Hashed a)) (HashSet (Hashed a)) (Hashed a) (Hashed a)

type SeqHash a = Seq (NodeHash a)

type SizeSet = Int

generateNode :: (Monad m, MonadIO m, Hashable a, Eq a) => 
  SizeSet -> 
  [Hashed a] -> 
  a -> 
  M.AdjointT (HistoryAdjL a) (HistoryAdjR a) m (Maybe (NodeHash a))
generateNode i existHash nextA = do
	srTrue <- fmap (fold . fmap (Set.singleton . hashed)) $ 
		fmap catMaybes $ 
		mapM (\_-> adjSnd hitoryRondomElement) [0..i]
	let le = P.length existHash
	srFalse <- fmap fold $ mapM (\_->do
		ri <- lift $ randomRIO (0,le)
		--lift $ liftIO $ print ri
		if not (P.null existHash)
			then do
				let rs = existHash !! ri
				if not $ Set.member rs srTrue
					then return $ Set.singleton rs 
					else return Set.empty 
			else return Set.empty
		) [0..i]
	mvh <- adjSnd viewHistoryLeft
	mapM (\vh->return $ NodeH srTrue srFalse (hashed vh) (hashed nextA)) mvh

type PairSetH a = (HashSet (Hashed a), HashSet (Hashed a))

type HGrAdjL a = (Env (Gr (Hashed a) (PairSetH a))) :.: (HistoryAdjL a)

type HGrAdjR a = (HistoryAdjR a) :.: (Reader (Gr (Hashed a) (PairSetH a)))

getHashNode :: NodeHash a -> Hashed a
getHashNode (NodeH _ _ _ h) = h

getLastHash :: NodeHash a -> Hashed a
getLastHash (NodeH _ _ h _) = h

getPairSetH :: NodeHash a -> PairSetH a
getPairSetH (NodeH x y _ _) = (x,y)

getInfoHGr ::(Monad m, Hashable a, Eq a) => 
	M.AdjointT 
		(Env (Gr (Hashed a) (PairSetH a))) 
		(Reader (Gr (Hashed a) (PairSetH a))) 
		m 
		(HashMap (Hashed a) Node, HashMap (PairSetH a) [(Node,Node)])
getInfoHGr = do
	gr <- adjGetEnv
	return $ ufold (\(lbnl,n,a,lbnr) (x,y)-> 
			( x <> (Map.singleton a n)
			, y <> 
				( P.foldl (\ m1 m2 -> unionWith (P.++) m1 m2) Map.empty $ 
					fmap (\ (b,n2) -> Map.singleton b [(n2,n)]) lbnl 
				) <>
				( P.foldl (\ m1 m2 -> unionWith (P.++) m1 m2) Map.empty $ 
					fmap (\ (b,n2) -> Map.singleton b [(n,n2)]) lbnr
				)
			)
		) (Map.empty, Map.empty) gr

setNodeHashToGr :: (Monad m, Hashable a, Eq a) => 
	NodeHash a ->
	M.AdjointT 
		(Env (Gr (Hashed a) (PairSetH a))) 
		(Reader (Gr (Hashed a) (PairSetH a))) 
		m 
		()
setNodeHashToGr (nh :: NodeHash a) = do
	(mN, mE) <- getInfoHGr
	let hn = getHashNode nh
	let psh = getPairSetH nh
	when (not $ Map.member hn mN) $ do
		gr <- adjGetEnv
		let [nn] = newNodes @Gr @(Hashed a) @(PairSetH a) 1 gr
		let ngr = insNode (nn,hn) gr
		adjSetEnv (ngr :: Gr (Hashed a) (PairSetH a)) (Identity ())
	(mN2, mE2) <- getInfoHGr
	let mn1 = Map.lookup hn mN2
	let lhn = getLastHash nh
	let mn2 = Map.lookup lhn mN2
	mapM_ (\(x,y)-> do
		grn <- adjGetEnv
		when (not $ hasLEdge grn (y,x,psh)) $ do 
			adjSetEnv (insEdge (y,x,psh) grn) (Identity ())
		) (do
		n1 <- mn1
		n2 <- mn2
		return (n1,n2)
		)

showGr :: (Monad m, Hashable a, Eq a, Show a) =>
	M.AdjointT 
		(Env (Gr (Hashed a) (PairSetH a))) 
		(Reader (Gr (Hashed a) (PairSetH a))) 
		m 
		String
showGr = do
	gr <- adjGetEnv
	return $ prettify gr

getArtPoints :: (Monad m, Hashable a, Eq a, Show a) =>
	M.AdjointT 
		(Env (Gr (Hashed a) (PairSetH a))) 
		(Reader (Gr (Hashed a) (PairSetH a))) 
		m 
		[Hashed a]
getArtPoints = do
	gr <- adjGetEnv
	let lp = catMaybes $ fmap (\p-> G.lab gr p) $ G.ap gr
	return lp

getComponentsGr :: (Monad m, Hashable a, Eq a, Show a) =>
	M.AdjointT 
		(Env (Gr (Hashed a) (PairSetH a))) 
		(Reader (Gr (Hashed a) (PairSetH a))) 
		m 
		[[Hashed a]]
getComponentsGr = do
	gr <- adjGetEnv
	let lp = fmap catMaybes $ (fmap . fmap) (\p-> G.lab gr p) $ G.components gr
	return lp 

getSccGr :: (Monad m, Hashable a, Eq a, Show a) =>
	M.AdjointT 
		(Env (Gr (Hashed a) (PairSetH a))) 
		(Reader (Gr (Hashed a) (PairSetH a))) 
		m 
		[[Hashed a]]
getSccGr = do
	gr <- adjGetEnv
	let lp = fmap catMaybes $ (fmap . fmap) (\p-> G.lab gr p) $ G.scc gr
	return lp 

stepMemoring :: (Monad m, MonadIO m, Hashable a, Eq a) => 
  SizeSet -> 
  [Hashed a] -> 
  a -> 
  M.AdjointT (HGrAdjL a) (HGrAdjR a) m ()
stepMemoring i existHash nextA = do
	mnh <- adjSnd $ generateNode i existHash nextA
	mapM_ (\nh->adjFst $ setNodeHashToGr nh) mnh

data Memored a = Memored
	{ listMemored :: [Hashed a]
	, setMemored :: PairSetH a
	, lastHesh :: Hashed a
	, nextHash :: Hashed a
	, mising :: Int
}

type MaxMising = Int

type LMemored a = [Memored a]

type MemAdjL a = (Env (LMemored a)) :.: (HGrAdjL a)

type MemAdjR a = (HGrAdjR a) :.: (Reader (LMemored a))

upMemored :: (Monad m, Hashable a, Eq a) => 
	MaxMising ->
	M.AdjointT (MemAdjL a) (MemAdjR a) m [(PairSetH a, Hashed a)]
upMemored mm = do
	mvh <- adjSnd $ adjSnd $ adjSnd viewHistoryLeft
	fmap (join . maybeToList) $ mapM (\v->do
		let vh = hashed v
		gri <- adjSnd $ adjFst getInfoHGr
		gr <- adjSnd $ adjFst adjGetEnv
		lmem <- adjFst $ adjGetEnv
		lmem2 <- mapM (\mem-> do
			if Set.member vh (fst $ setMemored mem) && not (Set.member vh (snd $ setMemored mem))
				then return $ mem {listMemored = vh:(listMemored mem)}
				else return $ mem {mising = (mising mem) + 1}
			) lmem
		lmem3 <- fmap catMaybes $ mapM (\mem->do
			if ((mising mem) > mm || 
				(P.length (listMemored mem) > Set.size (fst $ setMemored mem)) ||
				(Set.member vh (snd $ setMemored mem))
				)
				then return Nothing
				else return $ Just mem
			) lmem2
		let addLMem = foldMapWithKey (\k v-> fmap (\(x,y)->Memored [vh] k (lab' $ context gr x) (lab' $ context gr y) 0) v) $ snd gri
		adjFst $ adjSetEnv (lmem3 ++ addLMem) (Identity ())
		fmap catMaybes $ mapM (\mem->do
			if vh == (lastHesh mem)
				then if Set.fromList (listMemored mem) == (fst $ setMemored mem)
					then return $ Just (setMemored mem,nextHash mem)
					else return Nothing
				else return Nothing
			) lmem2
		) mvh

upadteMemored :: (Monad m, MonadIO m, Hashable a, Eq a) => 
	MaxMising ->
	SizeSet -> 
  [Hashed a] -> 
  a -> 
	M.AdjointT (MemAdjL a) (MemAdjR a) m [Bool]
upadteMemored mm ss le a = do
	lpshh <- upMemored mm
	lb <- mapM (\(_,h)->
		return $ h == (hashed a) 
		) lpshh
	when (P.null lb || not (or lb)) $ do
		adjSnd $ stepMemoring ss le a
	adjSnd $ adjSnd $ addToLHistoryLeft a
	return lb

instance (ToJSON a, ToJSON b) => ToJSON (Gr a b)
instance (FromJSON a, FromJSON b) => FromJSON (Gr a b)

instance (ToJSON a, Hashable a) => ToJSON (Hashed a) where
	toJSON = toJSON . unhashed 

instance (FromJSON a, Hashable a) => FromJSON (Hashed a) where
	parseJSON = fmap hashed . parseJSON 

data DataMemored a = DMemored
  { historyLength :: Int
  , grDMemored :: (Gr (Hashed a) (PairSetH a))
} deriving (Generic, ToJSON, FromJSON)

getDataMemored :: (Monad m, Hashable a, Eq a) =>
	M.AdjointT (MemAdjL a) (MemAdjR a) m (DataMemored a)
getDataMemored = do
	i <- adjSnd $ adjSnd $ adjFst $ adjGetEnv
	gr <- adjSnd $ adjFst $ adjGetEnv
	return $ DMemored i gr

setDataMemored :: (Monad m, Hashable a, Eq a) =>
	DataMemored a ->
	M.AdjointT (MemAdjL a) (MemAdjR a) m ()
setDataMemored dm = do
	adjSnd $ adjSnd $ adjSnd $ emptyHistory
	adjSnd $ adjSnd $ adjFst $ adjSetEnv (historyLength dm) (Identity ())
	adjSnd $ adjFst $ adjSetEnv (grDMemored dm) (Identity ())
	adjFst $ adjSetEnv [] (Identity ())

{-}
type HashForest a = Forest (PairSetH a, Hashed a)

type FutuForestAdjL a = (Env (HashForest a)) :.: (MemAdjL a)

type FutuForestAdjR a = (MemAdjR a) :.: (Reader (HashForest a))

addCause :: (Monad m, Hashable a, Eq a) =>
	[(PairSetH a, Hashed a)] -> 
	M.AdjointT (Env (HashForest a)) (Reader (HashForest a)) m ()
addCause = undefined
-}