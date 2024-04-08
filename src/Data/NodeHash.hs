module Data.NodeHash where

import Preluse as Pre
import Data.Sequence as Seq
import System.Random
import Data.Hashable
import Data.HashSet as Set
import Data.HashMap.Lazy as Map
import Data.Tree as Tree
import Data.Maybe
import Data.Graph.Inductive.PatriciaTree as G
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
  M.AdjointT (HistoryAdjL a) (HistoryAdjR a) m (NodeHash a)
generateNode i existHash nextA = do
	srTrue <- fmap fold $ mapM (\_->fmap (Set.singleton . hashed) $ adjSnd hitoryRondomElement) [0..i]
	let le = Pre.length existHesh
	srFalse <- fmap fold $ mapM (\_->do
		ri <- lift $ randomRIO (0,le)
		let rs = existHash ! ri
		if not $ member rs srTrue
			then return $ Set.singleton ri 
			else return Set.empty 
		) [0..i]
	vh <- adjSnd $ fmap hashed viewHistoryLeft
	return $ NodeH srTrue srFalse vh (hashed nextA)

type PairSetH a = (HashSet (Hashed a), HashSet (Hashed a))

type HGrAdjL a = (Env (Gr (Hashed a) (PairSetH a))) :.: (HistoryAdjL a)

type HGrAdjR a = (HistoryAdjR a) :.: (Reader (Gr (Hashed a) (PairSetH a)))

getHashNode :: NodeHash a -> Hashed a
getHashNode (NodeH _ _ _ h) = h

grtLastHesh :: NodeHash a -> Hashed a
grtLastHesh (NodeH _ _ h _) = h

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
			( x <> (Map.singelton a n)
			, y <> 
				( P.foldl (\ m1 m2 -> unionWith (P.++) m1 m2) Map.empry $ 
					fmap (\ (b,n2) -> Map.singleton b [(n2,n)]) lbnl 
				) <>
				( P.foldl (\ m1 m2 -> unionWith (P.++) m1 m2) Map.empry $ 
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
setNodeHashToGr nh = do
	(mN, mE) <- getInfoHGr
	let hn = getHashNode nh
	let psh = getPairSetH nh
	when (not $ Map.member hn mN) $ do
		gr <- adjGetEnv
		let [nn] = newNodes 1 gr
		let ngr = insNode (nn,hn)
		adjSetEnv ngr (Identity ())
	(mN2, mE2) <- getInfoHGr
	let mn1 = Map.lookup nh mN2
	let lhn = getLastHesh nh
	let mn2 = Map.lookup lhn mN2
	mapM_ (\(x,y)-> do
		grn <- adjGetEnv
		when (not $ hasLEdge gtn (y,x,psh)) $ do 
			adjSetEnv (insEdge (y,x,psh) grn) (Identity ())
		) (do
		n1 <- mn1
		n2 <- mn2
		return (n1,n2)
		)

stepMemoring :: (Monad m, MonadIO m, Hashable a, Eq a) => 
  SizeSet -> 
  [Hashed a] -> 
  a -> 
  M.AdjointT (HGrAdjL a) (HGrAdjR a) m (NodeHash a)
stepMemoring i existHash nextA =
	nh <- adjSnd $ generateNode i existHash nextA
	adjFst $ setNodeHashToGr nh

data Memored a = Memored
	{ listMemored :: [Hashed a]
	, setMemored :: PairSetH a
	, lastHesh :: Hashed a
	, nextHash :: Hashed a
	, mising :: Int
}

type MaxMising = Int

type LMemored = [Memored]

type MemAdjL = (Env (LMemored a)) :.: (HGrAdjL a)

type MemAdjR = (HGrAdjR a) :.: (Reader (LMemored a))

upMemored :: (Monad m, Hashable a, Eq a) => 
	MaxMising ->
	M.AdjointT (MemAdjL a) (MemAdjR a) m [(PairSetH a, Hashed a)]
upMemored mm = do
	vh <- adjSnd $ adjSnd $ adjSnd $ fmap hashed viewHistoryLeft
	gri <- adjSnd $ adjFst getInfoHGr
	gr <- adjSnd $ adjFst adjGetEnv
	lmem <- adjFst $ adjGetEnv
	lmem2 <- mapM (\mem-> do
		if member vh (fst $ setMemored mem) && not (member vh (snd $ setMemored mem))
			then return $ mem {listMemored = vh:(listMemored mem)}
			else return $ mem {mising = (mising mem) + 1}
		) lmem
	lmem3 <- fmap catMaybes $ mapM (\mem->do
		if ((mising mem) > mm || 
			-- (P.length (listMemored mem) >= Set.size (fst $ setMemored mem)) ||
			(member vh (snd $ setMemored mem))
			)
			then return Nothing
			else return $ Just mm
		) lmem2
	let addLMem = foldMapWithKey (\k v-> fmap (\(x,y)->Memored [vh] k (lab' $ context gr x) (lab' $ context gr y) 0) v) $ snd gri
	adjFst $ adjSetEnv (lmem3 ++ addLMem) (Identity ())
	mapM (\mem->do
		if vh == (lastHesh mem)
			then if fromList (listMemored mem) == (fst $ setMemored mem)
				then return (setMemored mem,nextHash mem)
		) lmem2

upadteMemored :: (Monad m, Hashable a, Eq a) => 
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
	adjSnd $ adjSnd $ adjSnd $ addToLHistoryLeft a
	return lb

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