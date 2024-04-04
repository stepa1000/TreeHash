module Data.NodeHash where

import Preluse as Pre
import Data.Sequence as Seq
import System.Random
import Data.Hashable
import Data.HashSet as Set
import Data.HashMap.Lazy as Map
import Data.Maybe
import Data.Graph.Inductive.PatriciaTree as G
import Control.Base.Comonad
import Control.Core.Biparam
import Control.Core.Composition
import Data.Functor.Identity
import Data.History

data NodeHash a = NodeH (HashSet (Hashed a)) (HashSet (Hashed a)) (Hashed a) (Hashed a)

type SeqHash a = Seq (NodeHash a)

generateNode :: (Monad m, MonadIO m, Hashable a, Eq a) => 
  Int -> 
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
	when (not $ map.member psh mE2) $ do
		gr <- adjGetEnv
		let mn1 = Map.lookup nh mN2
		let lhn = grtLastHesh nh
		let mn2 = Map.lookup lhn mN2
		mapM (\(x,y)-> do
			adjSetEnv (insEdge (y,x,psh)) (Identity ())
			) (do
			n1 <- mn1
			n2 <- mn2
			return (n1,n2)
			)

stepMemoring :: (Monad m, MonadIO m, Hashable a, Eq a) => 
  Int -> 
  [Hashed a] -> 
  a -> 
  M.AdjointT (HGrAdjL a) (HGrAdjR a) m (NodeHash a)
stepMemoring i existHash nextA =
	nh <- adjSnd $ generateNode i existHash nextA
	adjFst $ setNodeHashToGr nh

data Memored = Memored
	{ listMemored :: [Hashed a]
	, setMemored :: PairSetH a
	, lastHesh :: Hashed a
	, mising :: Int
}

type MaxMising = Int

type LMemored = [Memored]

type MemAdjL = (Env LMemored) :.: (HGrAdjL a)

type MemAdjR = (HGrAdjR a) :.: (Reader LMemored)

upMemored :: (Monad m, Hashable a, Eq a) => 
	MaxMising ->
	M.AdjointT (HGrAdjL a) (HGrAdjR a) m [(PairSetH a, Hashed a)]
upMemored mm = do
	vh <- adjSnd $ adjSnd $ adjSnd $ fmap hashed viewHistoryLeft
	gri <- adjSnd $ getInfoHGr
	lmem <- adjFst $ adjGetEnv
	lmem2 <- mapM (\mem-> do
		if member vh (fst $ setMemored mem) && not (member vh (snd $ setMemored mem))
			then return $ mem {listMemored = vh:(listMemored mem)}
			else return $ mem {mising = (mising mem) + 1}
		) lmem
	lmem3 <- fmap catMaybes $ mapM (\mem->do
		if ((mising mem) > mm || 
			(P.length (listMemored mem) >= Set.size (fst $ setMemored mem)) ||
			(member vh (snd $ setMemored mem))
			)
			then return Nothing
			else return $ Just mm
		) lmem2
	r <- mapM (\mem->do
		
		) lmem3
