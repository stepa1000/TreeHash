module Data.NodeHash where

import Preluse as Pre
import Data.Sequence as Seq
import System.Random
import Data.Hashable
import Data.HashSet as Set
import Data.HashMap.Lazy as Map
import Data.Graph.Inductive.PatriciaTree as G
import Control.Base.Comonad
import Control.Core.Biparam
import Control.Core.Composition
import Data.Functor.Identity
import Data.History

data NodeHash a = NodeH (HashSet (Hashed a)) (HashSet (Hashed a)) (Hashed a) 

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
	return $ NodeH srTrue srFalse (hashed nextA)

type PairSetH a = (HashSet (Hashed a), HashSet (Hashed a))

type HGrAdjL a = (Env (Gr (Hashed a) (PairSetH a))) :.: (HistoryAdjL a)

type HGrAdjR a = (HistoryAdjR a) :.: (Reader (Gr (Hashed a) (PairSetH a)))

getHashNode :: NodeHash a -> Hashed a
getHashNode (NodeH _ _ h) = h

getPairSetH :: NodeHash a -> PairSetH a
getPairSetH (NodeH x y _) = (x,y)

getInfoHGr ::(Monad m, Hashable a, Eq a) => 
	M.AdjointT 
		(Env (Gr (Hashed a) (PairSetH a))) 
		(Reader (Gr (Hashed a) (PairSetH a))) 
		m 
		(HashMap (Hashed a) Node, HashMap (PairSetH a) (Node,Node))
getInfoHGr = do
	gr <- adjGetEnv
	return $ ufold (\(lbnl,n,a,lbnr) (x,y)-> 
			( x <> (Map.singelton a n)
			, y <> 
				( fold $ fmap (\ (b,n2) -> Map.singleton b (n2,n)) lbnl 
				) <>
				( fold $ fmap (\ (b,n2) -> Map.singleton b (n,n2)) lbnr
				)
			)
		) (Map.empty, Map.empty) gr

setNodeHashToGr :: (Monad m, Hashable a, Eq a) => 
	NodeHash a ->
	Hashed a ->
	M.AdjointT 
		(Env (Gr (Hashed a) (PairSetH a))) 
		(Reader (Gr (Hashed a) (PairSetH a))) 
		m 
		()
setNodeHashToGr nh lhn = do
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
		let mn2 = Map.lookup lhn mN2
		mapM (\(x,y)-> do
			adjSetEnv (insEdge (y,x,psh)) (Identity ())
			) (do
			n1 <- mn1
			n2 <- mn2
			return (n1,n2)
			)
