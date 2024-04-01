module Data.NodeHash where

import Preluse as Pre
import Data.Sequence as Seq
import System.Random
import Data.Hashable
import Data.HashSet as Set
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



