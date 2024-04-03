module Data.History where

import Data.Sequence as Seq
import System.Random
import Control.Base.Comonad
import Control.Core.Biparam
import Control.Core.Composition
import Data.Functor.Identity

emptyHistory :: Monad m => M.AdjointT (Env (Seq a)) (Reader (Seq a)) m ()
emptyHistory = adjSetEnv empty (Identity ())

addToHistoryLeft :: Monad m => a -> M.AdjointT (Env (Seq a)) (Reader (Seq a)) m ()
addToHistoryLeft = adjBiparam (\a s-> a <| s)

addToHistoryRight :: Monad m => a -> M.AdjointT (Env (Seq a)) (Reader (Seq a)) m ()
addToHistoryRight = adjBiparam (\a s-> s |> a)

getHistoryLeft :: Monad m => M.AdjointT (Env (Seq a)) (Reader (Seq a)) m a
getHistoryLeft = adjState (\(a :<| s)-> return (a,s))

getHistoryRight :: Monad m => M.AdjointT (Env (Seq a)) (Reader (Seq a)) m a
getHistoryRight = adjState (\(s |>: a)-> return (a,s))

viewHistoryLeft :: Monad m => M.AdjointT (Env (Seq a)) (Reader (Seq a)) m a
viewHistoryLeft = adjState (\(a :<| s)-> return (a,a :<| s))

viewHistoryRight :: Monad m => M.AdjointT (Env (Seq a)) (Reader (Seq a)) m a
viewHistoryRight = adjState (\(s |>: a)-> return (a,s |>: a))

getHistoryLength :: Monad m => M.AdjointT (Env (Seq a)) (Reader (Seq a)) m Int
getHistoryLength = fmap Seq.length $ adjGetEnv 

hitoryRondomElement :: (Monad m, MonadIO m) => M.AdjointT (Env (Seq a)) (Reader (Seq a)) m a
hitoryRondomElement = do
	i <- getHistoryLength
	s <- adjGetEnv
	ri <- lift $ randomRIO (0,i)
	return $ index s ri

type HistoryAdjL a = (Env Int) :.: (Env (Seq a))

type HistoryAdjR a = (Reader (Seq a)) :.: (Reader Int)

hitoryCheckLengthLimit :: Monad m => M.AdjointT (HistoryAdjL a) (HistoryAdjR a) m Bool
hitoryCheckLengthLimit = do
	lengthSeq <- adjSnd getHistoryLength
	limitSeq <- adjFst adjGetEnv
	return $ lengthSeq < limitSeq

addToLHistoryLeft :: Monad m => a -> M.AdjointT (HistoryAdjL a) (HistoryAdjR a) m (Maybe a)
addToLHistoryLeft a = do
	adjSnd $ addToHistoryLeft a
	b <- hitoryCheckLengthLimit
	if b
		then return Nothing
		else fmap Just $ adjSnd getHistoryRight

addToLHistoryRight :: Monad m => a -> M.AdjointT (HistoryAdjL a) (HistoryAdjR a) m (Maybe a)
addToLHistoryRight = do
	adjSnd $ addToHistoryRight a
	b <- hitoryCheckLengthLimit
	if b
		then return Nothing
		else fmap Just $ adjSnd getHistoryLength