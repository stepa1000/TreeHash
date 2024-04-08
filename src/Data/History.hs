{-# LANGUAGE TypeOperators #-}

module Data.History where

import Data.Sequence as Seq
import System.Random
import Control.Monad.Trans.Adjoint as M
import Control.Monad.Reader
import Control.Comonad.Env
import Control.Monad.IO.Class
import GHC.Generics
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

getHistoryLeft :: Monad m => M.AdjointT (Env (Seq a)) (Reader (Seq a)) m (Maybe a)
getHistoryLeft = adjState (\ss-> case ss of
	(a :<| s) -> return (Just a,s)
	_ -> return (Nothing, ss)
	)

getHistoryRight :: Monad m => M.AdjointT (Env (Seq a)) (Reader (Seq a)) m (Maybe a)
getHistoryRight = adjState (\ss -> case ss of
	(s :|> a) -> return (Just a,s)
	_ -> return (Nothing, ss)
	)
viewHistoryLeft :: Monad m => M.AdjointT (Env (Seq a)) (Reader (Seq a)) m (Maybe a)
viewHistoryLeft = adjState (\ss -> case ss of
	(a :<| s) -> return (Just a,a :<| s)
	_ -> return (Nothing, ss)
	)

viewHistoryRight :: Monad m => M.AdjointT (Env (Seq a)) (Reader (Seq a)) m (Maybe a)
viewHistoryRight = adjState (\ss -> case ss of
	(s :|> a) -> return (Just a,s :|> a)
	_ -> return (Nothing, ss)
	)

getHistoryLength :: Monad m => M.AdjointT (Env (Seq a)) (Reader (Seq a)) m Int
getHistoryLength = fmap Seq.length $ adjGetEnv 

hitoryRondomElement :: (Monad m, MonadIO m) => M.AdjointT (Env (Seq a)) (Reader (Seq a)) m (Maybe a)
hitoryRondomElement = do
	i <- getHistoryLength
	s <- adjGetEnv
	lift $ liftIO $ print i
	ri <- lift $ randomRIO (0,i)
	lift $ liftIO $ print $ "random:" ++ show ri
	return $ Seq.lookup ri s

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
		else adjSnd getHistoryRight

addToLHistoryRight :: Monad m => a -> M.AdjointT (HistoryAdjL a) (HistoryAdjR a) m (Maybe a)
addToLHistoryRight a = do
	adjSnd $ addToHistoryRight a
	b <- hitoryCheckLengthLimit
	if b
		then return Nothing
		else adjSnd getHistoryLeft