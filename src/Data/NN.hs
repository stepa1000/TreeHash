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
import Control.Base.Comonad
import Control.Core.Biparam
import Control.Core.Composition
import Data.Functor.Identity
import Data.History
import Data.NodeHash

type Hash = Int

type LNetwork = [Network]

type Layers = [Int]

type AdjNetworkL = (Env LNetwork) :.: (Env Layers)

type AdjNetworkR = (Reader Layers) :.: (Reader LNetwork) 

creatRandomNetworksAdj :: (Monad m, MonadIO m) => 
	Int ->
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
	toLD :: a -> [Double]
	fromLD :: [Double] -> a -> a

calculateAdjLD :: (Monad m, MonadIO m, ListDoubled a) => 
	a ->
	M.AdjointT 
		AdjNetworkL 
		AdjNetworkR
		m
		[(HashNN,a)]
calculateAdjLD a = do
	lhld <- calculateAdj $ toLD a
	return $ fmap (\(h,ld) -> (h, fmap (\x-> fromLD x a) ld)) lhld

trainAdjLD :: (Monad m, MonadIO m, Hashable a, Eq a) => 
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
	trainAdj p pe $ P.replicate i (toLD x, toLD y)

type HashNN = Hash

type NNGrAdjL a = (Env (Gr (Hashed a) HashNN)) :.: AdjNetworkL

type NNGrAdjR a = AdjNetworkR :.: (Reader (Gr (Hashed a) HashNN))

getRandomElementList :: [a] -> IO (Maybe a)
getRandomElementList la = do
	let l = P.length la
	i <- randomRIO (0,l)
	return $ la !? i

getRELs :: Int -> [a] -> IO [a]
getRELs i la = fmap catMaybes $ mapM (\_-> getRandomElementList la) [0..i]

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

upgradingNNGr :: (Monad m, MonadIO m, Hashable a, Eq a) => 
	(a,a)
	SerchInt ->
	UpgradingInt ->
	M.AdjointT 
		(NNGrAdjL a) 
		(NNGrAdjR a)
		m 
		()
upgradingNNGr si ui = do
	mapM (\_-> do
		ln <- adjFst $ fmap join $ getSccGrNode
		gr <- adjFst $ adjGetEnv
		adjFst $ adjSetEnv (subgraph ln gr) (Identity ())
		updatingNNGr si
		) [0..ui]

type HashSccGr = Hash

type IntMapPrimeNN = IntMap ([[PackedNeuron]],[HashSccGr])

type NNPrimeAdjL a = (Env IntMapPrimeNN) :.: (NNGrAdjL a)

type NNPrimeAdjR a = (NNGrAdjR a) :.: (Reader IntMapPrimeNN)

safeNNScc :: (Monad m, MonadIO m, Hashable a, Eq a) => 
	M.AdjointT 
		(NNPrimeAdjL a) 
		(NNPrimeAdjR a)
		m 
		()
safeNNScc = do
	ln <- adjSnd $ adjSnd $ adjFst $ adjGetEnv
	impnn <- fmap fold $ mapM (\n->do
		let pnn = packNetwork n
		return $ singleton (hash pnn) pnn
		)
	im <- adjFst $ adjGetEnv
	adjFst $ adjSetEnv (IMap.union im impnn) (Identity ())

type NNSccGrAdjL' a = (Env (Gr (Gr (Hashed a) HashNN) HashNN)) :.: AdjNetworkL

type NNSccGrAdjR' a = AdjNetworkR :.: (Reader (Gr (Gr (Hashed a) HashNN) HashNN))