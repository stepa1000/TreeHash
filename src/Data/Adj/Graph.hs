{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Data.Adj.Graph where

import Prelude as P
import Data.Sequence as Seq
import System.Random
import Data.Hashable
import Data.HashSet as Set
import Data.HashMap.Lazy as Map
import Data.Tree as Tree
import Data.Maybe
import Data.Graph.Inductive.PatriciaTree as G
import Data.Graph.Inductive.Graph as G
import Data.Graph.Inductive.Query.DFS as G
import Data.Graph.Inductive.Query.ArtPoint as G
import Data.ByteString as B
import Data.Word
import Data.Aeson as Aeson
import Debug.Trace
import Control.Monad.Trans.Adjoint as M
import Data.Functor.Adjunction
import Control.Monad.Reader
import Control.Monad
import Control.Exception
import Control.Comonad.Env
import Control.Monad.IO.Class
import Control.Concurrent.MVar
import Control.Concurrent
import Control.Logger
import GHC.Generics
import AI.BPANN
import Control.Base.Comonad
import Control.Core.Biparam
import Control.Core.Composition
import Data.Functor.Identity
import Data.History
import Other.Utils

getInfoHGr ::(Monad m, Hashable a, Hashable b, Eq a) => 
	M.AdjointT 
		(Env (Gr a b)) 
		(Reader (Gr a b)) 
		m 
		(HashMap a Node, HashMap b [(Node,Node)])
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


showGr :: (Monad m, Hashable a, Eq a, Show a, Show b) =>
	M.AdjointT 
		(Env (Gr a b)) 
		(Reader (Gr a b)) 
		m 
		String
showGr = do
	gr <- adjGetEnv
	return $ prettify gr

getArtPoints :: (Monad m, Hashable a, Eq a, Show a) =>
	M.AdjointT 
		(Env (Gr a b)) 
		(Reader (Gr a b)) 
		m 
		[a]
getArtPoints = do
	gr <- adjGetEnv
	let lp = catMaybes $ fmap (\p-> G.lab gr p) $ G.ap gr
	return lp

getComponentsGr :: (Monad m, Hashable a, Eq a, Show a) =>
	M.AdjointT 
		(Env (Gr a b)) 
		(Reader (Gr a b)) 
		m 
		[[a]]
getComponentsGr = do
	gr <- adjGetEnv
	let lp = fmap catMaybes $ (fmap . fmap) (\p-> G.lab gr p) $ G.components gr
	return lp 

getSccGr :: (Monad m, Hashable a, Eq a, Show a) =>
	M.AdjointT 
		(Env (Gr a b)) 
		(Reader (Gr a b)) 
		m 
		[[a]]
getSccGr = do
	gr <- adjGetEnv
	let lp = fmap catMaybes $ (fmap . fmap) (\p-> G.lab gr p) $ G.scc gr
	return lp 

getSccGrNode :: (Monad m, Hashable a, Eq a) =>
	M.AdjointT 
		(Env (Gr a b)) 
		(Reader (Gr a b)) 
		m 
		[[Node]]
getSccGrNode = do
	gr <- adjGetEnv
	let lp = G.scc gr
	return lp

getSccGrGraph :: (Monad m, Hashable a, Eq a) =>
	M.AdjointT 
		(Env (Gr a b)) 
		(Reader (Gr a b)) 
		m 
		[(Gr a b)]
getSccGrGraph = do
	gr <- adjGetEnv
	ln <- getSccGrNode
	return $ fmap (\l->subgraph l gr) ln

sccArtPoint :: Gr a b -> [Gr a b]
sccArtPoint gr 
	| G.isEmpty gr = []
	| P.length (labNodes gr) == 1 = [gr]
sccArtPoint gr = (f $ P.foldr (\a b->G.delNode a b) gr artP)
	where
		f grn 
			| G.isEmpty grn = [] 
			| P.length (labNodes grn) == 1 = [grn]
		f grn = join $ fmap (\l-> sccArtPoint $ subgraph l grn) lp
			where
				lp = G.scc grn
		artP = G.ap gr


getTopsort :: (Monad m, Hashable a, Eq a, Show a) =>
	M.AdjointT 
		(Env (Gr a b)) 
		(Reader (Gr a b)) 
		m 
		[a]
getTopsort = do
	gr <- adjGetEnv
	return $ topsort' gr

getDffA :: (Monad m, Hashable a, Eq a, Show a) =>
	M.AdjointT 
		(Env (Gr a b)) 
		(Reader (Gr a b)) 
		m 
		[Tree a]
getDffA = do
	gr <- adjGetEnv
	return $ dffWith' lab' gr

randomPath :: (Monad m, MonadIO m, Hashable a, Eq a) =>
	Gr a b ->
	m [a]
randomPath ga = do
	let ta = dffWith' lab' ga
	fmap join $ mapM f ta
	where
		f (Node a []) = return [a]
		f (Node a lta) = do
			mrta <- liftIO $ getRandomElementList lta
			mlra <- fmap (join . maybeToList) $ mapM f mrta
			return $ a : mlra

