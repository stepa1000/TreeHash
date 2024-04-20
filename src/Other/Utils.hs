{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Data.Other.Utils where

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

metric :: [[PackedNeuron]] -> [[PackedNeuron]] -> Double
metric llpn1 llpn2 = 
	sum $
	fmap sum $
	(fmap . fmap) sum $
	(fmap . fmap . fmap) (\(x,y)-> abs $ x - y) $ 
	P.zipWith (P.zipWith P.zip) llpn1 llpn2

getRandomElementList :: [a] -> IO (Maybe a)
getRandomElementList la = do
	let l = P.length la
	i <- randomRIO (0,l)
	return $ la !? i

getRELs :: Int -> [a] -> IO [a]
getRELs i la = fmap catMaybes $ mapM (\_-> getRandomElementList la) [0..i]

pairing :: [a] ->[(a,a)]
pairing [] = []
pairing (x:[]) = []
pairing (x:x2:xs) = (x,xs) : (pairing (x2:[]))