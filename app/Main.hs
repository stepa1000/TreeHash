{-# LANGUAGE TypeOperators #-}

module Main (main) where

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
import Data.NodeHash
import Data.Imp.BSS
import Data.Imp.NNS

main :: IO ()
main = do
	initNNS snn
	runLTNN snn

snn = SettingNN
	"data/PEPN.fb2"
	"data/StateNN.json"
	"data/Log.text"
	"data/gr"

{-}
	initEmptyGraph sspw
	grShowToFIleIO 
		"data/GraphShow" 
		"data/ShowAP" 
		"data/ShowComponent"
		"data/ShowStrongComponent"
		sspw
	print "post initEmptyGraph"
	runStartLTM sspw

sspw = SPWord "data/PEPN.fb2" "data/hashGraph.json"
-}
