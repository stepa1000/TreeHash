module Main (main) where

import Preluse as Pre
import Data.Sequence as Seq
import System.Random
import Data.Hashable
import Data.HashSet as Set
import Data.HashMap.Lazy as Map
import Data.Tree as Tree
import Data.Maybe
import Data.Graph.Inductive.PatriciaTree as G
import Data.ByteString as B
import Data.Word
import Data.Aeson as Aeson
import Control.Base.Comonad
import Control.Core.Biparam
import Control.Core.Composition
import Data.Functor.Identity
import Data.History
import Data.NodeHash
import Data.Imp.BSS

main :: IO ()
main = do
	initEmptyGraph sspw
	runStartLTM sspw

sspw = SPWord "data/PEPN.fb2" "data/hashGraph.json"
