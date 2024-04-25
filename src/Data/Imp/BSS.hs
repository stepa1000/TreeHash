{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Data.Imp.BSS where

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
import Control.Base.Comonad
import Control.Core.Biparam
import Control.Core.Composition
import Data.Functor.Identity
import Data.History
import Data.NodeHash

instance (MonadFail m, Adjunction f g, Traversable f) => MonadFail (AdjointT f g m) where
	fail = lift . fail

type PWord = (Word8,Word8)

bsToPW :: ByteString -> [PWord]
bsToPW bs = if bs2 == B.empty 
	then []
	else (w1, B.head bs2) : (bsToPW bs2)
	where
		(Just (w1,bs2)) = B.uncons bs

type AdjunctorPWord = M.AdjointT (MemAdjL PWord) (MemAdjR PWord) IO 

lernToMemory :: MVar String -> SettingPWord -> [PWord] -> AdjunctorPWord ()
lernToMemory mvs spw lpw = do
	mapM_ (\pw->do
		lb <- upadteMemored 11 5 [] pw
		lift $ P.print lb
		e <- lift $ tryTakeMVar mvs
		if e == (Just "s")
			then do				
				dm2 <- getDataMemored
				lift $ encodeFile (fileForState spw) dm2
				lift $ print "safe sucsess"
			else return ()
		) lpw

data SettingPWord = SPWord
	{ fileForRead :: FilePath
	, fileForState :: FilePath
}

initEmptyGraph :: SettingPWord -> IO ()
initEmptyGraph spw = do
	m <- try @SomeException $ decodeFileStrict @(DataMemored PWord) (fileForState spw)
	case m of
		(Right (Just _)) -> return ()
		_ -> encodeFile @(DataMemored PWord) (fileForState spw) $ DMemored 11 G.empty

startLTM' :: MVar String -> SettingPWord -> AdjunctorPWord ()
startLTM' mvs spw = do
	setDataMemoredToAdjPWord spw
	bsffr <- lift $ B.readFile (fileForRead spw) 
	lernToMemory mvs spw $ bsToPW bsffr

setDataMemoredToAdjPWord :: SettingPWord -> AdjunctorPWord ()
setDataMemoredToAdjPWord spw =  do
	(Just dm1) <- lift $ decodeFileStrict (fileForState spw) 
	setDataMemored dm1

grShowToFIle :: 
	FilePath -> 
	FilePath ->
	FilePath ->
	FilePath ->
	SettingPWord -> 
	AdjunctorPWord ()
grShowToFIle fp fpap fpcp fpscp spw = do
	setDataMemoredToAdjPWord spw
	str <- adjSnd $ adjFst showGr
	lift $ P.writeFile fp str
	lap <- adjSnd $ adjFst getArtPoints
	lift $ P.writeFile fpap $ show lap
	cp <- adjSnd $ adjFst getComponentsGr
	lift $ P.writeFile fpcp $ show cp
	scp <- adjSnd $ adjFst getSccGr
	lift $ P.writeFile fpscp $ show cp

runPW = void .
		runAdjT Seq.empty .
		runAdjTfst 0 .
		runAdjTfst G.empty .
		runAdjTfst []

grShowToFIleIO :: 
	FilePath -> 
	FilePath -> 
	FilePath ->
	FilePath ->
	SettingPWord -> 
	IO ()
grShowToFIleIO fp fpap fpcp fpscp spw = runPW $ 
	grShowToFIle 
		fp 
		fpap 
		fpcp 
		fpscp
		spw

runStartLTM :: SettingPWord -> IO ()
runStartLTM spw = do
	mvs <- newEmptyMVar 
	forkIO $ runPW $ 
		startLTM' mvs spw
	str <- P.getLine
	f mvs str
	where
		f mvs str = do
			putMVar mvs str
			str2 <- P.getLine
			f mvs str2

u = undefined