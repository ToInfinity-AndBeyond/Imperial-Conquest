{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
module AutoTest where

import Submission2
import Test (runTests, test, testFromFile, Test (..), Question (..))

import Lib
import Data.Map (fromList)
import qualified Data.Map as M
import Data.Coerce
import Control.Exception
import GHC.Generics
import Data.Type.Bool
import Data.List
import Data.Maybe
import Data.Function

import Control.Monad
import Control.DeepSeq

import System.IO

deriving instance Eq Order
deriving instance Ord Order

instance Read PageRank where
  readsPrec = coerce (readsPrec @Double)

instance Read PlanetRank where
  readsPrec = coerce (readsPrec @Double)

-- | Question n and its max mark
qn :: String -> Question
qn i = case lookup i [
    ("01", 10),
    ("02", 10),
    ("03", 10),
    ("04", 10),
    ("05", 10),
    ("06", 10),
    ("07", 10),
    ("08", 10),
    ("09", 10),
    ("10", 10)
    ] of
        Just n -> Question (i, n)
        Nothing -> error $ "Question Doens't exist: " ++ i

main :: IO ()
main = runTests $ do
  testFromFile "Find enemy tests" (qn "01") findEnemyPlanet (const (==)) "tests/findEnemyTests.txt"
  testFromFile "Send tests"  (qn "02") (uncurry3 send) (const sameOrders) "tests/sendTests.txt"
  testFromFile "Attack from all tests"  (qn "03") (uncurry attackFromAll) checkAttackFromAll "tests/attackFromAllTests.txt"
  testFromFile "Zerg Rush tests"  (qn "04") (rushWrapper zergRush) checkZergRush "tests/zergRush.txt"
  test "Initialise PageRank tests"  (qn "05") (initPageRank' @Int @Int) (const same) initRankTests
  testFromFile "Next PageRank tests"  (qn "06") (uncurry3 (nextPageRank @PlanetId @_ @GameState)) (const same') "tests/nextPageRank.txt"
  testFromFile "PageRank tests"  (qn "07") (pageRank' @PlanetId @GameState) (const same) "tests/pageRankTests.txt"
  testFromFile "Next PlanetRank tests"  (qn "08") (uncurry3 nextPlanetRank) (const same') "tests/nextPlanetRank.txt"
  testFromFile "PlanetRankRush tests"  (qn "09") planetRankRushWrapper checkPlanetRankRush "tests/planetRankRush.txt"
  testFromFile "TimidRush tests"  (qn "10") timidRushWrapper timidRushCmp "tests/timidRush.txt"

epsilon :: Fractional a => a
epsilon = 0.001

same' :: (Ord a, Fractional a) => a -> a -> Bool
same' a b = abs (a - b) < epsilon

same :: (Ord k, Fractional a, Ord a) => M.Map k a -> M.Map k a -> Bool
same ps1 ps2 = and (M.map (< epsilon) (M.unionWith (\p1 p2 -> abs (p1 - p2)) ps1 ps2))

sameOrders :: [Order] -> [Order] -> Bool
sameOrders os1 os2
  = normalise os1 == normalise os2

normalise :: [Order] -> [Order]
normalise os = map (foldr1 combine) (groupBy ((==) `on` wh) (sortOn wh os))
  where
    wh (Order w _) = w

    combine :: Order -> Order -> Order
    combine (Order w s) (Order _ s') = Order w (s + s')

checkAttackFromAll :: (PlanetId, GameState) -> [Order] -> [Order] -> Bool
checkAttackFromAll (tgtId, gs@(GameState ps ws fs)) _ orders' = all onShortestPath orders && allSent where
  orders :: [Order]
  orders = normalise orders'

  -- By computing the shortest paths on the dual graph from the target, we know
  -- the shortest distance from each planet to the target planet.
  distanceToTarget :: M.Map PlanetId Integer
  distanceToTarget = M.fromList $ (tgtId, 0) : 
     (map (\p -> (target p, weight p)) (shortestPaths (dualGameState gs) tgtId))

  onShortestPath :: Order -> Bool
  onShortestPath (Order wId ships) = maybe False (const True) $
    do (Wormhole (Source s) (Target t) (Turns turns)) <- M.lookup wId ws 
       p@(Planet _ totalShips _) <- M.lookup s ps 
       guard (ourPlanet p)
       guard (totalShips == ships)
       tToTarget <- M.lookup t distanceToTarget
       sToTarget <- M.lookup s distanceToTarget
       guard (toInteger turns + tToTarget == sToTarget)

  allSent :: Bool
  allSent = all (\p -> not (null (filter (fromPlanet p) orders))) ourPlanets where 
    ourPlanets :: [PlanetId]
    ourPlanets = filter (\pId -> ourPlanet (lookupPlanet pId gs)) (M.keys ps)

    fromPlanet :: PlanetId -> Order -> Bool
    fromPlanet pId (Order wId _) = fromMaybe False $
      do (Wormhole (Source s) _ _) <- M.lookup wId ws 
         return (s == pId)

-- A game state with all wormholes' source and target flipped.
dualGameState :: GameState -> GameState
dualGameState (GameState ps ws fs) = GameState ps wsOp fs where
  wsOp = M.map (\(Wormhole (Source s) (Target t) turns) -> Wormhole (Source t) (Target s) turns) ws

type family HasRushTargetField (s :: * -> *) :: Bool where
  HasRushTargetField (D1 _ x) = HasRushTargetField x
  HasRushTargetField (C1 _ x) = HasRushTargetField x
  HasRushTargetField (l :*: r) = HasRushTargetField l || HasRushTargetField r
  HasRushTargetField (l :+: r) = HasRushTargetField l && HasRushTargetField r
  HasRushTargetField (S1 ('MetaSel ('Just "rushTarget") _ _ _) (Rec0 (Maybe PlanetId))) = 'True
  HasRushTargetField _ = 'False

class KnownBool (b :: Bool) where
  boolVal :: Bool

instance KnownBool 'True where
  boolVal = True

instance KnownBool 'False where
  boolVal = False

hasRushTargetField :: Bool
hasRushTargetField = boolVal @(HasRushTargetField (Rep AIState))

uncurry3 :: (a->b->c -> d) -> (a,b,c) -> d
uncurry3 f ~(a, b, c) = f a b c


rushWrapper :: (GameState -> AIState -> ([Order], Log, AIState))
            -> ((GameState, Maybe PlanetId) -> ([Order], Maybe PlanetId))
rushWrapper f (gs, t) = let (os, _, as) = f gs (initialState {rushTarget = t})
                        in (os, rushTarget as)

checkZergRush :: (GameState, Maybe PlanetId) -> ([Order], Maybe PlanetId) -> ([Order], Maybe PlanetId) -> Bool
checkZergRush (gs, p) (osExp, pExp) (osAct, pAct) = (pExp == pAct) && (null osExp == null osExp)

initRankTests = [ M.fromList [(0, 0), (1,0), (2,0), (3,0)] :=> M.fromList [(0, 0.25), (1, 0.25), (2, 0.25), (3, 0.25)]
                , M.fromList [(0, 0), (1,0)] :=> M.fromList [(0, 0.5), (1, 0.5)]
                , M.fromList [(0, 0)] :=> M.fromList [(0, 1)] ]

planetRankRushWrapper :: GameState -> [Order]
planetRankRushWrapper gs = let (o, _, _) = (planetRankRush gs initialState) in o

timidRushWrapper :: GameState -> [Order]
timidRushWrapper gs = let (o, _, _) = (timidRush gs initialState) in o

-- This is deliberately weak since a full check will be expensive and reveal the solution.
checkPlanetRankRush :: GameState -> [Order] -> [Order] -> Bool
checkPlanetRankRush gs osExp osAct = (null osExp == null osAct)

timidRushCmp :: GameState -> [Order] -> [Order] -> Bool
timidRushCmp _ a b = sameOrders a b 
