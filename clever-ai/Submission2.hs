
{-#  LANGUAGE GeneralizedNewtypeDeriving  #-}
{-#  LANGUAGE StandaloneDeriving  #-}
{-#  LANGUAGE DeriveGeneric  #-}
{-#  LANGUAGE FlexibleInstances  #-}
{-#  LANGUAGE MultiParamTypeClasses  #-}

module Submission2 where
import Lib

  hiding (example1, example2, example3, lookupPlanet)
import qualified Data.Map as M
import Data.Map (Map)
import Data.List (unfoldr)
import Data.List
import Data.Maybe
import Text.Printf
import Control.DeepSeq
import GHC.Generics
import Data.Ord

deriving instance (Integral Growth)
deriving instance (Enum Growth)
deriving instance (Real Growth)

data Strategy
  = Pacifist
  | ZergRush
  | PlanetRankRush
  | TimidRush
  | Skynet
  deriving (Enum, Bounded, Show, Read)

logic :: Strategy -> GameState -> AIState 
      -> ([Order], Log, AIState)
logic strat gs ai
  = let logic' = case strat of
          Pacifist       -> pacifist
          ZergRush       -> zergRush
          PlanetRankRush -> planetRankRush
          TimidRush      -> timidRush
          Skynet         -> skynet
    in logic' gs ai {turn = turn ai + 1}

data AIState = AIState
  { turn       :: Turns
  , rushTarget :: Maybe PlanetId
  } deriving Generic
 
initialState :: AIState
initialState = AIState
  { turn = 0
  , rushTarget = Nothing
  }

type Log = [String]

pacifist :: GameState -> AIState -> ([Order], Log, AIState)
pacifist _ ai =
  ([], ["This world is illusory. Why fight?"], ai)

enemyPlanet :: Planet -> Bool
enemyPlanet (Planet (Owned Player2) _ _) = True
enemyPlanet _                            = False

findEnemyPlanet :: GameState -> Maybe PlanetId
findEnemyPlanet = undefined

send :: WormholeId -> Maybe Ships -> GameState 
     -> [Order]
send wId mShips st = undefined where
  Wormhole (Source src) _ _ = lookupWormhole wId st
  planet@(Planet _ totalShips _) = lookupPlanet src st

shortestPath :: PlanetId -> PlanetId -> GameState 
             -> Maybe (Path (WormholeId, Wormhole))
shortestPath src dst st = 
  case filter ((== dst) . target) (shortestPaths st src) of
    [] -> Nothing
    (x : _) -> Just x

ourPlanet :: Planet -> Bool
ourPlanet (Planet (Owned Player1) _ _) = True
ourPlanet _ = False

ourPlanets :: GameState -> Planets
ourPlanets (GameState ps _ _) = M.filter ourPlanet ps

lookupWormhole :: WormholeId -> GameState -> Wormhole
lookupWormhole wId (GameState _ wormholes _)
  = wormholes M.! wId

lookupPlanet :: PlanetId -> GameState -> Planet
lookupPlanet pId (GameState planets _ _)
  = planets M.! pId

attackFromAll :: PlanetId -> GameState -> [Order]
attackFromAll targetId gs = undefined

zergRush :: GameState -> AIState 
         -> ([Order], Log, AIState)
zergRush gs ai = undefined

newtype PageRank = PageRank Double
  deriving (Num, Eq, Ord, Fractional)
 
type PageRanks pageId = Map pageId PageRank

instance Show PageRank where
  show (PageRank p) = printf "%.4f" p

initPageRanks :: (Graph g e pageId, Ord pageId) 
              => g -> PageRanks pageId
initPageRanks g = M.fromList 
  [ (p, PageRank (1 / fromIntegral n)) | p <- ps ]
  where ps = vertices g
        n  = length ps

example1 :: [(String, String, Integer)]
example1 = [("a","b",1), ("a","c",1), ("a","d",1),
            ("b","a",1), ("c","a",1), ("d","a",1), 
            ("c","d",1)]

initPageRank' :: Map pageId a -> PageRanks pageId
initPageRank' = undefined

nextPageRank :: (Ord pageId, Edge e pageId,
                 Graph g e pageId) 
             => g -> PageRanks pageId -> pageId 
             -> PageRank
nextPageRank g pr i = undefined
  where
    d = 0.85

nextPageRanks :: Ord pageId => Graph g e pageId =>
  g -> PageRanks pageId -> PageRanks pageId
nextPageRanks g pr = 
  M.mapWithKey (const . nextPageRank g pr) pr

pageRanks :: (Ord pageId, Graph g e pageId)
          => g -> [PageRanks pageId]
pageRanks g = iterate (nextPageRanks g) (initPageRanks g)

pageRank :: (Ord pageId, Graph g e pageId)
         => g -> PageRanks pageId
pageRank g = pageRanks g !! 200

nextPageRank' :: (Ord pageId, Edge e pageId, Graph g e pageId)
              => g -> PageRanks pageId -> PageRank -> pageId 
              -> PageRank -> Maybe PageRank
nextPageRank' g pr k i pri
  | abs (pri - pri') < k  = Nothing
  | otherwise             = Just pri'
 where
   pri' = nextPageRank g pr i

nextPageRanks' :: (Ord pageId, Graph g e pageId) =>
  g -> PageRank -> PageRanks pageId ->
  Maybe (PageRanks pageId)
nextPageRanks' g k pr =
  case M.mapAccumWithKey nextPageRank'' True pr of
    (True,  pr)  -> Nothing
    (False, pr') -> Just pr'
  where
    nextPageRank'' converged i pri =
      case nextPageRank' g pr k i pri of
        Nothing   -> (converged, pri)
        Just pri' -> (False, pri')

pageRanks' :: (Ord pageId, Graph g e pageId)
           => g -> PageRank -> [PageRanks pageId]
pageRanks' g k = iterateMaybe (nextPageRanks' g k) 
                              (initPageRanks g)
 
iterateMaybe :: (a -> Maybe a) -> a -> [a]
iterateMaybe f x = x : maybe [] (iterateMaybe f) (f x)

pageRank' :: (Ord pageId, Graph g e pageId) 
          => g -> PageRanks pageId
pageRank' g = undefined
  where
    k = 0.0001

example2 :: GameState
example2 = GameState planets wormholes fleets where
  planet :: Owner -> Int -> Int -> Planet
  planet o s g = Planet o (Ships s) (Growth g)
  planets = M.fromList
    [ (PlanetId 0, planet (Owned Player1) 300 7)
    , (PlanetId 1, planet Neutral 200 2)
    , (PlanetId 2, planet Neutral 150 3)
    , (PlanetId 3, planet Neutral 30  6)
    ]
  wormhole :: Int -> PlanetId -> PlanetId 
           -> Int -> (WormholeId, Wormhole)
  wormhole w s t ts = (WormholeId w, 
    Wormhole (Source s) (Target t) (Turns ts))
  wormholes = M.fromList
    [ (wormhole 0 0 1 1), (wormhole 1 0 2 1)
    , (wormhole 2 0 3 1), (wormhole 3 1 0 1)
    , (wormhole 4 2 0 1), (wormhole 5 3 0 1)
    , (wormhole 6 2 3 1)
    ]
  fleets = []

newtype PlanetRank = PlanetRank Double
  deriving (Num, Eq, Ord, Fractional)
 
type PlanetRanks = Map PlanetId PlanetRank
 
instance Show PlanetRank where
  show (PlanetRank p) = printf "%.4f" p

initPlanetRanks :: GameState -> PlanetRanks
initPlanetRanks g = M.fromList 
  [ (p, PlanetRank (1 / fromIntegral n)) | p <- ps ]
  where ps = vertices g
        n  = length ps

planetRank :: GameState -> PlanetRanks
planetRank g = planetRanks g !! 200
 
planetRanks :: GameState -> [PlanetRanks]
planetRanks g =
  iterate (nextPlanetRanks g) (initPlanetRanks g)

nextPlanetRanks :: GameState -> PlanetRanks -> PlanetRanks
nextPlanetRanks g pr = 
  M.mapWithKey (const . nextPlanetRank g pr) pr

nextPlanetRank :: GameState -> PlanetRanks 
               -> PlanetId -> PlanetRank
nextPlanetRank g@(GameState planets _ _) pr i = 
  (1 - d) / n + d * sum [pr M.! j * growth i / growths j 
                        | j <- targets i]
  where
    d   = 0.85
    n   = fromIntegral (length planets)

    growth :: PlanetId -> PlanetRank
    growth i  = (\(Planet _ _ g) -> fromIntegral g) 
                                    (planets M.! i)
    targets :: PlanetId -> [PlanetId]
    targets i = undefined
 
    growths :: PlanetId -> PlanetRank
    growths j = undefined

checkPlanetRanks :: PlanetRanks -> PlanetRank
checkPlanetRanks = sum . M.elems

planetRankRush :: GameState -> AIState 
               -> ([Order], Log, AIState)
planetRankRush _ _ = undefined

timidAttackFromAll :: PlanetId -> GameState -> [Order]
timidAttackFromAll = undefined

timidRush :: GameState -> AIState
          -> ([Order], Log, AIState)
timidRush gs ai = undefined

skynet :: GameState -> AIState -> ([Order],Log,AIState)
skynet _ _ = undefined

deriving instance Generic PlanetRank
deriving instance Generic PageRank
 
instance NFData PageRank
instance NFData PlanetRank
