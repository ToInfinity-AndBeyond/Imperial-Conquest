{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}

module Submission2 where

import Control.DeepSeq
import Data.List (unfoldr)
import Data.List
import Data.Map (Map)
import Data.Map qualified as M
import Data.Maybe
import Data.Ord
import GHC.Generics
import Lib
  ( Edge (..),
    Fleet (..),
    Fleets,
    GameState (..),
    Graph (..),
    Growth (..),
    Order (..),
    Owner (..),
    PQueue (..),
    Path (..),
    Planet (..),
    PlanetId (..),
    Planets,
    Player (..),
    Ships (..),
    Source (..),
    Target (..),
    Turns (..),
    Wormhole (..),
    WormholeId (..),
    Wormholes,
    eq,
    gt,
    lt,
    lte,
    maxBy,
    shortestPaths,
    tabulate,
    wormholesFrom,
    wormholesTo,
  )
import Text.Printf

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

logic ::
  Strategy ->
  GameState ->
  AIState ->
  ([Order], Log, AIState)
logic strat gs ai =
  let logic' = case strat of
        Pacifist -> pacifist
        ZergRush -> zergRush
        PlanetRankRush -> planetRankRush
        TimidRush -> timidRush
        Skynet -> skynet
   in logic' gs ai {turn = turn ai + 1}

data AIState = AIState
  { turn :: Turns,
    rushTarget :: Maybe PlanetId,
    rank :: Maybe PlanetRanks
  }
  deriving (Generic)

initialState :: AIState
initialState =
  AIState
    { turn = 0,
      rushTarget = Nothing,
      rank = Nothing
    }

type Log = [String]

pacifist :: GameState -> AIState -> ([Order], Log, AIState)
pacifist _ ai =
  ([], ["This world is illusory. Why fight?"], ai)

enemyPlanet :: Planet -> Bool
enemyPlanet (Planet (Owned Player2) _ _) = True
enemyPlanet _ = False

findEnemyPlanet :: GameState -> Maybe PlanetId
findEnemyPlanet (GameState planets _ _)
  | null target = Nothing
  | otherwise = Just (fst (head target))
  where
    target = M.toList (M.filter enemyPlanet planets)

send ::
  WormholeId ->
  Maybe Ships ->
  GameState ->
  [Order]
send wId mShips st
  | not (ourPlanet planet) = []
  | fromMaybe totalShips mShips > totalShips = [Order wId totalShips]
  | otherwise = [Order wId (fromMaybe totalShips mShips)]
  where
    Wormhole (Source src) _ _ = lookupWormhole wId st
    planet@(Planet owner totalShips _) = lookupPlanet src st

shortestPath ::
  PlanetId ->
  PlanetId ->
  GameState ->
  Maybe (Path (WormholeId, Wormhole))
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
lookupWormhole wId (GameState _ wormholes _) =
  wormholes M.! wId

lookupPlanet :: PlanetId -> GameState -> Planet
lookupPlanet pId (GameState planets _ _) =
  planets M.! pId

attackFromAll :: PlanetId -> GameState -> [Order]
attackFromAll targetId gs = concatMap sendShortestPath shortestPaths
  where
    planetIds = map fst (M.toList (ourPlanets gs))
    shortestPaths = map (\sourceId -> shortestPath sourceId targetId gs) planetIds

    sendShortestPath :: Maybe (Path (WormholeId, Wormhole)) -> [Order]
    sendShortestPath mPath = case mPath of
      Nothing -> []
      Just (Path _ wormholePath) ->
        let wormholeId = fst (last wormholePath)
         in send wormholeId Nothing gs

zergRush :: GameState -> AIState -> ([Order], Log, AIState)
zergRush gs ai
  | isNothing targetPlanetId || ourPlanet (lookupPlanet (fromJust targetPlanetId) gs) =
      ([], ["Zerg Rush Failed"], ai {rushTarget = findEnemyPlanet gs})
  | otherwise = (attackFromAll (fromJust targetPlanetId) gs, zergRushMsg, ai)
  where
    targetPlanetId = rushTarget ai
    zergRushMsg = ["Zerg Rush Initiated: "] ++ [show targetPlanetId]

newtype PageRank = PageRank Double
  deriving (Num, Eq, Ord, Fractional)

type PageRanks pageId = Map pageId PageRank

instance Show PageRank where
  show (PageRank p) = printf "%.4f" p

initPageRanks ::
  (Graph g e pageId, Ord pageId) =>
  g ->
  PageRanks pageId
initPageRanks g =
  M.fromList
    [(p, PageRank (1 / fromIntegral n)) | p <- ps]
  where
    ps = vertices g
    n = length ps

example1 :: [(String, String, Integer)]
example1 =
  [ ("a", "b", 1),
    ("a", "c", 1),
    ("a", "d", 1),
    ("b", "a", 1),
    ("c", "a", 1),
    ("d", "a", 1),
    ("c", "d", 1)
  ]

initPageRank' :: Map pageId a -> PageRanks pageId
initPageRank' ps = M.map (const (1 / fromIntegral (M.size ps))) ps

nextPageRank ::
  ( Ord pageId,
    Edge e pageId,
    Graph g e pageId
  ) =>
  g ->
  PageRanks pageId ->
  pageId ->
  PageRank
nextPageRank g pr i = (1 - d) / n + d * sum [pr M.! j / t j | j <- s i]
  where
    d = 0.85
    n = fromIntegral (length (vertices g))
    t j = fromIntegral (length (edgesFrom g j))
    s i = map source (edgesTo g i)

nextPageRanks ::
  Ord pageId =>
  Graph g e pageId =>
  g ->
  PageRanks pageId ->
  PageRanks pageId
nextPageRanks g pr =
  M.mapWithKey (const . nextPageRank g pr) pr

pageRanks ::
  (Ord pageId, Graph g e pageId) =>
  g ->
  [PageRanks pageId]
pageRanks g = iterate (nextPageRanks g) (initPageRanks g)

pageRank ::
  (Ord pageId, Graph g e pageId) =>
  g ->
  PageRanks pageId
pageRank g = pageRanks g !! 200

nextPageRank' ::
  (Ord pageId, Edge e pageId, Graph g e pageId) =>
  g ->
  PageRanks pageId ->
  PageRank ->
  pageId ->
  PageRank ->
  Maybe PageRank
nextPageRank' g pr k i pri
  | abs (pri - pri') < k = Nothing
  | otherwise = Just pri'
  where
    pri' = nextPageRank g pr i

nextPageRanks' ::
  (Ord pageId, Graph g e pageId) =>
  g ->
  PageRank ->
  PageRanks pageId ->
  Maybe (PageRanks pageId)
nextPageRanks' g k pr =
  case M.mapAccumWithKey nextPageRank'' True pr of
    (True, pr) -> Nothing
    (False, pr') -> Just pr'
  where
    nextPageRank'' converged i pri =
      case nextPageRank' g pr k i pri of
        Nothing -> (converged, pri)
        Just pri' -> (False, pri')

pageRanks' ::
  (Ord pageId, Graph g e pageId) =>
  g ->
  PageRank ->
  [PageRanks pageId]
pageRanks' g k =
  iterateMaybe
    (nextPageRanks' g k)
    (initPageRanks g)

iterateMaybe :: (a -> Maybe a) -> a -> [a]
iterateMaybe f x = x : maybe [] (iterateMaybe f) (f x)

pageRank' ::
  (Ord pageId, Graph g e pageId) =>
  g ->
  PageRanks pageId
pageRank' g = last (take 200 (pageRanks' g k))
  where
    k = 0.0001

example2 :: GameState
example2 = GameState planets wormholes fleets
  where
    planet :: Owner -> Int -> Int -> Planet
    planet o s g = Planet o (Ships s) (Growth g)
    planets =
      M.fromList
        [ (PlanetId 0, planet (Owned Player1) 300 7),
          (PlanetId 1, planet Neutral 200 2),
          (PlanetId 2, planet Neutral 150 3),
          (PlanetId 3, planet Neutral 30 6)
        ]
    wormhole ::
      Int ->
      PlanetId ->
      PlanetId ->
      Int ->
      (WormholeId, Wormhole)
    wormhole w s t ts =
      ( WormholeId w,
        Wormhole (Source s) (Target t) (Turns ts)
      )
    wormholes =
      M.fromList
        [ (wormhole 0 0 1 1),
          (wormhole 1 0 2 1),
          (wormhole 2 0 3 1),
          (wormhole 3 1 0 1),
          (wormhole 4 2 0 1),
          (wormhole 5 3 0 1),
          (wormhole 6 2 3 1)
        ]
    fleets = []

newtype PlanetRank = PlanetRank Double
  deriving (Num, Eq, Ord, Fractional)

type PlanetRanks = Map PlanetId PlanetRank

instance Show PlanetRank where
  show (PlanetRank p) = printf "%.4f" p

initPlanetRanks :: GameState -> PlanetRanks
initPlanetRanks g =
  M.fromList
    [(p, PlanetRank (1 / fromIntegral n)) | p <- ps]
  where
    ps = vertices g
    n = length ps

planetRank :: GameState -> PlanetRanks
planetRank g = planetRanks g !! 200

planetRanks :: GameState -> [PlanetRanks]
planetRanks g =
  iterate (nextPlanetRanks g) (initPlanetRanks g)

nextPlanetRanks :: GameState -> PlanetRanks -> PlanetRanks
nextPlanetRanks g pr =
  M.mapWithKey (const . nextPlanetRank g pr) pr

nextPlanetRank ::
  GameState ->
  PlanetRanks ->
  PlanetId ->
  PlanetRank
nextPlanetRank g@(GameState planets _ _) pr i =
  (1 - d) / n
    + d
      * sum
        [ pr M.! j * growth i / growths j
          | j <- targets i
        ]
  where
    d = 0.85
    n = fromIntegral (length planets)

    growth :: PlanetId -> PlanetRank
    growth i =
      (\(Planet _ _ g) -> fromIntegral g)
        (planets M.! i)
    targets :: PlanetId -> [PlanetId]
    targets i = map target (edgesFrom g i)

    growths :: PlanetId -> PlanetRank
    growths j = sum $ map (growth . source) (edgesTo g j)

checkPlanetRanks :: PlanetRanks -> PlanetRank
checkPlanetRanks = sum . M.elems

planetRankRush :: GameState -> AIState -> ([Order], Log, AIState)
planetRankRush gs ai
  | isNothing (rank ai) = planetRankRush gs (ai {rank = Just (planetRank gs)})
  | isNothing targetPlanetId || ourPlanet (lookupPlanet (fromJust targetPlanetId) gs) =
      planetRankRush gs (ai {rushTarget = nextHighestRankingPlanet gs (fromJust (rank ai))})
  | otherwise = (attackFromAll (fromJust targetPlanetId) gs, planetRankRushMsg, ai)
  where
    targetPlanetId = rushTarget ai
    planetRankRushMsg = ["Planet Rank Rush Initiated: "] ++ [show targetPlanetId]

nextHighestRankingPlanet :: GameState -> PlanetRanks -> Maybe PlanetId
nextHighestRankingPlanet gs pRanks = findNextRankingPlanet (M.toList pRanks) initialId minRank
  where
    initialId = -1
    minRank = 0
    findNextRankingPlanet :: [(PlanetId, PlanetRank)] -> PlanetId -> PlanetRank -> Maybe PlanetId
    findNextRankingPlanet [] currentPid _ = if currentPid == initialId then Nothing else Just currentPid
    findNextRankingPlanet ((pId, pRank) : prs) currentPid maxRank
      | notOurPlanet && pRank > maxRank = findNextRankingPlanet prs pId pRank
      | otherwise = findNextRankingPlanet prs currentPid maxRank
      where
        notOurPlanet = not (ourPlanet (lookupPlanet pId gs))

data PList a = PList (a -> a -> Ordering) [a]

instance PQueue PList where
  toPQueue cmp xs = PList cmp (sortBy cmp xs)

  fromPQueue (PList _ xs) = xs

  empty cmp = PList cmp []

  isEmpty (PList _ xs) = null xs

  priority (PList cmp _) = cmp

  insert x (PList cmp []) = PList cmp [x]
  insert x ps@(PList cmp xs)
    | x <= y = cons x ps
    | otherwise = cons y (Lib.insert x ys)
    where
      (<=) = lte cmp
      (y, ys) = detach ps
      cons x (PList cmp xs) = PList cmp (x : xs)

  extract (PList cmp (x : xs)) = x

  discard (PList cmp (x : xs)) = PList cmp xs

pathFromEdge :: Edge e v => e -> Path e
pathFromEdge e = Path (weight e) [e]

extend :: Edge e v => Path e -> e -> Path e
extend (Path _ []) _ = error "extend: Empty path"
extend (Path d (e:es)) e'
  | target e == source e' = Path (d + weight e') (e':e:es)
  | otherwise = error "extend: Incompatible endpoints"

timidAttackFromAll :: PlanetId -> GameState -> [Order]
timidAttackFromAll targetId gs@(GameState planets wormholes fleets) =
  let sendToPath tId gState pId =
        case easiestPath pId tId gState of
          Just (Path _ paths) -> send (fst (last paths)) Nothing gState
          Nothing             -> []
  
          where
            easiestPath :: PlanetId -> PlanetId -> GameState -> Maybe (Path (WormholeId, Wormhole))
            easiestPath src dst st =
              case filter ((== dst) . target) (easiestPaths st src) of
                []      -> Nothing
                (x : _) -> Just x
  
            easiestPaths :: GameState -> PlanetId -> [Path (WormholeId, Wormhole)]
            easiestPaths gs'@(GameState ps' _ _) v =
              dijkstra gs' (vertices gs' \\ [v]) ps
              where
                ps :: PList (Path (WormholeId, Wormhole))
                ps = toPQueue compareEasiestpath (map pathFromEdge (edgesFrom gs' v))

                dijkstra :: (PQueue pqueue) => GameState -> [PlanetId] -> pqueue (Path (WormholeId, Wormhole)) -> [Path (WormholeId, Wormhole)]
                dijkstra gs' [] ps = []
                dijkstra gs' us ps
                  | isEmpty ps = []
                  | t `elem` us =
                      p : dijkstra gs' (us \\ [t]) (foldr (Lib.insert . extend p) ps' (edgesFrom gs' t))
                  | otherwise = dijkstra gs' us ps'
                  where
                    (p, ps') = detach ps
                    t = target p

                compareEasiestpath :: Path (WormholeId, Wormhole) -> Path (WormholeId, Wormhole) -> Ordering
                compareEasiestpath (Path _ p1@((_, (Wormhole _ (Target pid) _)) : _)) (Path _ p2@((_, (Wormhole _ (Target pid') _)) : _)) =
                  compare (numOfShips p1) (numOfShips p2) <> compare pid' pid  

                numOfShips :: [(WormholeId, Wormhole)] -> Int
                numOfShips = sum . map (\(_, Wormhole _ (Target pId) _) ->
                  case M.lookup pId ps' of
                    Just (Planet (Owned Player1) _ _) -> 0
                    Just (Planet _ (Ships s') _) -> s'
                    _ -> 0)
  
  in concatMap (sendToPath targetId gs) (M.keys (ourPlanets gs))


timidRush :: GameState -> AIState -> ([Order], Log, AIState)
timidRush gs ai
  | isNothing (rank ai) = timidRush gs (ai {rank = Just (planetRank gs)})
  | isNothing targetPlanetId || ourPlanet (lookupPlanet (fromJust targetPlanetId) gs) =
      timidRush gs (ai {rushTarget = nextHighestRankingPlanet gs (fromJust (rank ai))})
  | otherwise = (timidAttackFromAll (fromJust targetPlanetId) gs, timidRushMsg, ai)
  where
    targetPlanetId = rushTarget ai
    timidRushMsg = ["Timid Rush Initiated: "] ++ [show targetPlanetId]

skynet :: GameState -> AIState -> ([Order], Log, AIState)
skynet _ _ = undefined

deriving instance Generic PlanetRank

deriving instance Generic PageRank

instance NFData PageRank

instance NFData PlanetRank
