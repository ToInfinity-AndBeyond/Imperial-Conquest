{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}

module Map
  ( Point
  , draw
  , drawBG
  , drawMap
  , resetCol
  , randomMap
  , moveCursor
  , mapToScreen
  , setP1Col
  , setP2Col
  , append
  , randIO
  )
  where

import           Control.Monad
import           Control.Monad.State
import           Data.List (sortOn, unfoldr, sort)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe (fromJust)
import qualified System.Random
import           System.Random (StdGen, Random)
import           Data.ByteString.Builder
import           Data.Bifunctor (bimap)
import           Data.Semigroup (Arg(..), Min(..))
import           System.IO

import Data.Array

import           Lib

type Point = (Int, Int)

type PPlanet = (Point, Planet)

type Rand = State System.Random.StdGen

randIO :: Rand a -> IO a
randIO r = System.Random.getStdRandom (runState r)

randomR :: Random a => (a, a) -> Rand a
randomR = state . System.Random.randomR

random :: Random a => Rand a
random = state System.Random.random

absRange :: Int -> Rand Int
absRange i = randomR (-i, i)

-- | Generates a random coordinate that lies within the given radius
randomCoordinate :: Int -> Rand Point
randomCoordinate radius = do
  x <- absRange radius
  y <- absRange (fromEnum (sqrt (toEnum (radius^2 - x^2) :: Double)))
  s <- random
  return (if s then (x, y) else (y, x))
  
distance :: Point -> Point -> Double
distance (x, y) (x', y')
  = let dx = x - x'
        dy = y - y'
    in sqrt (fromIntegral (dx^2 + dy^2))

tooClose :: [PPlanet] -> Point -> Growth -> Bool
tooClose ps p (Growth g) =
  or [ dist < threshold || dist <= 5
     | (p', Planet _ _ (Growth g')) <- ps
     , let dist = distance p p'
     , let threshold = multiplier * (sqrt (fromIntegral g) + sqrt (fromIntegral g'))
     ]
  where multiplier = 0.9

-- | @inMap i (x,y)@ returns if the point @(x,y)@ is inside the circle (centre
-- at origin) of radius i.
inMap :: Int -> Point -> Bool
inMap radius (x, y) = x^2 + y^2 <= radius ^2

untilM :: Monad m => (a -> Bool) -> m a -> m a
untilM p m = r where
  r = do x <- m; if p x then return x else r

randomPlanet :: Int       -- ^ Radius
             -> [PPlanet] -- ^ Previous planets
             -> Rand PPlanet
randomPlanet radius ps = untilM (\(c, Planet _ _ g) -> not (tooClose ps c g)) $ do
  c      <- randomCoordinate radius
  growth <- Growth <$> randomR (1,5)
  ships  <- Ships <$> randomR (50,150)
  return (c, Planet Neutral ships growth)

-- if not too_close && inMap radius c then

mirrorPlanet :: PPlanet -> PPlanet
mirrorPlanet ((x, y), Planet o s g)
  = ((-x, -y), Planet (mirrorOwner o) s g)
  where mirrorOwner Neutral = Neutral
        mirrorOwner (Owned Player1) = Owned Player2
        mirrorOwner (Owned Player2) = Owned Player1

repeatAndCollect :: Monad m => Int -> ([a] -> m a) -> m [a]
repeatAndCollect m k = go [] m
  where
    go acc n | n <= 0 = return acc
    go acc n = k acc >>= (\x -> go (x:acc) (n-1))

-- generates random planets for player 1
randomPlanets :: Int -> Rand (PPlanet, [PPlanet])
randomPlanets radius = do
  (c, Planet _ s _) <- randomPlanet radius []
  let home1 = (c, Planet (Owned Player1) s (Growth 5))
  ps <- repeatAndCollect (radius `div` 2) (randomPlanet radius . (:) home1)
  return (home1, ps)

type RenderableMap = (Map PlanetId Point, Planets, Wormholes)

minimumOn :: (Ord b, Foldable f) => (a -> b) -> f a -> a
minimumOn k = maybe (error "minimumOn: empty foldable") (getArg . getMin) 
            . foldMap (\x -> Just (Min (Arg (k x) x)))
  where
    getArg (Arg _ x) = x

randomMap :: Int -> Rand RenderableMap
randomMap radius = do
  -- Create planets for the half of the map for player 1
  ((c, home1), ps) <- randomPlanets radius

  let ps' = sortOn (\(c', _) -> distance c c') ps
      planets1_ :: [(PlanetId, PPlanet)]
      planets1_ = zip (map PlanetId [1..]) ps'

  -- Create paths from the home planet to all other planets
  (wormholes1 :: [Wormhole], planets1 :: [(PlanetId, (Point, Planet))]) <- foldM
    (\(wormholes, connected) target@(target_id, (target_pos, _)) -> do
        let (source_id, (source_pos, _))
              = minimumOn (\(_, (c', _)) -> distance target_pos c') connected
            turns  = Turns (round (distance source_pos target_pos))
            wormhole = Wormhole (Source source_id) (Target target_id) turns
        return (wormhole : wormholes, target : connected)
    )
    ([], [(PlanetId 0, (c, home1))]) planets1_

  -- Mirror the planets for player 2 
  let
    home2_id
      = length planets1

    twinId :: PlanetId -> PlanetId
    twinId (PlanetId p)
      = PlanetId ((p+home2_id) `mod` (2*home2_id))

    planets2 :: [(PlanetId, (Point, Planet))]
    planets2
      = mirrorPlanets home2_id planets1

    planets' :: Map PlanetId (Point, Planet)
    planets'
      = M.fromList (planets1 ++ planets2)

    planets_list = M.assocs planets'
    planets_count = length planets_list


  -- Generating some more wormholes for each planet
  (battle_wormholes :: [Wormhole]) <- fmap concat . forM planets1 $ \(pId, (pos, _)) -> do
    roll <- randomR @Int (1, 100)
    if roll <= 70
      then do
        index <- randomR (0, planets_count - 1)
        let (pId', (pos', _)) = planets_list !! index
            dis = distance pos pos'
        if dis <= 3 then
          return []
        else do
            let turns = Turns (round dis)
            return [ Wormhole (Source pId) (Target pId') turns ]
      else
        return []

  let mirrorWormholes :: [Wormhole] -> [Wormhole]
      mirrorWormholes = map (\(Wormhole (Source x) (Target y) t) -> 
                               Wormhole (Source (twinId x)) (Target (twinId y)) t) 

      dist = round (distance (fst (planets' M.! 1)) (fst (planets' M.! twinId 0)))

      homeWormhole = Wormhole (Source 1) (Target (twinId 0)) (Turns dist)

      halfWormholes = [homeWormhole] ++ wormholes1 ++ battle_wormholes

      wormholes = halfWormholes ++ mirrorWormholes halfWormholes
      

  -- If a planet has no incoming or outgoing edges, connect it to its twin.
  new_ws <- forM planets1 $ \(pId, (pos, _)) -> do
    let
      pId' = twinId pId
      twinPos = fst (planets' M.! pId')
      turns = Turns (round (distance pos twinPos))
    if isSink pId wormholes || isSource pId wormholes
      then return [ Wormhole (Source pId) (Target pId') turns
                  , Wormhole (Source pId') (Target pId) turns
                  ]
      else return []

  let ws_no_sinks = wormholes ++ concat new_ws

  return ( M.map fst planets'
         , M.map snd planets'
         , M.fromList (zip (map WormholeId [0..]) ws_no_sinks))

  where isSink :: PlanetId -> [Wormhole] -> Bool
        isSink pId = any ((==pId) . source)

        isSource :: PlanetId -> [Wormhole] -> Bool
        isSource pId = any ((==pId) . target)

        source :: Wormhole -> PlanetId
        source (Wormhole (Source s) _ _) = s

        target :: Wormhole -> PlanetId
        target (Wormhole (Source s) _ _) = s

        shiftPlanetId :: Int -> PlanetId -> PlanetId
        shiftPlanetId by (PlanetId pId) = PlanetId (by + pId)

        mirrorPlanets :: Int -> [(PlanetId, PPlanet)] -> [(PlanetId, PPlanet)]
        mirrorPlanets by = map (bimap (shiftPlanetId by) mirrorPlanet)


--------------------------------------------------------------------------------
-- Render

newtype Render a = Render { runRender :: State Builder a }
  deriving (Functor, Applicative, Monad)

draw :: Handle -> Render a -> IO a
draw h (Render st) = do
  let (a, s) = runState st mempty
  hPutBuilder h s
  return a

append :: String -> Render ()
append str = Render (modify (<> string7 str))

appendLn :: String -> Render ()
appendLn str = Render (modify (\s -> s <> string7 str <> char7 '\n'))

setNeutralCol :: Render ()
setNeutralCol =
  resetCol
  -- append "\x1b[30m"

setP1Col :: Render ()
setP1Col = do
  append "\x1b[44m"
  append "\x1b[97m"

setP2Col :: Render ()
setP2Col = do
  append "\x1b[41m"
  append "\x1b[97m"

resetCol :: Render ()
resetCol =
  append "\x1b[0m"

displayPlanet :: Planet -> Render ()
displayPlanet (Planet o (Ships s) (Growth g)) = do
  let playerCol = case o of
        Neutral       -> setNeutralCol
        Owned Player1 -> setP1Col
        Owned Player2 -> setP2Col
  playerCol
  append "\ESC7"
  append "    "
  append "\ESC8"
  append $ "[+" ++ show g ++ "]"
  append "\ESC8"
  append "\ESC[1B"
  append "    "
  append "\ESC8"
  append "\ESC[1B"
  append $ show s
  resetCol

drawBG :: Int -> Render ()
drawBG radius = do
  moveCursor (1,1)
  forM_ [- radius.. radius] $ \y -> do
    forM_ [- radius.. radius] $ \x -> do
      if not (inMap radius (x, y))
        then append "."
        else append " "
      append " "
    appendLn ""
  resetCol
  moveCursor (1,1)

mapToScreen :: Int -> Point -> Point
mapToScreen radius (x, y) = ((radius + x)*2 + 1, radius + y + 1)

moveCursor :: Point -> Render ()
moveCursor (x, y) = 
  append $ "\ESC[" ++ show y  ++ ";" ++ show x ++ "H"

data PixelVal = Empty | WormholePoint | FleetPoint Player deriving (Eq, Ord)

drawPlanets :: Int -> RenderableMap -> Render ()
drawPlanets radius (positions, planets, _) =
  forM_ (M.assocs positions) $ \ (pId, c) -> do
    moveCursor (mapToScreen radius c)
    displayPlanet (fromJust (M.lookup pId planets))


drawMap :: Int -> RenderableMap -> Fleets -> Render ()
drawMap radius rm@(positions, _, wormholes) fleets = do
  let wpos = mapToScreen radius . fromJust . flip M.lookup positions
      wcoord (Wormhole (Source s) (Target t) _) = (wpos s, wpos t)
  

  let arr = accumArray max Empty (mapToScreen radius (-radius,-radius), mapToScreen radius (radius,radius))
               ([ ((x,y),WormholePoint)
                |  w <- M.elems wormholes
                , let (c_s, c_t) = wcoord w
                , (x,y) <- line c_s c_t ] ++
               [ ((x,y),FleetPoint p)
               | Fleet p _ wId (Turns remaining) <- fleets
               , let Wormhole (Source s) (Target t) (Turns total) = fromJust (M.lookup wId wormholes)
                     ps = line (wpos s) (wpos t)
                     (x,y) = ps !! max 0 (floor $ fromIntegral (length ps) * (fromIntegral (total - remaining) / fromIntegral total))
               ]
               )

  forM_ (assocs arr) $ \case
    ((x,y),Empty) -> return ()
    ((x,y),WormholePoint) -> do append "\ESC[90m"; moveCursor (x,y); append "."; resetCol
    ((x,y),FleetPoint p) -> do setPCol p; moveCursor (x, y); append "."; resetCol
        where setPCol Player1 = setP1Col
              setPCol Player2 = setP2Col

  drawPlanets radius rm

  resetCol
  moveCursor (1, radius * 2 + 1)

-- drawFleet :: Player -> Point -> Point -> Double -> Render ()
-- drawFleet player p1 p2 progress = do
--   let ps = line p1 p2
--   setPCol player
--   let (x, y) = ps !! max 0 (floor $ fromIntegral (length ps) * progress)
--   moveCursor (x, y)
--   append " "
--   where setPCol Player1 = setP1Col
--         setPCol Player2 = setP2Col

-- drawLine :: Point -> Point -> Render ()
-- drawLine p1 p2 = do
--   append "\ESC[90m"
--   let ps = line p1 p2
--   forM_ ps $ \(x, y) -> do
--     moveCursor (x, y)
--     append "."
--   resetCol

-- from https://wiki.haskell.org/Bresenham%27s_line_drawing_algorithm (tweaked)
line :: Point -> Point -> [Point]
line pa@(xa,ya) pb@(xb,yb)
  = final . map maySwitch . unfoldr go $ (x1,y1,0)
  where
    steep = abs (yb - ya) > abs (xb - xa)
    maySwitch = if steep then (\(x,y) -> (y,x)) else id
    [(x1,y1),(x2,y2)] = sort [maySwitch pa, maySwitch pb]
    final = if maySwitch pa < maySwitch pb then id else reverse
    deltax = x2 - x1
    deltay = abs (y2 - y1)
    ystep = if y1 < y2 then 1 else -1
    go (xTemp, yTemp, err)
        | xTemp > x2 = Nothing
        | otherwise  = Just ((xTemp, yTemp), (xTemp + 1, newY, newErr))
        where
          tempError = err + deltay
          (newY, newErr) = if (2*tempError) >= deltax
                            then (yTemp+ystep,tempError-deltax)
                            else (yTemp,tempError)

{-
checkMap :: RenderableMap -> Bool
checkMap (_, planets, wormholes) = isSimpleGraph && isSymmetric && noSingleton where
  isSimpleGraph :: Bool
  isSimpleGraph = noDuplicate cmp (edges gs) && not (any selfLoop (edges gs))
    where cmp :: (WormholeId, Wormhole) -> (WormholeId, Wormhole) -> Bool
          cmp (_, Wormhole s t _) (_, Wormhole s' t' _) = s == s' && t == t'

  isSymmetric :: Bool
  isSymmetric = even numPlanets && all hasTwinEdge (edges gs) 

  hasTwinEdge :: (WormholeId, Wormhole) -> Bool 
  hasTwinEdge (_, Wormhole (Source s) (Target t) n) = Wormhole (Source (twinId s)) (Target (twinId t)) n `elem` map snd (edges gs)
  

  noSingleton :: Bool
  noSingleton = all (\v -> not (null (edgesFrom gs v)) && not (null (edgesTo gs v))) 
                    (vertices gs)

  gs :: GameState
  gs = GameState planets wormholes []

  noDuplicate :: (a -> a -> Bool) -> [a] -> Bool
  noDuplicate _ []     = True
  noDuplicate eq (x:xs) = not (any (eq x) xs) && noDuplicate eq xs

  selfLoop :: (WormholeId, Wormhole) -> Bool
  selfLoop (_, Wormhole (Source s) (Target t)  _) = s == t

  numPlanets :: Int
  numPlanets = M.size planets

  twinId :: PlanetId -> PlanetId
  twinId (PlanetId p)
    = PlanetId ((p + (numPlanets `div` 2)) `mod` numPlanets)
-}
