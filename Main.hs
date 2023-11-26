{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE CPP #-}

#ifndef BUILD_DIR
#define BUILD_DIR "."
#endif

#ifndef OUT_DIR
#define OUT_DIR "."
#endif

module Main where

import           Control.Exception
import           Control.Monad
import           Control.Concurrent
import           Control.Monad.Trans.State
import           Control.Monad.IO.Class
import           Data.List (sortOn, partition)
import           Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Binary as B
import qualified Data.ByteString.Lazy as B
import           Data.Maybe (fromJust, fromMaybe)
import           Data.IORef
import           System.Environment
import           System.IO
import           System.Process
import           System.Random
import           System.Exit
import           System.FilePath
import           System.Timeout
import           System.Directory (createDirectoryIfMissing)
import           Data.Time.Clock
import           Data.Coerce (coerce)
import           System.IO.NoBufferingWorkaround
import           Data.Hash.MD5 (md5s, Str (..))

import           Lib
import           Map
import           OptParser


log1_file :: String
log1_file = OUT_DIR </> "log1.txt"

log2_file :: String
log2_file = OUT_DIR </> "log2.txt"

main :: IO ()
main = do
  hSetBuffering stdout (BlockBuffering (Just 2000000))
  hSetBinaryMode stdout True

  let radius = 25

  Arguments
    { arg_p1        =  arg_p1
    , arg_p2        =  arg_p2
    , arg_seed      =  arg_seed
    , arg_strategy1 =  arg_strategy1
    , arg_strategy2 =  arg_strategy2
    , arg_ui        =  arg_ui
    , arg_turns     =  arg_turns
    , arg_recomp    =  arg_recomp
    , arg_stepping  =  arg_stepping
    , arg_timeout   =  arg_timeout
    } <- readArguments

  when arg_stepping $ do 
    hSetEcho stdin False
    initGetCharNoBuffering


  let strategy1 = fromMaybe Pacifist arg_strategy1
      strategy2 = fromMaybe Pacifist arg_strategy2


  -- Compile the AIs and get the file path to their binaries.
  m_p1 <- fmap Just (compileClient arg_recomp arg_p1 Player1)
            `catch` (\(_ :: SomeException) -> 
                       do putStrLn ("Failed to compile " ++ show Player1)
                          return Nothing)
  m_p2 <- fmap Just (compileClient arg_recomp arg_p2 Player2)
            `catch` (\(_ :: SomeException) ->
                       do putStrLn ("Failed to compile " ++ show Player2)
                          return Nothing)

  case (m_p1, m_p2) of
    (Just _, Nothing) -> putStrLn "Player 1 won" >> exitSuccess
    (Nothing, Just _) -> putStrLn "Player 2 won" >> exitSuccess
    (Nothing, Nothing) -> putStrLn "Draw" >> exitSuccess
    (Just _, Just _) -> return ()

  let p1 = fromJust m_p1
      p2 = fromJust m_p2
      
  seed <- maybe getStdGen return arg_seed
  setStdGen seed
  let (positions, planets, wormholes) = evalState (randomMap radius) seed


  -- Generate the map

  -- The time available to each AI is kept in an IORef
  timer_1 <- newIORef @NominalDiffTime (fromIntegral arg_timeout)
  timer_2 <- newIORef @NominalDiffTime (fromIntegral arg_timeout)

  let serverState
        = initialServerState
            arg_turns
            timer_1
            timer_2
            positions
            (GameState planets wormholes [])

  -- Options for calling AIs: the I/O of AIs are connected to the server by pipes.
  let p1config = (proc p1 ["+RTS", "-M2g", "-RTS", show strategy1])
                   {std_in = CreatePipe, std_out = CreatePipe, std_err = CreatePipe}
      p2config = (proc p2 ["+RTS", "-M2g", "-RTS", show strategy2])
                   {std_in = CreatePipe, std_out = CreatePipe, std_err = CreatePipe}

  when (arg_ui == Headless) $ do
    putStrLn "Running in headless mode..."
    putStrLn ("Seed: " <> showSeed seed)
    hFlush stdout

  -- Invoke the AIs.
  withCreateProcess p1config $ \(Just p1_in) (Just p1_out) (Just p1_err) p1h ->
    withCreateProcess p2config $ \(Just p2_in) (Just p2_out) (Just p2_err) p2h -> do

      -- The server writes the game state of each turn to the stdin of the AIs and
      -- reads the order of the AIs from their stdout. 
      -- Both |GameState| and |Order| are communicated in a binary format using the
      -- Data.Binary interface, so we need to set the pipes to the binary mode.
      hSetBinaryMode p1_in True
      hSetBinaryMode p1_out True
      hSetBinaryMode p2_in True
      hSetBinaryMode p2_out True

      when (isTUI arg_ui) $ do
        putStr "\ESC[2J" -- clear background
        liftIO (draw stdout (drawBG radius))

      writeFile log1_file ""
      writeFile log2_file ""

      let channel1 = makeChannel Player1 timer_1 p1_in p1_out p1_err
          channel2 = makeChannel Player2 timer_2 p2_in p2_out p2_err

      result <- evalStateT (loop radius seed arg_ui arg_stepping channel1 channel2) serverState
        `catch` (\(e :: AsyncException) -> case e of
            UserInterrupt -> return Interrupted
            e' -> throw e'
        ) `catch` (\(e :: SomeException) -> do
            when (isTUI arg_ui) $ do
              putStr "\ESC[2J"
              draw stdout resetCol

            exitCode1 <- getProcessExitCode p1h
            exitCode2 <- getProcessExitCode p2h

            putStrLn "Exception:"
            print e
            case exitCode1 of
              Just (ExitFailure _) -> do
                putStrLn "Player1 crashed: "
                r1 <- hReady p1_err
                when r1 (hGetContents p1_err >>= putStrLn)
              _ -> return ()

            case exitCode2 of
              Just (ExitFailure _) -> do
                putStrLn "Player2 crashed: "
                r2 <- hReady p2_err
                when r2 (hGetContents p2_err >>= putStrLn)
              _ -> return ()
            terminateProcess p1h
            terminateProcess p2h
            exitFailure
          )

      when (isTUI arg_ui) $ do
        putStrLn ""
        draw stdout resetCol

      case result of
        Player1Won  -> putStrLn "Player 1 won"
        Player2Won  -> putStrLn "Player 2 won"
        Draw        -> putStrLn "Draw"
        Interrupted -> putStrLn "Game interrupted"

      return ()

  return ()


-- Parse command line arguments.
readArguments :: IO Arguments
readArguments = do
  args <- getArgs
  case parseArgs args of
    Right a  -> return a
    Left err -> do unless (null err) (putStrLn err >> putStrLn "")
                   printUsage 
                   exitSuccess
       

-- |compileClient recomp src_dir p| invokes GHC to compile AI.hs in directory
-- src_dir as the AI for player |p| and returns the path to the compiled binary.
-- The argument |recomp| forces recompilation.
compileClient :: Bool -> String -> Player -> IO String
compileClient recomp src_dir _ = do
  let output_dir = BUILD_DIR </> escapeStr src_dir

      binary_name = output_dir </> "AI"

      fforce_recomp = if recomp then ["-fforce-recomp"] else []

  createDirectoryIfMissing True output_dir

  callProcess "ghc" (["-i" <> src_dir
                      , src_dir </> "AI.hs"
                      -- , "-package-env -"
                      , "-outputdir " ++ output_dir
                      , "-rtsopts"
                      , "-o", binary_name] ++ fforce_recomp)
  return binary_name

  where
    escapeStr :: FilePath -> String
    escapeStr path = "AI" ++ take 8 (md5s (Str path))


data ServerState = ServerState
  { remainingTurns   :: Turns
  , turnToDraw       :: Int
  , timer1           :: IORef NominalDiffTime
  , timer2           :: IORef NominalDiffTime
  , gameState        :: GameState
  , planet_positions :: Map PlanetId Point
  }

initialServerState
  :: Turns
  -> IORef NominalDiffTime
  -> IORef NominalDiffTime
  -> Map PlanetId Point
  -> GameState
  -> ServerState
initialServerState ts t1 t2 pos gs = ServerState
  { remainingTurns   = ts
  , turnToDraw       = 0
  , timer1           = t1
  , timer2           = t2
  , gameState        = gs
  , planet_positions = pos
  }

type Game a = StateT ServerState IO a

data PlayerTimedOutException
  = PlayerTimedOutException Player
  deriving Show

instance Exception PlayerTimedOutException

data Channel = Channel
  { sendGameState :: GameState -> IO [Order]
  , getErrors     :: IO String
  }

-- The IO actions for communicating with an AI for each turn.
makeChannel
  :: Player
  -> IORef NominalDiffTime
  -> Handle
  -> Handle
  -> Handle
  -> Channel
makeChannel player timer_ref stdin_ stdout_ stderr_
  = Channel sendGameState getErrors
  where
    sendGameState :: GameState -> IO [Order]
    sendGameState mst = do
      B.hPutStr stdin_ (B.encode mst)
      -- hPutStrLn stdin_ (show mst)
      hFlush stdin_

      timer <- readIORef timer_ref

      start <- getCurrentTime
      m_orders <- timeout ((floor timer + 2) * 10^(6::Integer)) $ -- set a timeout of t+2 seconds for the AI. 
        do size <- B.decode @Int <$> B.hGet stdout_ 8
           payload <- B.hGet stdout_ size
           return (B.decode @[Order] payload)
      end <- getCurrentTime

      case m_orders of
           Just orders -> do
             let new_timer = timer - diffUTCTime end start
             when (new_timer < 0) $
               throw (PlayerTimedOutException player)
             writeIORef timer_ref new_timer
             return orders
           Nothing -> throw (PlayerTimedOutException player)

    getErrors :: IO String
    getErrors = go []
      where go acc = do
              c <- hReady stderr_
              if c then do
                l <- hGetLine stderr_
                go (l : acc)
              else return (unlines (reverse acc))

--------------------------------------------------------------------------------
-- * Utilities


lookupPlanet :: PlanetId -> ServerState -> Planet
lookupPlanet pId ServerState{gameState=GameState planets _ _}
  = fromJust (M.lookup pId planets)

updatePlanet :: PlanetId -> (Planet -> Planet) -> ServerState -> ServerState
updatePlanet pId f st
  = st { gameState = updatePlanets (M.update (Just . f) pId) (gameState st)}
  where updatePlanets w (GameState planets wormholes fleets)
          = GameState (w planets) wormholes fleets

lookupWormhole :: WormholeId -> ServerState -> Wormhole
lookupWormhole wId ServerState{gameState=GameState _ wormholes _}
  = fromJust (M.lookup wId wormholes)

getPlanets :: Game Planets
getPlanets = do
  (GameState planets _ _) <- gets gameState
  return planets

getFleets :: Game Fleets
getFleets = do
  (GameState _ _ fleets) <- gets gameState
  return fleets

getTurns :: Game Turns
getTurns =
  gets remainingTurns

playerPlanets :: Player -> Game Planets
playerPlanets player
  = M.filter (\(Planet o _ _) -> o == Owned player) <$> getPlanets

playerTotalFleets :: Player -> Game Fleets
playerTotalFleets player
  = filter (\(Fleet p _ _ _) -> p == player) <$> getFleets

playerTotalGrowth :: Player -> Game Growth
playerTotalGrowth player
  = sum . map (\(Planet _ _ g) -> g) . M.elems <$> playerPlanets player

playerTotalShips :: Player -> Game Ships
playerTotalShips player = do
  planets <- playerPlanets player
  fleets  <- playerTotalFleets player
  return
    $ sum (map (\(Planet _ s _) -> s) (M.elems planets))
    + sum (map (\(Fleet _ s _ _) -> s) fleets)

--------------------------------------------------------------------------------
-- * Game logic

loop :: Int -> StdGen -> UI -> Bool -> Channel -> Channel -> Game Result
loop radius seed ui stepping ch1 ch2 = do
  st <- gets gameState

  (o1, o2) <- liftIO $ do
    o1 <- sendGameState ch1 st
    o2 <- sendGameState ch2 (invertPlayers st)
    e1 <- getErrors ch1
    e2 <- getErrors ch2
    appendFile log1_file e1
    appendFile log2_file e2
    return (o1, o2)

  departure Player1 o1
  departure Player2 o2
  advancement
  arrival

  draw_turn <- gets turnToDraw

  when (isTUI ui && draw_turn <= 0) $ do
    drawGameState radius seed
    if stepping 
      then liftIO $ getCharNoBuffering >> return ()
      else liftIO $ threadDelay 100000

  updateServerState ui

  m_result <- checkEndGame
  case m_result of
    Just result -> do when (isTUI ui) (drawGameState radius seed) 
                      return result
    Nothing -> loop radius seed ui stepping ch1 ch2

departure :: Player -> [Order] -> Game ()
departure = mapM_ . execute

execute :: Player -> Order -> Game ()
execute p (Order wId ships) = do
  Wormhole (Source sId) _ turns <- gets (lookupWormhole wId)
  Planet owner sourceShips _    <- gets (lookupPlanet sId)
  if sourceShips >= ships && owner == Owned p
    then do
    modify (updatePlanet sId (\(Planet _o s _g) -> Planet _o (s - ships) _g))
    modifyGameState $ \(GameState _ps _ws fleets) ->
      GameState _ps _ws (Fleet p ships wId turns : fleets)
    else error "execute: not enough ships!"

growPlanet :: Planet -> Planet
growPlanet p@(Planet Neutral _ _)
  = p
growPlanet (Planet o@(Owned _) ships g@(Growth growth))
  = Planet o (ships + Ships growth) g

advanceFleet :: Fleet -> Fleet
advanceFleet (Fleet _p _s _w (Turns t))
  = Fleet _p _s _w (Turns (t - 1))

advancement :: Game ()
advancement
  = modifyGameState $ \(GameState planets _w fleets) ->
    GameState (M.map growPlanet planets) _w (map advanceFleet fleets)

data PlanetForces = PlanetForces
  { _player1 :: Ships
  , _player2 :: Ships
  , _neutral :: Ships
  }

instance Semigroup PlanetForces where
  PlanetForces p1 p2 n <> PlanetForces p1' p2' n'
    = PlanetForces (p1 + p1') (p2 + p2') (n + n')

instance Monoid PlanetForces where
  mempty = PlanetForces 0 0 0
  mappend = (<>)

existingForces :: Planet -> PlanetForces
existingForces (Planet owner ships _) = case owner of
  Neutral       -> PlanetForces 0     0     ships
  Owned Player1 -> PlanetForces ships 0     0
  Owned Player2 -> PlanetForces 0     ships 0

fleetForce :: Player -> Ships -> PlanetForces
fleetForce Player1 ships = PlanetForces ships 0 0
fleetForce Player2 ships = PlanetForces 0 ships 0

invertPlayers :: GameState -> GameState
invertPlayers (GameState planets wormholes fleets)
  = GameState (invertPlanets planets) (invertWormholes wormholes) (invertFleets fleets)
  where inv Player1 = Player2
        inv Player2 = Player1
        invertOwner (Owned o) = Owned (inv o)
        invertOwner Neutral   = Neutral
        invertPlanet :: Planet -> Planet
        invertPlanet (Planet o s g) = Planet (invertOwner o) s g
        invertPlanets = M.map invertPlanet
        invertWormholes = id
        invertFleet :: Fleet -> Fleet
        invertFleet (Fleet p s w t) = Fleet (inv p) s w t
        invertFleets = map invertFleet

settle :: PlanetForces -> Planet -> Planet
settle (PlanetForces p1 p2 n) (Planet owner _ growth)
  = case sortOn fst [(p1, Owned Player1), (p2, Owned Player2), (n, Neutral)] of
      [_, (lForce, _), (wForce, winner)]
        | wForce == lForce -> Planet owner 0 growth
        | otherwise        -> Planet winner (wForce - lForce) growth
      _ -> error "impossible"

modifyGameState :: (GameState -> GameState) -> Game ()
modifyGameState f = modify (\st -> st { gameState = f (gameState st) })

arrival :: Game ()
arrival = do
  GameState planets _ fleets <- gets gameState
  let (arrived, fleets') = partition (\(Fleet _ _ _ turns) -> turns == 0) fleets

  modifyGameState (\(GameState ps ws _) -> GameState ps ws fleets')

  let initialForces :: Map PlanetId PlanetForces
      initialForces = M.map existingForces planets

  arrivingForces <- forM arrived $ \(Fleet owner ships viaWormhole _) -> do
    Wormhole _ (Target dst) _ <- gets (lookupWormhole viaWormhole)
    return (dst, fleetForce owner ships)

  let totalForces
        = M.unionWith (<>) initialForces (M.fromListWith (<>) arrivingForces)

  forM_ (M.toList totalForces) $ \ (pId, pForces) ->
    modify (updatePlanet pId (settle pForces))

data Result
  = Player1Won
  | Player2Won
  | Draw
  | Interrupted

checkEndGame :: Game (Maybe Result)
checkEndGame = do
  turns <- gets remainingTurns

  p1Ships <- playerTotalShips Player1
  p2Ships <- playerTotalShips Player2

  let end = or [turns == 0, p1Ships == 0, p2Ships == 0]

  if end then
    return (Just (gameOver p1Ships p2Ships))
  else
    return Nothing

gameOver :: Ships -> Ships -> Result
gameOver p1Ships p2Ships
  | p1Ships > p2Ships = Player1Won
  | p1Ships < p2Ships = Player2Won
  | otherwise         = Draw

updateServerState :: UI -> Game ()
updateServerState ui
  = modify (\st -> st { remainingTurns = remainingTurns st - 1
                      , turnToDraw =
                          case ui of
                            TUI n -> if turnToDraw st <= 0 
                                       then n - 1
                                       else turnToDraw st - 1
                            _ -> turnToDraw st
                      })

--------------------------------------------------------------------------------
-- * Drawing

drawGameState :: Int -> StdGen -> Game ()
drawGameState radius seed = do
  ServerState _ _ t1 t2 (GameState planets wormholes fleets) positions <- get
  liftIO $ draw stdout (drawMap radius (positions, planets, wormholes) fleets)
  drawStats radius seed t1 t2
  liftIO $ draw stdout (moveCursor (mapToScreen radius (radius, radius)))
  liftIO $ hFlush stdout

drawStats :: Int -> StdGen -> IORef NominalDiffTime -> IORef NominalDiffTime -> Game ()
drawStats radius seed t1 t2 = do
  timer1 <- liftIO $ readIORef t1
  timer2 <- liftIO $ readIORef t2
  let stats
        = [ (resetCol, "Seed",            pure (showSeed seed))
          , (resetCol, "Remaining turns", show @Int . coerce <$> getTurns)
          , (setP1Col, "Player 1 ships",  show @Int . coerce <$> playerTotalShips Player1)
          , (setP1Col, "Player 1 growth", show @Int . coerce <$> playerTotalGrowth Player1)
          , (setP1Col, "Player 1 time",   pure (show timer1))
          , (setP2Col, "Player 2 ships",  show @Int . coerce <$> playerTotalShips Player2)
          , (setP2Col, "Player 2 growth", show @Int . coerce <$> playerTotalGrowth Player2)
          , (setP2Col, "Player 2 time",   pure (show timer2))
          ]

  forM_ (zip [1..] stats) $ \(pos, (set_col, legend, value)) -> do
    v <- value
    liftIO . draw stdout $ do
      set_col
      moveCursor (radius * 4 + 5, pos)
      append (legend ++ ": ")
      append "\ESC7"
      append "        "
      append "\ESC8"
      append v

  liftIO (draw stdout resetCol)
