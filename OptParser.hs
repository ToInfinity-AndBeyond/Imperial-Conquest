{-# LANGUAGE TypeApplications #-}

module OptParser ( parseArgs
                 , printUsage
                 , Strategy (..)
                 , UI (..)
                 , isTUI
                 , Arguments (..)
                 , showSeed
                 ) where

import           Prelude hiding (fail, or)
import           Control.Monad hiding (fail)
import           Control.Monad.Trans
import           Control.Monad.Trans.State
import           Data.List (intercalate)
import           System.Random
import           System.Environment

import           Lib

data Strategy
  = Pacifist
  | ZergRush
  | PlanetRankRush
  | TimidRush
  | Skynet
  deriving (Enum, Bounded, Show, Read)

data UI = Headless | TUI Int
  deriving (Ord, Eq, Show)

isTUI :: UI -> Bool
isTUI (TUI _) = True
isTUI _       = False

-- The datatype for command line arguments. 
-- The fields are annotated as being strict so that illegal command line
-- arguments can be detected as soon as possible.
data Arguments = Arguments
  { arg_p1        :: !String
  , arg_p2        :: !String
  , arg_seed      :: !(Maybe StdGen)
  , arg_strategy1 :: !(Maybe Strategy)
  , arg_strategy2 :: !(Maybe Strategy)
  , arg_ui        :: !UI
  , arg_turns     :: !Turns
  , arg_recomp    :: !Bool
  , arg_stepping  :: !Bool
  , arg_timeout   :: !Int
  } deriving Show


defaultArguments :: String -> String -> Arguments
defaultArguments p1 p2
  = Arguments { arg_p1=p1
              , arg_p2=p2
              , arg_seed=Nothing
              , arg_strategy1=Nothing
              , arg_strategy2=Nothing
              , arg_ui=TUI 1
              , arg_turns=400
              , arg_recomp=False
              , arg_stepping=False
              , arg_timeout=10
              }

printUsage :: IO ()
printUsage
  = do progName <- getProgName

       let all_strats :: [Strategy]
           all_strats = [minBound..maxBound]

           options :: [(String, String)]
           options = [ ("[--seed seed]",             "random generator seed for the map")
                     , ("[--strategy1 [ " ++ intercalate " | " (map show all_strats) ++ " ]]"
                       ,                             "strategy for the first player. Default is Pacifist")
                     , ("[--strategy2 [ " ++ intercalate " | " (map show all_strats) ++ " ]]"
                       ,                             "strategy for the second player. Default is Pacifist" )
                     , ("[--headless]",              "run the game without drawing. Default is off")
                     , ("[--draw-interval turns]",   "when runnning in TUI, draw the map every <turns> turns. Default is 1")
                     , ("[--stepping]",              "when running in TUI, wait for a key press before showing the next turn. Default is off")
                     , ("[--recomp]",                "force recompilation of the AIs. Default is off")
                     , ("[--turns turns]",           "the total number of turns for the game. Default is 400")
                     , ("[--timeout seconds]",       "the timeout for each AI. Default is 60")
                     ]

           optWidth :: Int
           optWidth = maximum (map (length . fst) options)

           optionStr = intercalate "\n" $
             map (\(opt, desc) -> opt ++ (replicate (optWidth + 2 - length opt) ' ') ++ desc)
                 options

       putStrLn $ concat
         [ "OVERVIEW: the server of Imperial Conquest\n"
         , "USAGE: ", progName, " <bot1> <bot2> [options]\n"
         , "\nOPTIONS:\n"
         , optionStr
         ]

parseArgs :: [String] -> Either String Arguments
parseArgs = evalStateT parser where

  -- The parser of command line arguments.
  parser :: OptParser Arguments
  parser = do ops   <- optionals
              p1    <- nonFlag `withErrMsg` "The server must take two AIs as arguments"
              ops'  <- optionals
              p2    <- nonFlag `withErrMsg` "The server must take two AIs as arguments"
              ops'' <- optionals
              end
              return (ops (ops' (ops'' (defaultArguments p1 p2))))

  -- Parse an optional argument.
  optional :: OptParser (Arguments -> Arguments)
  optional = do a <- arg 
                case a of
                  "--seed" -> do seed <- nonFlag >>= readSeed 
                                 return (\res -> res {arg_seed = Just seed})
                  "--strategy1" -> do strategy <- nonFlag >>= readSafe
                                      return (\res -> res {arg_strategy1 = Just strategy})
                  "--strategy2" -> do strategy <- nonFlag >>= readSafe
                                      return (\res -> res {arg_strategy2 = Just strategy})
                  "--headless" -> return (\res -> res {arg_ui = Headless})

                  "--draw-interval" -> do turns <- posInt `withErrMsg` "--draw-interval must take a positive integer"
                                          return (\res -> res {arg_ui = TUI turns})
                  "--recomp" -> return (\res -> res {arg_recomp = True})

                  "--stepping" -> return (\res -> res {arg_stepping = True})

                  "--no-recomp" -> return (\res -> res {arg_recomp = False})

                  "--turns" -> do turns <- posInt `withErrMsg` "--turns must take a positive integer"
                                  return (\res -> res {arg_turns = Turns turns})
                  "--timeout" -> do time <- posInt `withErrMsg` "--timeout must take a positive integer"
                                    return (\res -> res {arg_timeout = time})
                  _ -> fail ("Unknown option: " ++ a)
                  
  -- Parse optionals until the next argument does not start wit '--'.
  optionals :: OptParser (Arguments -> Arguments)
  optionals = fmap (foldr (.) id) $ optional `till` nextIsNotAnOption

  nextIsNotAnOption :: OptParser ()
  nextIsNotAnOption = lookAhead (end `or` (do x <- arg; when (flag x) (fail "")))

  flag :: String -> Bool
  flag ('-' : '-' : _) = True
  flag _ = False

  -- Consume an argument not starting with '--'.
  nonFlag :: OptParser String
  nonFlag = do a <- arg
               if flag a then fail "" else return a

  -- Consume a positive integer
  posInt :: OptParser Int
  posInt = do a <- nonFlag 
              i <- readSafe a
              when (i <= 0) (fail ("Not a positive integer: " ++ a)) 
              return i

-- A minimal parser combinator library
--------------------------------------------------------------------------------

type OptParser x = StateT [String] (Either String) x

-- Fail with an error message
fail :: String -> OptParser a
fail s = lift (Left s)

-- Modify the error message of a parser
withErrMsg :: OptParser a -> String -> OptParser a
withErrMsg p str = StateT $ \s -> 
  case runStateT p s of 
    Left _ -> Left str
    Right a -> Right a

-- Consume an argument
arg :: OptParser String
arg = do args <- get
         case args of
           (a:as) -> put as >> return a
           _      -> fail "No more argument"

-- It succeeds when all arguments are consumed.
end :: OptParser ()
end = do args <- get
         case args of [] -> return ()
                      _  -> fail ("Cannot parse argument(s): " ++ (intercalate " " args))

-- Try the first parse, and if it fails, try again with the second one (as if
-- the first parser didn't consume anything).
or :: OptParser a -> OptParser a -> OptParser a
or a b = StateT $ \s -> case runStateT a s of
           Left _  -> runStateT b s
           res     -> res

-- Iterate a parser until it fails. 
many :: OptParser a -> OptParser [a]
many p = (do x <- p; xs <- many p; return (x : xs)) `or` return []

-- Iterate the first parser until the second succeeds.
till :: OptParser a -> OptParser b -> OptParser [a]
till p end = (fmap (const []) end) `or` ((:) <$> p <*> (till p end))

-- Run a parser and rewind the consumed tokens even if it succeeds.
lookAhead :: OptParser a -> OptParser a
lookAhead p = StateT $ \s ->
  case runStateT p s of
    Left m       -> Left m
    Right (a, _) -> Right (a, s)

showSeed :: StdGen -> String
showSeed stdgen = map go (show stdgen)
  where go ' ' = '-'
        go x = x

readSeed :: String -> OptParser StdGen
readSeed str = readSafe (map go str)
  where go '-' = ' '
        go x = x

readSafe :: Read a => String -> OptParser a
readSafe s = case reads s of
                [(a, "")] -> return a
                _         -> lift (Left ("Cannot parse " ++ s))
