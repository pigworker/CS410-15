module Ex4Haskell where

import System.IO
import System.Environment
import System.IO.Error
import Control.Applicative
import Debug.Trace

hOpenIO :: String -> IOMode -> IO (Maybe Handle)
hOpenIO s m = do
  -- putStrLn ("OpenIn!" ++ s)
  mh <- catchIOError (Just <$> openFile s m) (const (return Nothing))
  -- putStrLn ("OpenOut!")
  return mh

hCloseIO :: Handle -> IO ()
hCloseIO h = do
  -- putStrLn "CloseIn!"
  hClose h
  -- putStrLn "CloseOut!"

hIsEOFIO :: Handle -> IO Bool
hIsEOFIO h = do
  -- putStrLn "IsEOFIn!"
  b <- hIsEOF h
  -- putStrLn "IsEOFOut!"
  return b

hGetCharIO :: Handle -> IO Char
hGetCharIO h = do
  -- putStrLn "GetIn!"
  c <- hGetChar h
  -- putStrLn "GetOut!"
  return c

hPutCharIO :: Handle -> Char -> IO ()
hPutCharIO h c = do
  -- putStrLn "PutIn!"
  hPutChar h c
  -- putStrLn "PutOut!"

hErrorIO :: String -> IO a
hErrorIO x = ioError (userError x)

mainLoop ::
  (s -> Either String (IO s)) -> (String -> String -> s) ->
  IO ()
mainLoop step start = do
  let go s = case step s of
        Left m -> putStrLn m
        Right a -> a >>= go
  xs <- getArgs
  case xs of
    [src, trg] -> go (start src trg)
    _ -> putStrLn "cp <source> <target>"
