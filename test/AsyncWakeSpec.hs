module Main (main) where

import Control.Concurrent
  ( forkIO
  , newEmptyMVar
  , putMVar
  , takeMVar
  )
import Control.Exception (Exception, catch, uninterruptibleMask_)
import Kappa.AsyncException (throwToAsync)
import System.Exit (exitFailure)
import System.Timeout (timeout)

data WakeProbe = WakeProbe
  deriving stock (Show)

instance Exception WakeProbe

main :: IO ()
main = do
  ready <- newEmptyMVar
  release <- newEmptyMVar
  done <- newEmptyMVar
  target <-
    forkIO $ do
      _ <-
        ( uninterruptibleMask_ $ do
            putMVar ready ()
            takeMVar release
        ) `catch` \WakeProbe -> pure ()
      putMVar done ()
  takeMVar ready
  returned <- timeout 1000000 (throwToAsync target WakeProbe)
  putMVar release ()
  _ <- takeMVar done
  case returned of
    Just () -> putStrLn "PASS: asynchronous host wake does not wait for target acceptance"
    Nothing -> do
      putStrLn "FAIL: host wake blocked on an uninterruptible target"
      exitFailure
