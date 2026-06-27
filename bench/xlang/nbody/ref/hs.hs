-- xlang/nbody reference — GHC (-O2).  N HARDCODED = 5000000 steps.
--
-- The classic CLBG N-body: Sun + 4 Jovian planets under Newtonian gravity,
-- leapfrog integrator (dt = 0.01), print total system energy before and after
-- to 9 decimals.  Idiomatic readable formulation over a flat mutable unboxed
-- array (one IOUArray Double holding [x,y,z,vx,vy,vz,mass] per body) with a
-- plain O(n^2) pairwise loop and `sqrt` — NOT the hand-tuned CLBG entry.
module Main where

import Data.Array.Base (unsafeRead, unsafeWrite)
import Data.Array.IO (IOUArray, newListArray)
import Text.Printf (printf)

nSteps :: Int
nSteps = 5000000 -- HARDCODED step count (must match every impl)

pii :: Double
pii = 3.141592653589793

solarMass :: Double
solarMass = 4.0 * pii * pii

daysPerYear :: Double
daysPerYear = 365.24

nBodies :: Int
nBodies = 5

-- 7 doubles per body: x y z vx vy vz mass
fieldsPerBody :: Int
fieldsPerBody = 7

initial :: [Double]
initial =
  concat
    [ -- Sun
      [0, 0, 0, 0, 0, 0, solarMass]
    , -- Jupiter
      [ 4.84143144246472090e+00, -1.16032004402742839e+00, -1.03622044471123109e-01
      , 1.66007664274403694e-03 * daysPerYear, 7.69901118419740425e-03 * daysPerYear
      , -6.90460016972063023e-05 * daysPerYear, 9.54791938424326609e-04 * solarMass ]
    , -- Saturn
      [ 8.34336671824457987e+00, 4.12479856412430479e+00, -4.03523417114321381e-01
      , -2.76742510726862411e-03 * daysPerYear, 4.99852801234917238e-03 * daysPerYear
      , 2.30417297573763929e-05 * daysPerYear, 2.85885980666130812e-04 * solarMass ]
    , -- Uranus
      [ 1.28943695621391310e+01, -1.51111514016986312e+01, -2.23307578892655734e-01
      , 2.96460137564761618e-03 * daysPerYear, 2.37847173959480950e-03 * daysPerYear
      , -2.96589568540237556e-05 * daysPerYear, 4.36624404335156298e-05 * solarMass ]
    , -- Neptune
      [ 1.53796971148509165e+01, -2.59193146099879641e+01, 1.79258772950371181e-01
      , 2.68067772490389322e-03 * daysPerYear, 1.62824170038242295e-03 * daysPerYear
      , -9.51592254519715870e-05 * daysPerYear, 5.15138902046611451e-05 * solarMass ]
    ]

base :: Int -> Int
base i = i * fieldsPerBody
{-# INLINE base #-}

offsetMomentum :: IOUArray Int Double -> IO ()
offsetMomentum a = do
  let go i px py pz
        | i >= nBodies = do
            unsafeWrite a 3 (negate px / solarMass)
            unsafeWrite a 4 (negate py / solarMass)
            unsafeWrite a 5 (negate pz / solarMass)
        | otherwise = do
            let b = base i
            vx <- unsafeRead a (b + 3)
            vy <- unsafeRead a (b + 4)
            vz <- unsafeRead a (b + 5)
            m  <- unsafeRead a (b + 6)
            go (i + 1) (px + vx * m) (py + vy * m) (pz + vz * m)
  go 0 0 0 0

energy :: IOUArray Int Double -> IO Double
energy a = goi 0 0.0
  where
    goi i !e
      | i >= nBodies = return e
      | otherwise = do
          let b = base i
          x  <- unsafeRead a (b + 0)
          y  <- unsafeRead a (b + 1)
          z  <- unsafeRead a (b + 2)
          vx <- unsafeRead a (b + 3)
          vy <- unsafeRead a (b + 4)
          vz <- unsafeRead a (b + 5)
          mi <- unsafeRead a (b + 6)
          let ke = 0.5 * mi * (vx * vx + vy * vy + vz * vz)
          e' <- goj i (i + 1) x y z mi (e + ke)
          goi (i + 1) e'
    goj i j x y z mi !e
      | j >= nBodies = return e
      | otherwise = do
          let c = base j
          xj <- unsafeRead a (c + 0)
          yj <- unsafeRead a (c + 1)
          zj <- unsafeRead a (c + 2)
          mj <- unsafeRead a (c + 6)
          let dx = x - xj
              dy = y - yj
              dz = z - zj
              dist = sqrt (dx * dx + dy * dy + dz * dz)
          goj i (j + 1) x y z mi (e - (mi * mj) / dist)

advance :: IOUArray Int Double -> Double -> IO ()
advance a dt = do
  let loopI i
        | i >= nBodies = return ()
        | otherwise = loopJ i (i + 1) >> loopI (i + 1)
      loopJ i j
        | j >= nBodies = return ()
        | otherwise = do
            let b = base i
                c = base j
            xi <- unsafeRead a (b + 0); yi <- unsafeRead a (b + 1); zi <- unsafeRead a (b + 2)
            xj <- unsafeRead a (c + 0); yj <- unsafeRead a (c + 1); zj <- unsafeRead a (c + 2)
            mi <- unsafeRead a (b + 6); mj <- unsafeRead a (c + 6)
            let dx = xi - xj; dy = yi - yj; dz = zi - zj
                d2 = dx * dx + dy * dy + dz * dz
                mag = dt / (d2 * sqrt d2)
            vix <- unsafeRead a (b + 3); viy <- unsafeRead a (b + 4); viz <- unsafeRead a (b + 5)
            vjx <- unsafeRead a (c + 3); vjy <- unsafeRead a (c + 4); vjz <- unsafeRead a (c + 5)
            unsafeWrite a (b + 3) (vix - dx * mj * mag)
            unsafeWrite a (b + 4) (viy - dy * mj * mag)
            unsafeWrite a (b + 5) (viz - dz * mj * mag)
            unsafeWrite a (c + 3) (vjx + dx * mi * mag)
            unsafeWrite a (c + 4) (vjy + dy * mi * mag)
            unsafeWrite a (c + 5) (vjz + dz * mi * mag)
            loopJ i (j + 1)
  loopI 0
  let posUpd i
        | i >= nBodies = return ()
        | otherwise = do
            let b = base i
            x  <- unsafeRead a (b + 0); y  <- unsafeRead a (b + 1); z  <- unsafeRead a (b + 2)
            vx <- unsafeRead a (b + 3); vy <- unsafeRead a (b + 4); vz <- unsafeRead a (b + 5)
            unsafeWrite a (b + 0) (x + dt * vx)
            unsafeWrite a (b + 1) (y + dt * vy)
            unsafeWrite a (b + 2) (z + dt * vz)
            posUpd (i + 1)
  posUpd 0

steps :: IOUArray Int Double -> Int -> IO ()
steps _ 0 = return ()
steps a k = advance a 0.01 >> steps a (k - 1)

main :: IO ()
main = do
  a <- newListArray (0, nBodies * fieldsPerBody - 1) initial :: IO (IOUArray Int Double)
  offsetMomentum a
  e0 <- energy a
  printf "%.9f\n" e0
  steps a nSteps
  e1 <- energy a
  printf "%.9f\n" e1
