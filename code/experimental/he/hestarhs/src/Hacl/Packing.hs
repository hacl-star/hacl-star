{-# LANGUAGE NamedFieldPuns #-}
-- | Packing methods

module Hacl.Packing where

import Universum hiding (exp, last, (<*>))

import qualified Lib as L


----------------------------------------------------------------------------
-- CRT packing
----------------------------------------------------------------------------

crt :: [Integer] -> [Integer] -> Integer
crt base vals = L.crt $ vals `zip` base

crtInv :: [Integer] -> Integer -> [Integer]
crtInv base v = map (v `mod`) base

crtToBase :: [Integer] -> [Integer] -> [Integer]
crtToBase base vals = map (\(b,p) -> b `mod` p) $ vals `zip` base

----------------------------------------------------------------------------
-- FFT Packing is in the playground.hs
----------------------------------------------------------------------------
