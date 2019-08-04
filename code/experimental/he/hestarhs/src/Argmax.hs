-- | Implementation of argmax protocol

module Argmax where

import Universum

import qualified Data.Time.Clock.POSIX as P
import qualified Foreign.Marshal as A
import System.Random (randomIO, randomRIO)

import Hacl
import qualified Lib as L
import Playground
