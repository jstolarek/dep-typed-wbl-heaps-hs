{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE NoImplicitPrelude    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
module Basics.Nat where

import Data.Singletons.TH

import Basics.Bool

-- Nat represents natural numbers (starting with 0)
data Nat :: * where
  Zero :: Nat
  Succ :: Nat -> Nat

$(genSingletons [ ''Nat ])

-- We define a constant 1 as it will be useful later on
one :: Nat
one = Succ Zero

-- Addition
$(promote [d|
  (+) :: Nat -> Nat -> Nat
  Zero     + m = m
  (Succ n) + m = Succ (n + m)
 |])

infix 6 +

(<) :: Nat -> Nat -> Bool
_ < Zero = False
Zero < Succ _ = True
Succ n < Succ m = n < m

(>=) :: Nat -> Nat -> Bool
_ >= Zero = True
Zero >= Succ _ = False
Succ m >= Succ n = m >= n

infixl 4 <, >=
