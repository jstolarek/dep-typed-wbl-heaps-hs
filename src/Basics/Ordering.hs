{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
module Basics.Ordering where

import Basics.Nat

import Data.Singletons

data GEq :: Nat -> Nat -> * where
  GeZ :: GEq y Zero
  GeS :: GEq x y -> GEq (Succ x) (Succ y)

data Order :: Nat -> Nat -> * where
  Ge :: GEq x y -> Order x y
  Le :: GEq y x -> Order x y

order :: forall (a :: Nat) (b :: Nat). Sing a -> Sing b -> Order a b
order  _         SZero    = Ge GeZ
order  SZero    (SSucc _) = Le GeZ
order (SSucc a) (SSucc b) = case order a b of
                              Ge ageb -> Ge (GeS ageb)
                              Le bgea -> Le (GeS bgea)
