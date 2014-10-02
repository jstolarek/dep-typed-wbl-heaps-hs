----------------------------------------------------------------------
-- Copyright: 2013, Jan Stolarek, Lodz University of Technology     --
--                                                                  --
-- License: See LICENSE file in root of the repo                    --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps   --
--                                                                  --
-- Definition of datatypes that represent ordering and functions    --
-- that operate on them. These datatypes are based on ideas         --
-- introduced in "Why Dependent Types Matter".                      --
----------------------------------------------------------------------

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

-- The ≥ type is a proof of greater-equal relation between two natural
-- numbers. It proves that: a) any number natural is greater or equal
-- to zero and b) any two natural numbers are in ≥ relation if their
-- predecessors are also in that relation.
data GEq :: Nat -> Nat -> * where
  GeZ :: GEq y Zero
  GeS :: GEq x y -> GEq (Succ x) (Succ y)

-- Order datatype tells whether two numbers are in ≥ relation or
-- not. In that sense it is an equivalent of Bool datatype. Unlike
-- Bool however, Order supplies a proof of WHY the numbers are (or are
-- not) in the ≥ relation.
data Order :: Nat -> Nat -> * where
  Ge :: GEq x y -> Order x y
  Le :: GEq y x -> Order x y

-- order function takes two natural numbers and compares them,
-- returning the result of comparison together with a proof of the
-- result (result and its proof are encoded by Order datatype).
order :: forall (a :: Nat) (b :: Nat). Sing a -> Sing b -> Order a b
order  _         SZero    = Ge GeZ
order  SZero    (SSucc _) = Le GeZ
order (SSucc a) (SSucc b) = case order a b of
                              Ge ageb -> Ge (GeS ageb)
                              Le bgea -> Le (GeS bgea)
