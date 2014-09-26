{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE TypeOperators       #-}
module Basics.Reasoning where

import Data.Singletons

import Basics.Nat
import Basics.Ordering
import Basics.Unreachable

data a :~: b where
  Refl :: a :~: a

sym :: (a :~: b) -> (b :~: a)
sym Refl = Refl

trans :: (a :~: b) -> (b :~: c) -> (a :~: c)
trans Refl Refl = Refl

cong :: (Sing a -> Sing b) -> (a :~: c) -> (f a :~: f c)
cong _ Refl = Refl

-- stolen from Data.Type.Equality (new in GHC 7.8)
gcastWith :: (a :~: b) -> ((a ~ b) => r) -> r
gcastWith Refl x = x

plusZero :: forall (a :: Nat).
            Sing a -> ((a :+ Zero) :~: a)
plusZero  SZero    = Refl
plusZero (SSucc a) = cong SSucc (plusZero a)


plusSucc :: forall (a :: Nat) (b :: Nat).
            Sing a -> Sing b -> ((Succ (a :+ b)) :~: (a :+ (Succ b)))
plusSucc  SZero    _ = Refl
plusSucc (SSucc a) b = cong SSucc (plusSucc a b)


plusComm :: forall (a :: Nat) (b :: Nat).
            Sing a -> Sing b -> (a :+ b) :~: (b :+ a)
plusComm a   SZero   = plusZero a
plusComm a (SSucc b) = trans (sym (plusSucc a b))
                             (cong SSucc (plusComm a b ))


plusAssoc :: forall (a :: Nat) (b :: Nat) (c :: Nat).
             Sing a -> Sing b -> Sing c -> (a :+ (b :+ c)) :~: ((a :+ b) :+ c)
plusAssoc  SZero    _ _ = Refl
plusAssoc (SSucc a) b c = cong SSucc (plusAssoc a b c)


geSym :: forall (a :: Nat) (b :: Nat).
         Sing a -> Sing b -> a :~: b -> GEq a b
geSym  SZero     SZero    Refl = GeZ
geSym (SSucc a) (SSucc b) Refl = GeS (geSym a b Refl)
geSym  SZero    (SSucc _) _    = unreachable
geSym (SSucc _)  SZero    _    = unreachable
