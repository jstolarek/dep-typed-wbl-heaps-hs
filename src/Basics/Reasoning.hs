{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}
module Basics.Reasoning where

import Data.Singletons

import Basics.Nat hiding ((>=))
import Basics.Ordering
import Basics.Unreachable

import Prelude (undefined)

data PropEq :: k -> k -> * where
  Refl :: PropEq x x

sym :: PropEq a b -> PropEq b a
sym Refl = Refl

trans :: PropEq a b -> PropEq b c -> PropEq a c
trans Refl Refl = Refl

cong :: (Sing a -> Sing b) -> PropEq a c -> PropEq (f a) (f c)
cong _ Refl = Refl

{-
I'll invent that when necessary
subst : {A : Set}(P : A → Set) → {a b : A} → a ≡ b → P a → P b
subst prp refl p = p
-}

plusZero :: forall (a :: Nat).
            Sing a -> PropEq (a :+ Zero) a
plusZero  SZero    = Refl
plusZero (SSucc a) = cong SSucc (plusZero a)


plusSucc :: forall (a :: Nat) (b :: Nat).
            Sing a -> Sing b -> PropEq (Succ (a :+ b)) (a :+ (Succ b))
plusSucc  SZero    _ = Refl
plusSucc (SSucc a) b = cong SSucc (plusSucc a b)


plusComm :: forall (a :: Nat) (b :: Nat).
         Sing a -> Sing b -> PropEq (a :+ b) (b :+ a)
plusComm a   SZero   = plusZero a
plusComm a (SSucc b) = trans (sym (plusSucc a b))
                             (cong SSucc (plusComm a b ))

plusAssoc :: forall (a :: Nat) (b :: Nat) (c :: Nat).
         Sing a -> Sing b -> Sing c -> PropEq (a :+ (b :+ c)) ((a :+ b) :+ c)
plusAssoc  SZero    _ _ = Refl
plusAssoc (SSucc a) b c = cong SSucc (plusAssoc a b c)

geSym :: forall (a :: Nat) (b :: Nat).
         Sing a -> Sing b -> PropEq a b -> GEq a b
geSym  SZero     SZero    Refl = GeZ
geSym (SSucc a) (SSucc b) Refl = GeS (geSym a b Refl)
geSym  SZero    (SSucc _) _    = unreachable
geSym (SSucc _)  SZero    _    = unreachable
