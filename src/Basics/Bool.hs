{-# LANGUAGE NoImplicitPrelude, KindSignatures, GADTs #-}
module Basics.Bool where

data Bool :: * where
  False :: Bool
  True  :: Bool
