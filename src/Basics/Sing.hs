-----------------------------------------------------------------------
-- Copyright: 2014, Jan Stolarek, Politechnika Łódzka                --
--                                                                   --
-- License: See LICENSE file in root of the repo                     --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps-hs --
--                                                                   --
-- Here we redefine a couple of things from `singletons` library so  --
-- that we don't need to install that package and its dependencies   --
-- just to get these few things. The extra cost is that we will be   --
-- writing by hand some boilerplate that could be generated          --
-- automatically by singletons but my intent was to strip down all   --
-- the library dependencies.                                         --
-----------------------------------------------------------------------

{-# LANGUAGE PolyKinds    #-}
{-# LANGUAGE TypeFamilies #-}
module Basics.Sing where

data family Sing (a :: k)
