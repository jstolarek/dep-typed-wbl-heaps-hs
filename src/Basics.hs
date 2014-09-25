module Basics (
   module Basics.Bool
 , module Basics.Nat
 , module Basics.Ordering
 , module Basics.Reasoning
 , module Basics.Unreachable
 , Rank, Priority
 , undefined
 ) where

import Basics.Bool
import Basics.Nat
import Basics.Ordering
import Basics.Reasoning
import Basics.Unreachable

type Rank = Nat

type Priority = Nat
