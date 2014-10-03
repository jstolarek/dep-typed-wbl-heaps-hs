-----------------------------------------------------------------------
-- Copyright: 2014, Jan Stolarek, Politechnika Łódzka                --
--                                                                   --
-- License: See LICENSE file in root of the repo                     --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps-hs --
--                                                                   --
-- Weight biased leftist heap that proves to maintain priority       --
-- invariant: priority at the node is not lower than priorities of   --
-- its two children. Uses a two-pass merging algorithm.              --
-----------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}
module TwoPassMerge.PriorityProof where



import Basics
import qualified Basics.Nat as Nat ((>=))

-- Priority invariant says that: for any node in the tree priority in
-- that node is now lower than priority stored by its children. This
-- means that any path from root to leaf is ordered (highest priority
-- at the root, lowest at the leaf). This property allows us to
-- construct an efficient merging operation (see Okasaki for more
-- details).
--
-- To prove this invariant we will index nodes using Priority. Index
-- of value n says that "this heap can store elements with priorities
-- n or lower" (remember that lower priority means larger Nat). In
-- other words Heap indexed with 0 can store any Priority, while Heap
-- indexed with 3 can store priorities 3, 4 and lower, but can't store
-- 0, 1 and 2.
--
-- As previously, Heap has two constructors:
--
--  1) empty returns Heap n, where index n is not constrained in any
--     way. This means that empty heap can be given any restriction on
--     priorities of stored elements.
--
--  2) node also creates Heap n, but this time n is constrained. If we
--     store priority p in a node then:

--       a) the resulting heap can only be restricted to store
--          priorities at least as high as p. For example, if we
--          create a node that stores priority 3 we cannot restrict
--          the resulting heap to store priorities 4 and lower,
--          because the fact that we store 3 in that node violates the
--          restriction. This restriction is expressed by the "p ≥ n"
--          parameter: if we can construct a value of type (p ≥ n)
--          then existance of such a value becomes a proof that p is
--          greater-equal to n. We must supply such proof to every
--          node.

--       b) children of a node can only be restricted to store
--          priorities that are not higher than p. Example: if we
--          restrict a node to store priorities 4 and lower we cannot
--          restrict its children to store priorities 3 and
--          higher. This restriction is expressed by index "p" in the
--          subheaps passed to node constructor.

data Heap :: Nat -> * where
  Empty :: Heap n
  Node  :: forall (p :: Nat) (n :: Nat).
           (Sing p) -> Rank -> GEq p n -> Heap p -> Heap p -> Heap n

-- Let's demonstrate that priority invariant cannot be broken. Below
-- we construct a heap like this:
--
--      ?
--     / \
--    /   \
--   E     0
--
-- where E means empty node and 0 means node storing Priority 0 (yes,
-- this heap violates the rank invariant!). We left out the root
-- element. The only value that can be supplied there is zero (try
-- giving one and see that typechecker will not accept it). This is
-- beacuse the value n with which 0 node can be index must obey the
-- restriction 0 ≥ n. This means that 0 node can only be indexed with
-- 0. When we try to construct ? node we are thus only allowed to
-- insert priority 0.

-- FIXME COMMENT ABOVE
--heapBroken :: Heap One
--heapBroken = Node sZero two GeZ Empty (Node sZero one GeZ Empty Empty)

-- Here is a correct heap. It stores one at the leaf and 0 at the
-- root. It still violates the rank invariant - we deal with that in
-- TwoPassMerge.RankProof.
heapCorrect :: Heap Zero
heapCorrect = Node sZero two GeZ Empty (Node sOne one GeZ Empty Empty)

-- Again, we need a function to extract rank from a node
rank :: Heap b -> Rank
rank Empty            = Zero
rank (Node _ r _ _ _) = r

-- The first question is how to create a singleton heap, ie. a Heap
-- storing one element. The question we need to answer is "what
-- Priorities can we later store in a singleton Heap?". "Any" seems to
-- be a reasonable answer. This means the resulting Heap will be
-- indexed with zero, meaning "Priorities lower or equal to zero can
-- be stored in this Heap" (remember that any priority is lower or
-- equal to zero). This leads us to following definition:
singleton :: forall (p :: Nat).
             Sing p -> Heap Zero
singleton p = Node p one GeZ Empty Empty

-- We can imagine we would like to limit the range of priorities we
-- can insert into a singleton Heap. This means the resulting Heap
-- would be index with some b (the bound on allowed Priority
-- values). In such case however we are required to supply a proof
-- that p ≥ b. This would lead us to a definition like this:
--
-- singletonB : {b : Priority} → (p : Priority) → p ≥ b → Heap b
-- singletonB p p≥b = node p one p≥b empty empty
--
-- We'll return to that idea soon.

-- makeT now returns indexed heaps, so it requires one more parameter:
-- a proof that priorities stored in resulting heap are not lower than
-- in the subheaps.
makeT :: forall (p :: Nat) (b :: Nat).
         Sing p -> GEq p b -> Heap p -> Heap p -> Heap b
makeT p pgeb l r = case rank l Nat.>= rank r of
                     True  -> Node p (Succ (rank l + rank r)) pgeb l r
                     False -> Node p (Succ (rank l + rank r)) pgeb r l

-- The important change in merge is that now we don't compare node
-- priorities using an operator that returns Bool. We compare them
-- using "order" function that not only returns result of comparison,
-- but also supplies a proof of the result. This proof tells us
-- something important about the relationship between p1, p2 and
-- priority bound of the merged Heap. Note that we use the new proof
-- to reconstruct one of the heaps that is passed in recursive call to
-- merge. We must do this because by comparing priorities p1 and p2 we
-- learned something new about restriction placed on priorities in one
-- of the heaps and we can now be more precise in expressing these
-- restrictions.
--
-- Note also that despite indexing our data types with Size the
-- termination checker complains that merge function does not
-- terminate. This is not a problem in our definitions but a bug in
-- Agda's implementation. I leave the code in this form in hope that
-- this bug will be fixed in a future release of Agda. For mor details
-- see http://code.google.com/p/agda/issues/detail?id=59#c23
merge :: forall (p :: Nat).
         Heap p -> Heap p -> Heap p
merge Empty h2 = h2
merge h1 Empty = h1
merge (Node p1 lRank p1gep l1 r1)
      (Node p2 rRank p2gep l2 r2) = case order p1 p2 of
          Le p1lep2 -> makeT p1 p1gep l1 (merge r1 (Node p2 rRank p1lep2 l2 r2))
          Ge p1gep2 -> makeT p2 p2gep l2 (merge (Node p1 lRank p1gep2 l1 r1) r2)
-- When writing indexed insert function we once again have to answer a
-- question of how to index input and output Heap. The easiest
-- solution is to be liberal: let us require that the input and output
-- Heap have no limitations on Priorities they can store. In other
-- words, let they be indexed by zero:
insert :: forall (p :: Nat).
          Sing p -> Heap Zero -> Heap Zero
insert p h = merge (singleton p) h

-- Now we can create an example heap. The only difference between this
-- heap and the heap without any proofs is that we need to explicitly
-- instantiate implicit Priority parameter of empty constructor.
heap :: Heap Zero
heap = insert sTwo
      (insert sOne
      (insert sZero
      (insert sThree Empty)))

-- But what if we want to insert into a heap that is not indexed with
-- 0? One solution is to be liberal and ``promote'' that heap so that
-- after insertion it can store elements with any priorities:
toZero :: Heap b -> Heap Zero
toZero Empty              = Empty
toZero (Node p rnk _ l r) = Node p rnk GeZ l r

insert0 :: forall (p :: Nat) b.
           Sing p -> Heap b -> Heap Zero
insert0 p h = merge (singleton p) (toZero h)

-- But what if we actaully want to maintain bounds imposed on the heap
-- by its index? To achieve that we need a new singleton function that
-- constructs a singleton Heap with a bound equal to priority of a
-- single element stored by the heap. To construct a proof required by
-- node we use ≥sym, which proves that if p :~: p then p ≥ p.
singletonB :: forall (p :: Nat).
              Sing p -> Heap p
singletonB p = Node p one (geqSym p p Refl) Empty Empty

-- We can now write new insert function that uses singletonB function:
insertB :: forall (p :: Nat).
           Sing p -> Heap p -> Heap p
insertB p h = merge (singletonB p) h
-- However, that function is pretty much useless - it can insert
-- element with priority p only to a heap that has p as its bound. In
-- other words if we have Heap zero - ie. a heap that can store any
-- possible priorityu -- the only thing that we can insert into it
-- using insertB function is zero. That's clearly not what we want. We
-- need a way to manipulate resulting priority bound.

-- Let's try again. This time we will write functions with signatures:
--
--  singletonB' : {b : Priority} → (p : Priority) → p ≥ b → Heap b
--  insertB' : {b : Priority} → (p : Priority) → p ≥ b → Heap p → Heap b
--
-- Singleton allows to construct Heap containing priority p but
-- bounded by b. This of course requires proof that p ≥ b, ie. that
-- priority p can actually be stored in Heap b. insertB' is similar -
-- it can insert element of priority p into Heap bounded by p but the
-- resulting Heap can be bounded by b (provided that p ≥ b, for which
-- we must supply evidence). Let's implement that.

-- Implementing singletonB' is straightforward:
singletonB' :: forall p b.
               Sing p -> GEq p b -> Heap b
singletonB' p pgeb = Node p one pgeb Empty Empty

-- To implement insertB' we need two additional functions. Firstly, we
-- need a proof of transitivity of ≥. We proceed by induction on
-- c. Our base case is:
--
--   a ≥ b ∧ b ≥ 0 ⇒ a ≥ 0
--
-- In other words if c is 0 then ge0 proves the property. If c is not
-- zero, then b is also not zero (by definitions of data constructors
-- of ≥) and hence a is also not zero. This gives us second equation
-- that is a recursive proof on ≥trans.
geqTrans :: forall a b c. GEq a b -> GEq b c -> GEq a c
geqTrans _          GeZ        = GeZ
geqTrans (GeS ageb) (GeS bgec) = GeS (geqTrans ageb bgec)
geqTrans _          _          = unreachable

-- Having proved the transitivity of ≥ we can construct a function
-- that loosens the bound we put on a heap. If we have a heap with a
-- bound p - meaning that all priorities in a heap are guaranteed to
-- be lower than or equal to p - and we also have evidence than n is a
-- priority higher than p then we can change the restriction on the
-- heap so that it accepts higher priorites. For example if we have
-- Heap 5, ie. all elements in the heap are 5 or greater, and we have
-- evidence that 5 ≥ 3, then we can convert Heap 5 to Heap 3. Note how
-- we are prevented from writing wrong code: if we have Heap 3 we
-- cannot convert it to Heap 5. This is not possible from theoretical
-- point of viwe: Heap 3 may contain 4, but Heap 5 is expected to
-- contain elements not smaller than 5. It is also not possible
-- practically: thanks to our definition of ≥ we can't orivide
-- evidence that 3 ≥ 5 because we cannot construct value of that type.
liftBound :: forall p b. GEq b p -> Heap b -> Heap p
liftBound _     Empty                = Empty
liftBound bgen (Node p rnk pgeb l r) = Node p rnk (geqTrans pgeb bgen) l r

-- With singletonB and liftBound we can construct insert function that
-- allows to insert element with priority p into a Heap bound by b,
-- but only if we can supply evidence that p ≥ b, ie. that p can
-- actually be stored in the heap.
insertB' :: forall p b. Sing p -> GEq p b -> Heap p -> Heap b
insertB' p pgeb h = merge (singletonB' p pgeb) (liftBound pgeb h)

-- But if we try to create an example Heap as we did previously we
-- quickly discover that this function isn't of much use either:
--heap' :: Heap Zero
--heap' = insertB' sTwo GeZ
--       (insertB' sOne GeZ
--       (insertB' sZero undefined
--       (insertB' sThree GeZ Empty)))

-- In third hole we are required to supply evidence that 0 ≥ 1 and
-- that is not possible. The reason is that our insertB' function
-- allows us only to insert elements into a heap in decreasing order:
heap'' :: Heap Zero
heap'' = insertB' sZero   GeZ
        (insertB' sOne    GeZ
        (insertB' sTwo   (GeS GeZ)
        (insertB' sThree (GeS (GeS GeZ)) Empty)))
-- This is a direct consequence of our requirement that priority of
-- element being inserted and bound on the Heap we insert into match.

-- Again, findMin and deletMin are incomplete
findMin :: forall (p :: Nat). Heap p -> Nat
findMin Empty            = undefined
findMin (Node p _ _ _ _) = fromSing p

-- deleteMin requires a bit more work than previously. First, notice
-- that the bound placed on the input and output heaps is the
-- same. This happens because relation between priorities in a node
-- and it's children is ≥, not > (ie. equality is allowed). We cannot
-- therefore guearantee that bound on priority will increase after
-- removing highest-priority element from the Heap. When we merge
-- left and right subtrees we need to lift their bounds so they are
-- now both b (not p).
deleteMin :: forall b. Heap b -> Heap b
deleteMin Empty               = undefined
deleteMin (Node _ _ pgeb l r) = merge (liftBound pgeb l) (liftBound pgeb r)
