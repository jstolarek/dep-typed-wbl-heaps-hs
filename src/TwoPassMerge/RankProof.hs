----------------------------------------------------------------------
-- Copyright: 2014, Jan Stolarek, Politechnika Łódzka     --
--                                                                  --
-- License: See LICENSE file in root of the repo                    --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps-hs   --
--                                                                  --
-- Weight biased leftist heap that proves rank invariant: size of   --
-- left subtree of a node is not smaller than size of right         --
-- subtree. Uses a two-pass merging algorithm.                      --
----------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}
module TwoPassMerge.RankProof where



import Basics

-- To prove the rank invariant we will index each Heap by its size,
-- (remember that size of a heap is its rank). Therefore index of
-- value n says that a Heap stores n elements. When merging two heaps
-- we will use the index to ensure that rank invariant is maintained.
--
-- Again, Heap has two constructor:
--
--  1) empty constructs a heap containing no elements. Therefore the
--     index is 0.
--
--  2) node takes two subtrees: one containing l elements, the other
--     containing r elements. The size of resulting heap is the sum of
--     l and r plus one for the element stored by the node itself. To
--     enforce the rank invariant node constructor expects a proof
--     that invariant holds: a value of type l ≥ r. If we can
--     construct value of this type then it proves the invariant.
data Heap :: Nat -> * where
  Empty :: Heap Zero
  Node  :: Priority -> GEq l r -> Heap l -> Heap r -> Heap (Succ (l :+ r))

-- Since rank is now an index we no longer need rank function to
-- extract Rank from a node. We can pattern match on the index
-- instead.
rank :: Heap l -> Sing l
rank Empty          = SZero
rank (Node _ _ l r) = SSucc (rank l %:+ rank r)

-- Singleton heap stores only one element. Therefore it has size of
-- one. To prove the rank invariant we must show that 0 ≥ 0. We
-- construct a value of this type using ge0 constructor.
singleton :: Priority -> Heap One
singleton p = Node p GeZ Empty Empty

-- Note [Proving rank invariant (merge using makeT)]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- Proving the rank invariant itself is surprisingly simple. We just
-- need to supply a proof that rank of left subtree is not smaller
-- than rank of right subtree. We can easily obtain evidence that it
-- is so by using order function which return result of comparing two
-- natural numbers (which will be tree ranks in this case) together
-- with a proof of the result.
--
-- But there is a different difficulty here. Since we index heaps by
-- their size we now require that makeT and merge construct trees of
-- correct size. Prooving this requires some substantial work on our
-- side.
--
-- We need to prove that the size of merged heap is equal to the sum
-- of sizes of heaps being merged. Recall that our merging algorithm
-- is two pass: we use merge to actually do the merging and makeT to
-- restore the rank invariant if necessary (see Note [Two-pass merging
-- algorithm]). This means our proof will be two-stage. We need to
-- prove that:
--
--  1) makeT creates a node of required size, even if it swaps left
--     and right children.
--
--  2) recursive calls to merge produce heaps of required size.

-- Note [Proving makeT]
-- ~~~~~~~~~~~~~~~~~~~~
--
-- makeT takes two subtrees of size l and r and produces a new tree of
-- size 1 + l + r. We must prove that each of two cases of makeT
-- returns tree of correct size:
--
--  1) size of l is ≥ than size of r: no extra proof is necessary as
--     everything follows from the definition of +.
--
--  2) size of r is ≥ than size of l: in this case we swap left and
--     right subtrees. This requires us to prove that:
--
--       suc (r + l) :~: suc (l + r)
--
--     That proof is done using congruence on suc function and
--     commutativity of addition. We will define that proof as
--     makeT-lemma as we will be using in subsequent proofs.

makeTlemma :: forall (a :: Nat) (b :: Nat).
              Sing a -> Sing b -> (Succ (a :+ b)) :~: (Succ (b :+ a))
makeTlemma a b = cong SSucc (plusComm a b)

makeT :: forall (l :: Nat) (r :: Nat).
         Sing l -> Sing r -> Priority -> Heap l -> Heap r -> Heap (Succ (l :+ r))
makeT lRank rRank p l r = case order lRank rRank of
  Ge lger -> Node p lger l r
  Le rgel -> gcastWith (makeTlemma rRank lRank) (Node p rgel r l)


-- Note [Notation for proving heap merge]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- In the proofs of heap merge we will use following notation:
--
--  h1, h2 - rank of heaps being merged
--  p1, p2 - priority of root element
--  l1     - rank of left  subtree in the first  heap
--  r1     - rank of right subtree in the first  heap
--  l2     - rank of left  subtree in the second heap
--  r2     - rank of right subtree in the second heap
--
-- Note that:
--
--    h1 = suc (l1 + r1)
--    h2 = suc (l2 + r2)
--
--     h1         h2
--
--     p1         p2
--    /  \       /  \
--   /    \     /    \
--  l1    r1   l2    r2


-- Note [Proving merge]
-- ~~~~~~~~~~~~~~~~~~~~
--
-- We need to prove that all four cases of merge (see [Two-pass merging
-- algorithm]) produce heap of required size, which is h1 + h2. Since
-- in the proofs we will always operate on l1, r1, l2 and r2 we have:
--
--   h1 + h2 ̄:~: suc (l1 + r1) + suc (l2 + r2)
--           :~: suc ((l1 + r1) + suc (l2 + r2))
--
-- (Second transformation comes from definition of +). This is the
-- expected size and therefore the final result we must prove in every
-- case that we analyze.

-- It is best to study the implementation of merge now and then read
-- the explanation of proofs.

-- Note [merge, proof 0a]
-- ~~~~~~~~~~~~~~~~~~~~~~
--
-- h1 :~: 0, therefore: h1 + h2 :~: 0 + h2 :~: h2 ∎
--
-- This is definitional equality based on _+_
--
-- ∎

-- Note [merge, proof 0b]
-- ~~~~~~~~~~~~~~~~~~~~~~
--
-- h2 :~: 0, therefore expected size is h1 + h2 :~: h1 + 0. We need to
-- show that:
--
--    h1 :~: h1 + 0
--
-- This is a simple statement that 0 is right identity of addition. We
-- proved that as one of basic properties of addition in
-- Basics.Reasoning module, except our proof had the sides of equality
-- reversed, ie. we proved a + 0 :~: a, not a :~: a + 0). We use symmetry
-- to construct a proof of latter from the former.
--
-- ∎

-- Note [merge, proof 1]
-- ~~~~~~~~~~~~~~~~~~~~~
--
-- We have p1 < p2. We keep p1 as the root and need to prove that
-- merging r1 with h2 gives correct size.  Here's how the term that
-- performs the merge corresponds to its type (for the sake of
-- readability I elided implict parameters):
--
--   makeT p1 x1 l1 (merge r1 (node p2 l2≥r2 l2 r2))
--    |          |         |   \__________________/
--    |   +------+         |            |
--    |   |     +----------+            |
--    |   |     |             +---------+
--    |   |     |     ________|__
--    |   |     |    /           \
--   suc (l1 + (r1 + suc (l2 + r2)))
--
-- Formally:
--
--   suc (l1 + (r1 + suc (l2 + r2))) :~: suc ((l1 + r1) + suc (l2 + r2))
--
-- Recall that RHS of this equality comes from [Proving merge]. We
-- begin proof with congruence on suc:
--
--   cong suc X
--
-- where X proves
--
--   l1 + (r1 + suc (l2 + r2)) :~: (l1 + r1) + suc (l2 + r2)
--
-- Substituting a = l1, b = r1 and c = suc (l2 + r2) we have
--
--   a + (b + c) :~: (a + b) + c
--
-- Which is associativity of addition that we have already proved in
-- Basics.Reasoning.
--
-- ∎

proof1 :: forall (l1 :: Nat) (r1 :: Nat) (l2 :: Nat) (r2 :: Nat).
       Sing l1 -> Sing r1 -> Sing l2 -> Sing r2 ->
       (Succ ( l1 :+ (r1 :+ Succ (l2 :+ r2))) :~: Succ ((l1 :+ r1) :+ Succ (l2 :+ r2)))
proof1 l1 r1 l2 r2 = cong SSucc (plusAssoc l1 r1 (SSucc (l2 %:+ r2)))

-- Note [merge, proof 2]
-- ~~~~~~~~~~~~~~~~~~~~~
--
-- We have p2 < p1. We keep p2 as the root and need to prove that
-- merging r2 with h1 gives correct size. Again, here's the
-- corespondence between the term and its type:
--
--   makeT p2 x2 l2 (merge r2 (node p1 l1≥r1 l1 r1))
--    |          |         |   \_________________/
--    |   +------+         |            |
--    |   |     +----------+  +---------+
--    |   |     |     ________|__
--    |   |     |    /           \
--   suc (l2 + (r2 + suc (l1 + r1)))
--
-- Formally:
--
--   suc (l2 + (r2 + suc (l1 + r1))) :~: suc ((l1 + r1) + suc (l2 + r2))
--
-- Again we use cong to deal with the outer calls to suc and
-- substitute a = l2, b = r2 and c = l1 + r1. This leaves us with a
-- proof of lemma A:
--
--   a + (b + suc c) :~: c + suc (a + b)
--
-- From associativity we know that:
--
--   a + (b + suc c) :~: (a + b) + suc c
--
-- If we prove lemma B:
--
--  (a + b) + suc c = c + suc (a + b)
--
-- we can combine it using transitivity to get the final proof. We can
-- rewrite lemma B as:
--
--    n + suc m :~: m + suc n
--
-- where n = a + b and m = c. From symmetry of +suc we have:
---
--   n + (suc m) :~: suc (n + m)
--
-- Using transitivity we combine it with congruence on commutativity
-- of addition to prove:
--
--   suc (n + m) :~: suc (m + n)
--
-- Again, using transitivity we combine it with +suc:
--
--   suc (m + n) :~: m + suc n
--
-- Which proves lemma B and therefore the whole proof is complete.
--
-- ∎

lemmaB :: forall (n :: Nat) (m :: Nat).
          Sing n -> Sing m -> ((n :+ Succ m) :~: (m :+ Succ n))
lemmaB n m = trans (sym (plusSucc n m)) (trans (cong SSucc (plusComm n m)) (plusSucc m n))

lemmaA :: forall (a :: Nat) (b :: Nat) (c :: Nat).
          Sing a -> Sing b -> Sing c ->
          ((a :+ (b :+ Succ c)) :~: (c :+ Succ (a :+ b)))
lemmaA a b c = trans (plusAssoc a b (SSucc c)) (lemmaB (a %:+ b) c)

proof2 :: forall (l1 :: Nat) (r1 :: Nat) (l2 :: Nat) (r2 :: Nat).
       Sing l1 -> Sing r1 -> Sing l2 -> Sing r2 ->
       (Succ (l2 :+ (r2  :+ Succ (l1 :+ r1))))
       :~: (Succ ((l1 :+ r1) :+ Succ (l2 :+ r2)))
proof2 l1 r1 l2 r2 = cong SSucc (lemmaA l2 r2 (l1 %:+ r1))

-- Note [Constructing equality proofs using transitivity]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- Now that constructed two specific proofs we can focus on a more
-- general technique used in both cases. Let's rewrite proof-2 in a
-- different fassion to see closely what is happening at each
-- step. Inlining lemmas A and B into proof-2 gives:
--
--   proof-2i : (l1 r1 l2 r2 : Nat) → suc (l2 + (r2  + suc (l1 + r1)))
--                                  :~: suc ((l1 + r1) + suc (l2 + r2))
--   proof-2i l1 r1 l2 r2 =
--     cong suc (trans (+assoc l2 r2 (suc (l1 + r1)))
--              (trans (sym (+suc (l2 + r2) (l1 + r1)))
--              (trans (cong suc (+comm (l2 + r2) (l1 + r1)))
--                     (+suc (l1 + r1) (l2 + r2))))
--
-- We see a lot of properties combined using transitivity. In general,
-- if we have to prove:
--
--   a :~: e
--
-- and we can prove:
--
--   a :~: b, b :~: c, c :~: d, d :~: e
--
-- then we can combine these proofs using transitivity:
--
--   trans (a :~: b) (trans (b :~: c) (trans (c :~: d) (d :~: e)))
--
-- While simple to use, combining proofs with transitivity can be not
-- so obvious at first. Let's rewrite the proof we have conducted
-- using following notation:
--
--  a :~:[ proof 1 ]
--  b :~:[ proof 2 ]
--  c :~:[ proof 3 ]
--  d :~:[ proof 4 ]
--  e ∎
--
-- Where proof 1 proves a :~: b, proof 2 proves b :~: c and so on. In our
-- particular case this will be:
--
--  suc  (l2 + (r2 + suc (l1 + r1))) :~:[ cong suc ]
-- [suc]  l2 + (r2 + suc (l1 + r1))  :~:[+assoc l2 r2 (suc (l1 + r1))]
-- [suc] (l2 + r2) + suc (l1 + r1)   :~:[ sym (+suc (l2 + r2) (l1 + r1))]
-- [suc] suc ((l2 + r2) + (l1 + r1)) :~:[ cong suc (+comm (l2 + r2) (l1 + r1)) ]
-- [suc] suc ((l1 + r1) + (l2 + r2)) :~:[+suc (l1 + r1) (l2 + r2) ]
-- [suc] (l1 + r1) + suc (l2 + r2) ∎
--
-- We use [suc] to denote that everything happens under a call to suc
-- (thanks to using congruence). Compare this notation with code of
-- proof-2i.


-- Note [Notation in merge]
-- ~~~~~~~~~~~~~~~~~~~~~~~~
--
-- merge uses different notation than the proofs. We use l1, r1, l2
-- and r2 to denote the respective subtrees and l1-rank, r1-rank,
-- l2-rank and r2-rank to denote their ranks. We use h1 and h2 to
-- denote heaps.
merge :: forall (l :: Nat) (r :: Nat).
         Heap l -> Heap r -> Heap (l :+ r)
merge  Empty h2 = h2 -- See [merge, proof 0a]
merge h1 Empty
  = gcastWith (sym (plusZero (rank h1))) h1 -- See [merge, proof 0b]
merge h1@(Node p1 _ l1 r1)
      h2@(Node p2 _ l2 r2) = case p1 < p2 of
         True -> gcastWith
             (proof1 l1Rank r1Rank l2Rank r2Rank) -- See [merge, proof 1]
             (makeT l1Rank (r1Rank %:+ h2Rank) p1 l1 (merge r1 h2))
         False -> gcastWith
             (proof2 l1Rank r1Rank l2Rank r2Rank) -- See [merge, proof 2]
             (makeT l2Rank (r2Rank %:+ h1Rank) p2 l2 (merge r2 h1))
      where l1Rank = rank l1
            r1Rank = rank r1
            l2Rank = rank l2
            r2Rank = rank r2
            h1Rank = rank h1
            h2Rank = rank h2

-- We require that inserting an element into the heap increases its
-- size by one. As previously we define insert as merge and a
-- singleton heap. Size of singleton heap is (suc zero), while already
-- existing heap has size n. According to definition of merge the
-- resulting heap will therefore have size:
--
--   (suc zero) + n
--
-- By definition of + this can be normalized to:
--
--   suc (zero + n)
--
-- and finally to
--
--   suc n
--
-- Which is size we require in the type signature. This means we don't
-- need any additional proof because expected result follows from
-- definitions.
insert :: forall (n :: Nat).
          Priority -> Heap n -> Heap (Succ n)
insert p h = merge (singleton p) h

-- By indexing heap with its size we can finally have means to ensure
-- that heap passed to findMin or deleteMin is not empty.
findMin :: forall (n :: Nat).
           Heap (Succ n) -> Priority
findMin (Node p _ _ _) = p


deleteMin :: forall (n :: Nat).
             Heap (Succ n) -> Heap n
deleteMin (Node _ _ l r) = merge l r
