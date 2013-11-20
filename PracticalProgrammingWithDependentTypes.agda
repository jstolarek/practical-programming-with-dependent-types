----------------------------------------------------------------------
--                                                                  --
-- Author  : Jan Stolarek                                           --
-- License : Public Domain                                          --
--                                                                  --
-- This module contains Agda implementation of code presented in    --
-- "Epigram: Practical Programming with Dependent Types" by Conor   --
-- McBride. Original code in the paper was written in Epigram, but  --
-- with its official web page offline for a couple of months        --
-- Epigram seems to be dead. Hence a rewrite in Agda.               --
--                                                                  --
-- This code is a work in progress.                                 --
--                                                                  --
-- This code was written and tested in Agda 2.3.2.1. YMMV           --
--                                                                  --
----------------------------------------------------------------------

module PracticalProgrammingWithDependentTypes where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

-- Section 2.5 : Some Familiar Datatypes
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- Definitions of some basic datatypes needed in the exercises.

data Bool : Set where
  true  : Bool
  false : Bool

data Maybe (X : Set) : Set where
  nothing : Maybe X
  just    : X → Maybe X

data List (X : Set) : Set where
  nil : List X
  cons : X → List X → List X

data Tree (N L : Set) : Set where
  leaf : L → Tree N L
  node : N → Tree N L → Tree N L → Tree N L


-- Exercise 1
-- ~~~~~~~~~~
-- Define the 'less-or-equal' test.

_≤_ : Nat → Nat → Bool
zero  ≤ y     = true
suc x ≤ zero  = false
suc x ≤ suc y = x ≤ y

-- We recurse on first argument. If decided to recurse on the second one we
-- would get:
--
-- _≤_ : Nat → Nat → Bool
-- x ≤ zero  = ?
-- x ≤ suc y = ?
--
-- and we would still have to do case analysis on x to compute the result.


-- Exercise 2
-- ~~~~~~~~~~
-- Define the conditional expression.

if_then_else_ : {X : Set} → Bool → X → X → X
if true  then x else y = x
if false then x else y = y

-- Exercise 3
-- ~~~~~~~~~~
-- Use the above to deﬁne the function which merges two lists, presumed already
-- sorted into increasing order, into one sorted list containing the elements
-- from both.

merge : List Nat → List Nat → List Nat
merge nil ys                  = ys
merge xs nil                  = xs
merge (cons x xs) (cons y ys) = if x ≤ y
                                then cons x (merge xs (cons y ys))
                                else cons y (merge (cons x xs) ys)

-- Here we need to perform structural recursion on both arguments (at least I
-- believe so).

-- Exercise 4
-- ~~~~~~~~~~
-- Use merge to implement a function ﬂattening a tree which may have numbers at
-- the leaves, to produce a sorted list of those numbers. Ignore the node
-- labels.

flatten : {N : Set} → Tree N (Maybe Nat) → List Nat
flatten (leaf nothing ) = nil
flatten (leaf (just x)) = cons x nil
flatten (node _ l r)    = merge (flatten l) (flatten r)

-- Exercise 5
-- ~~~~~~~~~~
-- Implement the insertion of a number into a tree. Maintain this balancing
-- invariant throughout: in (node true s t), s and t contain equally many
-- numbers, whilst in (node false s t), s contains exactly one more number
-- than t.

insert : Nat → Tree Bool (Maybe Nat) → Tree Bool (Maybe Nat)
insert n (leaf nothing)   = node false (leaf (just n)) (leaf nothing)
insert n (leaf (just x))  = node true  (leaf (just x)) (leaf (just n))
insert n (node true  l r) = node false (insert n l) r
insert n (node false l r) = node true  l (insert n r)

-- Exercise 6
-- ~~~~~~~~~~
-- Implement share and sort so that sort sorts its input in O(n log n) time.

share : List Nat → Tree Bool (Maybe Nat)
share ns = go ns (leaf nothing)
  where go : List Nat → Tree Bool (Maybe Nat) → Tree Bool (Maybe Nat)
        go nil         t = t
        go (cons n ns) t = go ns (insert n t)

sort : List Nat → List Nat
sort ns  = flatten (share ns)

-- Comment on Exercises 1-6
-- ~~~~~~~~~~~~~~~~~~~~~~~~
-- Exercises 1-6 implement merge sorting algorithm presented in "Why Dependent
-- Types Matter" by Thorsten Altenkirch, Conor McBride and James McKinna
-- (Section 3.2, Figure 2 in that paper).
