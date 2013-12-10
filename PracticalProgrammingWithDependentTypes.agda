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

-- Definitions of datatypes needed in the exercises 1-6.

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

-- Exercises: Matrix Multiplication
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- Definitions of datatypes and functions needed in the exercises 7-12.

data Vec (X : Set) : Nat → Set where
  vnil : Vec X zero
  vcons : {n : Nat} → X → Vec X n → Vec X (suc n)

vec : {n : Nat} {X : Set} → X → Vec X n
vec {zero}  x = vnil
vec {suc n} x = vcons x (vec x)

va : {n : Nat} {S T : Set} → Vec (S → T) n → Vec S n → Vec T n
va vnil         vnil         = vnil
va (vcons f fs) (vcons s ss) = vcons (f s) (va fs ss)

-- A bit of syntactic sugar
Matrix : (X : Set) → (r c : Nat) → Set
Matrix X r c = Vec (Vec X c) r

-- We represent Matrix as a Vector of rows, so c is the number of columns and r
-- is the number of rows. Note that this means that each row has c elements and
-- each column has r elements (this got me confused when I was implementing
-- matrix multiplication). Example:
--
--                [x x x x x]
-- Matrix X 3 5 = [x x x x x]
--                [x x x x x]
--
-- is stored as 3 vectors, each containing 5 elements

transpose : {X : Set} {m n : Nat} → Matrix X m n → Matrix X n m
transpose vnil         = vec vnil
transpose (vcons x xs) = va (va (vec vcons) x) (transpose xs)

-- Exercise 7
-- ~~~~~~~~~~
-- Show how vec and va can be used to generate the vector analogues of Haskell’s
-- map, zipWith, and the rest of the family.

vmap : {n : Nat} {S T : Set} → (S → T) → Vec S n → Vec T n
vmap f xs = va (vec f) xs

vZipWith : {n : Nat} {A B C : Set} → (A → B → C) → Vec A n → Vec B n → Vec C n
vZipWith f xs ys = va (vmap f xs) ys

-- Exercise 8
-- ~~~~~~~~~~
-- Implement vdot, the scalar product of two vectors of Nats.

-- For that I need addition and multiplication of Nats. Addition was
-- defined in the paper as plus, but I didn't implement it earlier as it wasn't
-- necessary.

_+_ : Nat → Nat → Nat
zero  + y = y
suc x + y = suc (x + y)

_*_ : Nat → Nat → Nat
zero  * y = zero
suc x * y = y + (x * y)

infixl 7  _*_
infixl 6  _+_

-- In this and other vector exercises that follow I assume that vectors have at
-- least one element. This isn't stated as a requirement in the exercises, but I
-- assume that this functions are meant to have a mathematical meaning and in
-- mathematics there are no 0-dimensional vectors or matrices.

vdot : {n : Nat} → Vec Nat (suc n) → Vec Nat (suc n) → Nat
vdot {zero } (vcons x vnil) (vcons y vnil) = x * y
vdot {suc n} (vcons x xs  ) (vcons y ys  ) = x * y + vdot xs ys

-- Exercise 9
-- ~~~~~~~~~~
-- How would you compute the zero matrix of a given size? Also implement a
-- function to compute any identity matrix.

vzero : {c r : Nat} → Matrix Nat (suc c) (suc r)
vzero = vec (vec zero)

-- I assume that identity matrix must be a square matrix
identity : {n : Nat} → Matrix Nat (suc n) (suc n)
identity {zero}  = vec (vec (suc zero))
identity {suc n} = vcons (vcons (suc zero) (vec zero))
                         (vZipWith vcons (vec zero) identity)

-- In the first case we create a matrix containing only `suc zero`. We could
-- write:
--
--   vcons (vcons (suc zero) vnil) vnil)
--
-- but `vec (vec (suc zero))` seems more elegant. In the second case:
--
--   vZipWith vcons (vec zero) identity
--
-- creates an identity matrix of a smaller size and adds 0 to the beginning of
-- each row in that matrix (in other words: adds column of zeros):
--
-- [1 0 0]     [0 1 0 0]
-- [0 1 0]  => [0 0 1 0]
-- [0 0 1]     [0 0 0 1]
--
-- The expression `vcons (suc zero) (vec zero)` creates a new row that
-- beggins with 1 and the outer vcons appends it to result of vZipWith:
--
--                 [0 1 0 0]     [1 0 0 0]
-- vcons [1 0 0 0] [0 0 1 0]  => [0 1 0 0]
--                 [0 0 0 1]     [0 0 1 0]
--                               [0 0 0 1]

-- Exercise 10
-- ~~~~~~~~~~~
-- Implement matrix-times-vector multiplication. (ie, interpret a Matrix m n as
-- a linear map Vec n Nat → Vec m Nat.)

-- At first I couldn't understand that analogy between matrix multiplication and
-- linear map. This was because I had my definiton of Matrix written as
--
--   Matrix X r c = Vec (Vec X r) c
--
-- instead of
--
--   Matrix X c r = Vec (Vec X r) c (note the reversed c and r on LHS)
--
-- This means I assumed c to be length of a column and r to length of a row,
-- which lead my to following signature of matrix-by-vector multiplication:
--
--   {m n : Nat} → Matrix Nat (suc m) (suc n) → Vec Nat (suc m) → Vec Nat (suc n)
--
-- There was indeed an analogy with map (Matrix m n → Vec m → Vec n), but it was
-- inconsistent with text of the exercise. It took me a moment to figure out the
-- reason for this idfference.

_**_ : {m n : Nat} → Matrix Nat (suc m) (suc n) → Vec Nat (suc n) → Vec Nat (suc m)
x ** y = vmap (λ v → vdot y v) x

-- At this point I'm beginnig to notice that writing (suc m) in all the type
-- signatures to ensure that matrices and vectors are not zero-sized is
-- tedious. I could probably do better by defining a data type similar to Fin
-- (which we will see in a moment).

-- Exercise 11
-- ~~~~~~~~~~~
-- Implement matrix-times-matrix multiplication. (ie, implement composition of
-- linear maps.)

_***_ : {i j k : Nat} → Matrix Nat (suc i) (suc j)
                      → Matrix Nat (suc j) (suc k)
                      → Matrix Nat (suc i) (suc k)
x *** y = vmap (λ v → yt ** v) x
  where yt = transpose y

-- Exercise 12 ((Mainly for Haskellers)
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- It turns out that for each n, Vec n is a monad, with vec playing the part of
-- return. What should the corresponding notion of join do? What plays the part
-- of ap?

-- Recall that for list join == concat. For vectors things are a bit trickier,
-- because we can't change size of the resulting vector. Hence we decide to
-- define join to take elements on the diagonal of a matrix defined by nested
-- Vecs. For that we will need vtail to drop first element of a vector.

vtail : {X : Set} {n : Nat} → Vec X (suc n) → Vec X n
vtail (vcons x xs) = xs

vjoin : {X : Set} {n : Nat} → Vec (Vec X n) n → Vec X n
vjoin vnil                    = vnil
vjoin (vcons (vcons x xs) vs) = vcons x (vjoin (vmap vtail vs))

-- vapp plays role of ap.

-- See also: Materials for "Dependently Typed Metaprogramming (in Agda)" by
-- Conor McBride, Exercise 1.6.
-- https://github.com/pigworker/MetaprogAgda

-- Exercises : Finite Sets
-- ~~~~~~~~~~~~~~~~~~~~~~~

data Fin : Nat → Set where
  fz : {n : Nat} → Fin (suc n)
  fs : {n : Nat} → Fin n → Fin (suc n)
-- Exercise 13
-- ~~~~~~~~~~~
-- Implement fmax (each nonempty set’s maximum value) and fweak (the function
-- preserving fz and fs, incrementing the index).

fmax : {n : Nat} → Fin (suc n)
fmax {zero}  = fz
fmax {suc n} = fs (fmax {n})

-- fweak function wasn't intuitive for me at first. The important thing is to
-- remember that index of Fin limits the maximal value represented by that data
-- type, but it might represent smaller values as well. For example, fz
-- (representing 0) might belong to Fin 1, but it might as well belong to Fin
-- 5. So the idea behind fweak is to take a value belonging to Fin and embed it
-- in a larger Fin:
--
--   fweak {3} (suc{2} zero{1}) = suc{3} zero{2}
--
-- This takes 1, belonging to Fin 3 and promotes it to Fin 4.

fweak : {n : Nat} → Fin n → Fin (suc n)
fweak fz     = fz
fweak (fs f) = fs (fweak f)

-- Exercise 14
-- ~~~~~~~~~~~
-- Implement vtab, the inverse of vproj, tabulating a function over finite sets
-- as a vector.

-- Below is vproj function as defined in the paper in Section 3.1:

vproj : {X : Set} {n : Nat} → Vec X n → Fin n → X
vproj (vcons x xs) fz     = x
vproj (vcons x xs) (fs i) = vproj xs i

-- In other words vproj is an index function (ie. given an index and a
-- vector it returns element under specified index). My understanding
-- of vtab function is that it creates vector of a given size n using
-- a function from finite set of size n to some other Set. It took me
-- a moment to get this function right, although now seeing the result
-- it is not that difficult. In the case of zero-sized vector we
-- return vnil, which is obvious. In the recursive case we apply our
-- constructing function to zero - we want our n-sized vector to begin
-- with 0-indexed element. The tricky part is the recursive call,
-- where we have to modify function passed to vtab. We increase the
-- passed parameter by one and use original f to construct new element
-- of a vector. In this way, with every recursive call, we increase by
-- one parameter passed to f.

vtab : {X : Set} {n : Nat} → (Fin n → X) → Vec X n
vtab {X} {zero}  f = vnil
vtab {X} {suc n} f = vcons (f fz) (vtab (λ i → f (fs i)))

-- As a sanity check let's define a function from Fin n to Nat that
-- acts as identity function: for fz it return zero, for (fs fz) it
-- returns (suc zero) and so on:

f : {n : Nat} → Fin n → Nat
f fz       = zero
f (fs fin) = suc (f fin)

-- When passed to vtab it will create a vector containing successive
-- natural numbers. You can verify this by pressing C-c C-n and
-- typing:
--
--   vtab {Nat} {suc (suc (suc zero))} f
--
-- which will create a vector of size three containing three
-- consecutive natural numbers: 0, 1 and 2:
--
--   vcons zero (vcons (suc zero) (vcons (suc (suc zero)) vnil))

-- Exercise 15
-- ~~~~~~~~~~~
-- Devise an inductive family, OPF m n which gives a unique first-order
-- representation of exactly the order-preserving functions in Fin m →
-- Fin n. Give your family a semantics by implementing:

-- opf : {m n : Nat} → OPF m n → Fin m → Fin n

-- Hint from #agda channel: Your encoding of an OPF from Fin (suc m)
-- to Fin n should be in terms of an OPF from Fin m to Fin n

-- I have no idea how to complete this exercise

-- Exercise 16
-- ~~~~~~~~~~~
-- Implement identity and composition:

-- iOPF : {n : Nat} → OPF n n
-- iOPF {n} = ?

-- cOPF : {m n l : Nat} → OPF m n → OPF l m → OPF l n
-- cOPF f g = ?

-- I have no idea how to complete this exercise

-- Exercise : Renaming and Substitution
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

-- Solving these exercises requires understanding of de Bruijn
-- indices. If you had no contact with the concept of de Bruijn
-- indices you need to do some additional reading. I highly recommend
-- 6th chapter of Benjamin Pierce's book "Types and Programming
-- Languages" (TAPL). In my comments I will refer to definitions given
-- in that book.

-- Definition of abstract syntax used for nameless representation of
-- terms. Index of Tm says how many free variables an expression can
-- contain.
data Tm : Nat → Set where
  var : {n : Nat} → Fin n → Tm n
  lda : {n : Nat} → Tm (suc n) → Tm n
  app : {n : Nat} → Tm n → Tm n → Tm n

-- Exercise 17
-- ~~~~~~~~~~~
-- Use wren to help you implement the renaming traversal

-- Renaming (aka "shifting") is given as definition 6.2.1 in TAPL.
-- ρ is the shifting function that renames variables if they are above
-- the cutoff threashold - see first equation in definition 6.2.1.

-- Weakening of renaming function is used when we introduce a new
-- binder with a lambda abstraction. Since now we have one more
-- binder than previously we have to modify the renaming function to
-- work on a larger range of binders.
wren : {m n : Nat} → (Fin m → Fin n) → Fin (suc m) → Fin (suc n)
wren ρ fz     = fz
wren ρ (fs i) = fs (ρ i)

ren : {m n : Nat} → (Fin m → Fin n) → Tm m → Tm n
ren ρ (var x)     = var (ρ x)
ren ρ (lda t)     = lda (ren (wren ρ) t)
ren ρ (app t1 t2) = app (ren ρ t1) (ren ρ t2)

-- Exercise 18
-- ~~~~~~~~~~~
-- Develop weakening for substitutions, then use it to go under lda in
-- the traversal.

-- Substitution is given by definition 6.2.4 in TAPL.

wsub : {m n : Nat} → (Fin m → Tm n) → Fin (suc m) → Tm (suc n)
wsub ρ fz     = var fz
wsub ρ (fs i) = ren fs (ρ i)

sub : {m n : Nat} → (Fin m → Tm n) → Tm m → Tm n
sub ρ (var x)     = ρ x
sub ρ (lda t)     = lda (sub (wsub ρ) t)
sub ρ (app t1 t2) = app (sub ρ t1) (sub ρ t2)

-- Exercise 19 (For the brave)
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- Refactor this development, abstracting the weakening-then-traversal
-- pattern. If you need a hint, see chapter 7 of [23].
