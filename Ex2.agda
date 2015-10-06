module Ex2 where

----------------------------------------------------------------------------
-- EXERCISE 2 -- STRUCTURE WITH VECTORS
--
-- VALUE:     15%
-- DEADLINE:  5pm, Friday 23 October (week 5)
--
-- DON'T SUBMIT, COMMIT!
--
-- The purpose of this exercise is to introduce you to some useful
-- mathematical structures and build good tools for working with
-- vectors
----------------------------------------------------------------------------

open import CS410-Prelude
open import CS410-Monoid
open import CS410-Nat
open import CS410-Vec
open import CS410-Functor

-- HINT: your tasks are heralded with the eminently searchable tag, "???"


----------------------------------------------------------------------------
-- ??? 2.1 replicattion to make a constant vector             (score: ? / 1)
----------------------------------------------------------------------------

vec : forall {n X} -> X -> Vec X n
vec x = {!!}

-- HINT: you may need to override default invisibility

-- SUSPICIOUS: no specification? why not?


----------------------------------------------------------------------------
-- ??? 2.2 vectorised application                             (score: ? / 1)
----------------------------------------------------------------------------

-- implement the operator which takes the same number of functions
-- and arguments and computes the applications in corresponding
-- positions

vapp : forall {n X Y} ->
       Vec (X -> Y) n -> Vec X n -> Vec Y n
vapp fs xs = {!!}


----------------------------------------------------------------------------
-- ??? 2.3 one-liners                                         (score: ? / 1)
----------------------------------------------------------------------------

-- implement map and zip for vectors using vec and vapp
-- no pattern matching or recursion permitted

vmap : forall {n X Y} -> (X -> Y) -> Vec X n -> Vec Y n
vmap f xs = {!!}

vzip : forall {n X Y} -> Vec X n -> Vec Y n -> Vec (X * Y) n
vzip xs ys = {!!}


----------------------------------------------------------------------------
-- ??? 2.4 unzipping                                          (score: ? / 2)
----------------------------------------------------------------------------

-- implement unzipping as a view, showing that every vector of pairs
-- is given by zipping two vectors

-- you'll need to complete the view type yourself

data Unzippable {X Y n} : Vec (X * Y) n -> Set where
  unzipped : {- some stuff -> -} Unzippable {!!}
  
unzip : forall {X Y n}(xys : Vec (X * Y) n) -> Unzippable xys
unzip xys = {!!}


----------------------------------------------------------------------------
-- ??? 2.5 vectors are applicative                            (score: ? / 2)
----------------------------------------------------------------------------

-- prove the Applicative laws for vectors

VecApp : forall n -> Applicative \X -> Vec X n
VecApp n = record
  { pure         = vec
  ; _<*>_        = vapp
  ; identity     = {!!}
  ; composition  = {!!}
  ; homomorphism = {!!}
  ; interchange  = {!!}
  } where
  -- lemmas go here


----------------------------------------------------------------------------
-- ??? 2.6 vectors are traversable                            (score: ? / 1)
----------------------------------------------------------------------------

-- show that vectors are traversable; make sure your traverse function
-- acts on the elements of the input once each, left-to-right

VecTrav : forall n -> Traversable \X -> Vec X n
VecTrav = {!!}


----------------------------------------------------------------------------
-- ??? 2.7 monoids make constant applicatives                 (score: ? / 1)
----------------------------------------------------------------------------

-- Show that every monoid gives rise to a degenerate applicative functor

MonCon : forall {X} -> Monoid X -> Applicative \_ -> X
MonCon M = record
             { pure          = {!!}
             ; _<*>_         = op
             ; identity      = {!!}
             ; composition   = {!!}
             ; homomorphism  = {!!}
             ; interchange   = {!!}
             } where open Monoid M


----------------------------------------------------------------------------
-- ??? 2.8 vector combine                                     (score: ? / 1)
----------------------------------------------------------------------------

-- Using your answers to 2.6 and 2.7, rather than any new vector recursion,
-- show how to compute the result of combining all the elements of a vector
-- when they belong to some monoid.

vcombine : forall {X} -> Monoid X ->
           forall {n} -> Vec X n -> X
vcombine M = {!!}


----------------------------------------------------------------------------
-- ??? 2.9 scalar product                                     (score: ? / 1)
----------------------------------------------------------------------------

-- Show how to compute the scalar ("dot") product of two vectors of numbers.
-- (Multiply elements in corresponding positions; compute total of products.)
-- HINT: think zippily, then combine

vdot : forall {n} -> Vec Nat n -> Vec Nat n -> Nat
vdot xs ys = {!!}


----------------------------------------------------------------------------
-- MATRICES
----------------------------------------------------------------------------

-- let's say that an h by w matrix is a column h high of rows w wide

Matrix : Set -> Nat * Nat -> Set
Matrix X (h , w) = Vec (Vec X w) h


----------------------------------------------------------------------------
-- ??? 2.11 identity matrix                                   (score: ? / 1)
----------------------------------------------------------------------------

-- show how to construct the identity matrix of a given size, with
-- 1 on the main diagonal and 0 everywhere else, e.g,
-- (1 :: 0 :: 0 :: []) ::
-- (0 :: 1 :: 0 :: []) ::
-- (0 :: 0 :: 1 :: []) ::
-- []

idMat : forall {n} -> Matrix Nat (n , n)
idMat = {!!}

-- HINT: you may need to do recursion on the side, but then you
-- can make good use of vec and vapp


----------------------------------------------------------------------------
-- ??? 2.10 transposition                                     (score: ? / 1)
----------------------------------------------------------------------------

-- show how to transpose matrices
-- HINT: use traverse, and it's a one-liner

transpose : forall {X m n} -> Matrix X (m , n) -> Matrix X (n , m)
transpose = {!!}


----------------------------------------------------------------------------
-- ??? 2.11 multiplication                                    (score: ? / 2)
----------------------------------------------------------------------------

-- implement matrix multiplication
-- HINT: transpose and vdot can be useful

matMult : forall {m n p} ->
          Matrix Nat (m , n) -> Matrix Nat (n , p) -> Matrix Nat (m , p)
matMult xmn xnp = {!!}
