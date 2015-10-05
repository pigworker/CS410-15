module Ex2 where

----------------------------------------------------------------------------
-- EXERCISE 2 -- STRUCTURE WITH VECTORS
--
-- VALUE:     15%
-- DEADLINE:  5pm, Friday 23 October (week 2)
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
  unzipped : {!!} -> Unzippable {!!}
  
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

