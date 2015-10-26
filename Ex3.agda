module Ex3 where

----------------------------------------------------------------------------
-- EXERCISE 3 -- MONADS FOR HUTTON'S RAZOR
--
-- VALUE:     15%
-- DEADLINE:  5pm, Friday 20 November (week 9)
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
-- HUTTON'S RAZOR
----------------------------------------------------------------------------

HVal : Set   -- the set of *values* for Hutton's Razor
HVal = Two + Nat   -- Booleans or natural numbers

data HExp (X : Set) : Set where
  var        : X -> HExp X                  -- variables
  val        : HVal -> HExp X               -- values
  _+H_ _>=H_ : (e1 e2 : HExp X) -> HExp X   -- addition, comparison
  ifH_then_else_ : (e1 e2 e3 : HExp X) -> HExp X  -- conditional

_>=2_ : Nat -> Nat -> Two
x      >=2  zero   = tt
zero   >=2  suc _  = ff
suc m  >=2  suc n  = m >=2 n


----------------------------------------------------------------------------
-- ??? 3.1 the HExp syntax-with-substitution monad            (score: ? / 2)
----------------------------------------------------------------------------

-- Show that HExp is a monad, where the "bind" operation performs
-- simultaneous substitution (transforming all the variables in a term).

hExpMonad : Monad HExp
hExpMonad = {!!}


----------------------------------------------------------------------------
-- ??? 3.2 the error management monad                         (score: ? / 1)
----------------------------------------------------------------------------

-- show that "+ E" is monadic, generalising the "Maybe" monad by allowing
-- some sort of error report

errorMonad : (E : Set) -> Monad \ V -> V + E   -- "value or error"
errorMonad E = {!!}


----------------------------------------------------------------------------
-- ??? 3.3 the environment monad transformer                   (score: ? / 1)
----------------------------------------------------------------------------

-- show that "+ E" is monadic, generalising the "Maybe" monad by allowing
-- some sort of error report

envMonad : (G : Set){M : Set -> Set} -> Monad M ->
           Monad \ V -> G -> M V      -- "computation in an environment"
envMonad G MM = {!!} where
  open Monad MM

----------------------------------------------------------------------------
-- ??? 3.4 interpreting Hutton's Razor                        (score: ? / 3)
----------------------------------------------------------------------------

-- Implement an interpreter for Hutton's Razor.
-- You will need to construct a type to represent possible run-time errors.
-- Ensure that addition and comparison act on numbers, not Booleans.
-- Ensure that the condition in an "if" is a Boolean, not a number.

data InterpretError : Set where

-- helpful things to build

Env : Set -> Set    -- an environment for a given set of variables
Env X = X -> HVal

Compute : Set{- variables -} -> Set{- values -} -> Set
Compute X V = Env X -> V + InterpretError  -- how to compute a V

computeMonad : {X : Set} -> Monad (Compute X)
computeMonad = {!!} -- build this from the above parts

-- This operation should explain how to get the value of a variable
-- from the environment.
varVal : {X : Set} -> X -> Compute X HVal
varVal x = {!!}

-- These operations should ensure that you get the sort of value
-- that you want, in order to ensure that you don't do bogus
-- computation.
mustBeNat : {X : Set} -> HVal -> Compute X Nat
mustBeNat v = {!!}

mustBeTwo : {X : Set} -> HVal -> Compute X Two
mustBeTwo v = {!!}

-- Now, you're ready to go. Don't introduce the environent explicitly.
-- Use the monad to thread it.

interpret : {X : Set} -> HExp X -> Env X -> HVal + InterpretError
interpret {X} = go where
  open Monad (envMonad (Env X) (errorMonad InterpretError))
  go : HExp X -> Env X -> HVal + InterpretError
  go t = {!!}
