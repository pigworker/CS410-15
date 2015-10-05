{-# OPTIONS --allow-unsolved-metas #-}

module CS410-Vec where

open import CS410-Nat

data Vec (X : Set) : Nat -> Set where
  []   : Vec X 0
  _::_ : forall {n} ->
         X -> Vec X n -> Vec X (suc n)
infixr 3 _::_
