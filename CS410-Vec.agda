{-# OPTIONS --allow-unsolved-metas #-}

module CS410-Vec where

open import CS410-Nat

data Vec (X : Set) : Nat -> Set where
  []   : Vec X 0
  _::_ : forall {n} ->
         X -> Vec X n -> Vec X (suc n)
infixr 3 _::_

_+V_ : forall {X m n} -> Vec X m -> Vec X n -> Vec X (m +N n)
[] +V ys = ys
(x :: xs) +V ys = x :: xs +V ys
infixr 3 _+V_
