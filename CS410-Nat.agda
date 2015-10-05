{-# OPTIONS --allow-unsolved-metas #-}

module CS410-Nat where

open import CS410-Prelude
open import CS410-Monoid

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

_+N_ : Nat -> Nat -> Nat
zero  +N n = n
suc m +N n = suc (m +N n)

{-+}
+Mon : Monoid Nat
+Mon = record   {
  e     = 0     ;
  op    = _+N_  ;
  lunit = {!!}  ;
  runit = {!!}  ;
  assoc = {!!}  }
  where
    -- lemmas go here
{+-}
