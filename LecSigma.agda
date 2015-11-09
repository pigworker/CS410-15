module LecSigma where

open import CS410-Prelude
open import CS410-Nat
open import CS410-Functor

-- look in the Prelude

-- talk about *
-- talk about +

_N>_ : Nat -> Nat -> Set
m N> n = m N>= suc n

Fin : Nat -> Set
Fin n = Sg Nat \ m -> n N> m

foo : Fin 7
foo = 5 , <>

-- command-response systems

_<|_ : (C : Set)(R : C -> Set) -> Set -> Set
(C <| R) X = Sg C (\ c -> R c -> X)

containerFunctor : (C : Set)(R : C -> Set) -> Functor (C <| R)
containerFunctor C R = record
  { map = \ {f (c , k) -> c , (f o k)} 
  ; mapid = \ _ -> refl
  ; mapcomp = \ _ _ _ -> refl
  }

IC : Set -> Set
IC = One <| \ c -> One

LC : Set -> Set
LC = Nat <| Fin

nil : {X : Set} -> LC X
nil = 0 , (\ { (m , ()) })

cons : {X : Set} -> X -> LC X -> LC X
cons x (n , k) = (suc n) , (\
     { (zero , p) -> x
     ; (suc m , p) -> k (m , p)
     })

{-
look : {X : Set} -> IC X -> Zero
look (<> , snd) = {!!}
-}

-- the free monad on a command-response system

module FREEMONAD (C : Set)(R : C -> Set) where

  data Free (X : Set) : Set where
    ret : X -> Free X
    do : (C <| R) (Free X) -> Free X

  graft : {X Y : Set} -> Free X -> (X -> Free Y) -> Free Y
  graft fx k = {!!}

  freeMonad : Monad Free
  freeMonad = record
    {  return  = {!!}
    ;  _>>=_   = graft
    ;  law1 = {!!}
    ;  law2 = {!!}
    ;  law3 = {!!}
    }

-- tree-like data

-- shapes and positions

