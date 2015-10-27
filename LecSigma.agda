module LecSigma where

open import CS410-Prelude

-- look in the Prelude

-- talk about *
-- talk about +

-- command-response systems

_<|_ : (C : Set)(R : C -> Set) -> Set -> Set
(C <| R) X = Sg C (\ c -> R c -> X)

-- the free monad on a command-response system

data Free (C : Set)(R : C -> Set)(X : Set) : Set where
  ret : X -> Free C R X
  do : (C <| R) (Free C R X) -> Free C R X

-- tree-like data

-- shapes and positions

