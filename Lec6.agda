module Lec6 where

open import CS410-Prelude
open import CS410-Functor
open import CS410-Nat

data Maybe (X : Set) : Set where
  yes  : X -> Maybe X
  no   : Maybe X

maybeFunctor : Functor Maybe
maybeFunctor = record
 { map      = \ { f (yes x) -> yes (f x)
                ; f no      -> no
                }
 ; mapid    = \ { (yes x) -> refl ; no -> refl }
 ; mapcomp  = \ { f g (yes x) -> refl ; f g no -> refl } }

open Functor maybeFunctor

data List (X : Set) : Set where  -- X scopes over the whole declaration...
  []    : List X                 -- ...so you can use it here...
  _::_  : X -> List X -> List X  -- ...and here.
infixr 3 _::_

may-take : {X : Set} -> Nat -> List X -> Maybe (List X)
may-take zero xs = yes []
may-take (suc n) [] = no
may-take (suc n) (x :: xs) = map (_::_ x) (may-take n xs)

data Hutton : Set where
  val : Nat -> Hutton
  _+H_ : Hutton -> Hutton -> Hutton
  fail : Hutton

maybeApplicative : Applicative Maybe
maybeApplicative = record
                     { pure = yes
                     ; _<*>_ = \ { no mx -> no
                                 ; (yes f) no -> no
                                 ; (yes f) (yes x) -> yes (f x)
                                 }
                     ; identity = {!!}
                     ; composition = {!!}
                     ; homomorphism = {!!}
                     ; interchange = {!!}
                     }

open Applicative maybeApplicative

eval : Hutton -> Maybe Nat
eval (val x) = yes x
eval (h +H h') = pure _+N_ <*> eval h <*> eval h'
eval fail = no
