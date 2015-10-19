module Lec8 where

open import CS410-Prelude
open import CS410-Functor
open import CS410-Monoid
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

data Hutton : Set where
  val : Nat -> Hutton
  _+H_ : Hutton -> Hutton -> Hutton
  hif_then_else_ : Hutton -> Hutton -> Hutton -> Hutton
  fail : Hutton

maybeApplicative : Applicative Maybe
maybeApplicative = record
                     { pure = yes
                     ; _<*>_ = \ { no mx -> no
                                 ; (yes f) no -> no
                                 ; (yes f) (yes x) -> yes (f x)
                                 }
                     ; identity = \ {(yes x) -> refl ; no -> refl}
                     ; composition = \
                        { (yes f) (yes g) (yes x) -> refl
                        ; (yes f) (yes g) no -> refl
                        ; (yes x) no mx -> refl
                        ; no mg mx -> refl
                        }
                     ; homomorphism = \ f x -> refl
                     ; interchange = \ { (yes f) y -> refl ; no y → refl }
                     }

open Applicative maybeApplicative public

cond : Nat -> Nat -> Nat -> Nat
cond zero t e = e
cond (suc c) t e = t

_>>=_ : forall {X Y} -> Maybe X -> (X -> Maybe Y) -> Maybe Y
yes x >>= x2my = x2my x
no >>= x2my = no

eval : Hutton -> Maybe Nat
eval (val x) = pure x
eval (h +H h') = pure _+N_ <*> eval h <*> eval h'
eval (hif c then t else e)
  -- = pure cond <*> eval c <*> eval t <*> eval e  -- oops
  = eval c >>= \ { zero -> eval e
                 ; (suc _) -> eval t}
eval fail = no

foo : Hutton
foo = hif val 1 then (val 2 +H val 3) else (hif val 0 then val 4 else val 6)

goo : Hutton
goo = hif val 1 then (val 2 +H val 3) else (hif val 0 then fail else val 6)

ap : forall {X Y} -> Maybe (X -> Y) -> Maybe X -> Maybe Y
ap mf mx = mf >>= \ f -> mx >>= \ x -> yes (f x)
