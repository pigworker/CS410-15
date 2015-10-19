module Lec6 where

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

module Eval where
  open Applicative maybeApplicative public

  eval : Hutton -> Maybe Nat
  eval (val x) = yes x
  eval (h +H h') = pure _+N_ <*> eval h <*> eval h'
  eval fail = no


listTrav : forall {F} -> Applicative F -> forall {A B} ->
           (A -> F B) -> List A -> F (List B)
listTrav {F} appF = trav where
  open Applicative appF
  trav : forall {A B} -> (A -> F B) -> List A -> F (List B)
  trav f []         = pure []
  trav f (a :: as)  = pure _::_ <*> f a <*> trav f as

listTraversable : Traversable List
listTraversable = record { traverse = listTrav }

I : Set -> Set
I X = X

iApplicative : Applicative I
iApplicative = record
  { pure = id
  ; _<*>_ = id
  ; identity = \ v -> refl
  ; composition = \ f g v -> refl
  ; homomorphism = \ f x -> refl
  ; interchange = \ u y -> refl
  }

lmap : forall {A B} -> (A -> B) -> List A -> List B
lmap = traverse iApplicative where
  open Traversable listTraversable

MonCon : forall {X} -> Monoid X -> Applicative \_ -> X
MonCon M = record
             { pure          = {!!}
             ; _<*>_         = op
             ; identity      = {!!}
             ; composition   = {!!}
             ; homomorphism  = {!!}
             ; interchange   = {!!}
             } where open Monoid M

lCombine : forall {A X} -> Monoid X -> (A -> X) -> List A -> X
lCombine M = traverse (MonCon M) {B = One} where
  open Traversable listTraversable

CurryApplicative : forall {E} -> Applicative \X -> E -> X
CurryApplicative = record
                     { pure = \ x e -> x  -- K
                     ; _<*>_ = \ ef ex e -> ef e (ex e)  -- S
                     ; identity = λ {X} v → refl
                     ; composition = λ {X} {Y} {Z} u v w → refl
                     ; homomorphism = λ {X} {Y} f x → refl
                     ; interchange = λ {X} {Y} u y → refl
                     }


