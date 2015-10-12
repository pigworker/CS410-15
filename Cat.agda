module Cat where

open import Agda.Primitive
open import CS410-Prelude
open import CS410-Nat
open import CS410-Monoid
open import CS410-Vec

record Cat {k}{l}(O : Set k)(_>>_ : O -> O -> Set l) : Set (lsuc (k ⊔ l)) where
  field
    -- OPERATIONS ---------------------------------------------------------
    iden  : {X : O} -> X >> X
    comp  : {R S T : O} -> S >> T -> R >> S -> R >> T
    -- KLUDGE -------------------------------------------------------------
    Eq : {S T : O} -> S >> T -> S >> T -> Set l
    -- LAWS ---------------------------------------------------------------
    idenL : {S T : O}(f : S >> T) -> Eq (comp iden f) f
    idenR : {S T : O}(f : S >> T) -> Eq (comp f iden) f
    assoc : {Q R S T : O}(f : S >> T)(g : R >> S)(h : Q >> R) ->
            Eq (comp f (comp g h)) (comp (comp f g) h)

SetCat : Cat Set (\ S T -> S -> T)
SetCat = record
           { iden = id
           ; comp = _o_
           ; Eq    = \ f g -> forall x -> f x == g x
           ; idenL = λ {S} {T} f x → refl
           ; idenR = λ {S} {T} f x → refl
           ; assoc = λ {Q} {R} {S} {T} f g h x → refl
           }

N>=Cat : Cat Nat _N>=_
N>=Cat = record
           { iden = \ {n} -> N>=refl n
           ; comp = \ {l}{m}{n} -> N>=trans l m n
           ; Eq = \ _ _ -> One
           ; idenL = λ {S} {T} f → <>
           ; idenR = λ {S} {T} f → <>
           ; assoc = λ {Q} {R} {S} {T} f g h → <>
           } where
           N>=refl : (n : Nat) -> n N>= n
           N>=refl zero = <>
           N>=refl (suc n) = N>=refl n
           N>=trans : forall l m n -> m N>= n -> l N>= m -> l N>= n
           N>=trans l m zero mn lm = <>
           N>=trans l zero (suc n) () lm
           N>=trans zero (suc m) (suc n) mn ()
           N>=trans (suc l) (suc m) (suc n) mn lm = N>=trans l m n mn lm

MonCat : forall {X} -> Monoid X -> Cat One \ _ _ -> X
MonCat M = record
             { iden = e
             ; comp = op
             ; Eq = _==_
             ; idenL = lunit
             ; idenR = runit
             ; assoc = assoc
             } where open Monoid M

record Functor {k l}{ObjS : Set k}{_>S>_ : ObjS -> ObjS -> Set l}
               {m n}{ObjT : Set m}{_>T>_ : ObjT -> ObjT -> Set n}
               (CS : Cat ObjS _>S>_)(CT : Cat ObjT _>T>_)
               : Set (lsuc (k ⊔ l ⊔ m ⊔ n)) where
  open Cat
  field
    -- OPERATIONS ---------------------------------------------------------
    Map      : ObjS -> ObjT
    map      : {A B : ObjS} -> A >S> B -> Map A >T> Map B
    -- LAWS ---------------------------------------------------------------
    mapId    : {A : ObjS} -> Eq CT (map (iden CS {A})) (iden CT {Map A})
    mapComp  : {A B C : ObjS}(f : B >S> C)(g : A >S> B) ->
               Eq CT (map (comp CS f g)) (comp CT (map f) (map g))
    mapEq    : {A B : ObjS}{f g : A >S> B} ->
               Eq CS f g -> Eq CT (map f) (map g)


data List (X : Set) : Set where  -- X scopes over the whole declaration...
  []    : List X                 -- ...so you can use it here...
  _::_  : X -> List X -> List X  -- ...and here.
infixr 3 _::_

listMap : {A B : Set} → (A → B) → List A → List B
listMap f [] = []
listMap f (a :: as) = f a :: listMap f as

list : Functor SetCat SetCat
list = record
  { Map = List
  ; map = listMap
  ; mapId = {!!}
  ; mapComp = {!!}
  ; mapEq = {!!}
  }


{-
goo : Functor (MonCat +Mon) SetCat
goo = ?
-}

hoo : (X : Set) -> Functor N>=Cat SetCat
hoo X = record
  { Map = Vec X
  ; map = {!!}
  ; mapId = {!!}
  ; mapComp = {!!}
  ; mapEq = {!!}
  }

