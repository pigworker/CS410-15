module CS410-Functor where

open import CS410-Prelude

record Functor (T : Set -> Set) : Set1 where
  field
    -- OPERATIONS ----------------------------------------------
    map     : forall {X Y} -> (X -> Y) -> T X -> T Y
    -- LAWS ----------------------------------------------------
    mapid   : forall {X}(x : T X) -> map id x == x
    mapcomp : forall {X Y Z}(f : Y -> Z)(g : X -> Y)(x : T X) ->
              map (f o g) x == map f (map g x)

record Applicative (T : Set -> Set) : Set1 where
  field
    -- OPERATIONS ----------------------------------------------
    pure         : forall {X} -> X -> T X
    _<*>_        : forall {X Y} -> T (X -> Y) -> T X -> T Y
    -- LAWS ----------------------------------------------------
    identity     : forall {X}(v : T X) -> pure id <*> v == v
    composition  : forall {X Y Z}(u : T (Y -> Z))(v : T (X -> Y))(w : T X) ->
                   pure _o_ <*> u <*> v <*> w == u <*> (v <*> w)
    homomorphism : forall {X Y}(f : X -> Y)(x : X) ->
                   pure (f x) == pure f <*> pure x
    interchange  : forall {X Y}(u : T (X -> Y))(y : X) ->
                   u <*> pure y == pure (\ f -> f y) <*> u
  infixl 10 _<*>_


App2Fun : {T : Set -> Set} -> Applicative T -> Functor T
App2Fun {T} app = record {
  map     = \ f x -> pure f <*> x;
  mapid   = identity;
  mapcomp = lem}
  where
    open Applicative app
    lem : forall {X Y Z}(f : Y -> Z)(g : X -> Y)(x : T X) ->
          pure (f o g) <*> x == pure f <*> (pure g <*> x)
    lem {X} f g x
      rewrite homomorphism (_o_ f) g | homomorphism (_o_ {X = X}) f =
        composition (pure f) (pure g) x

record Traversable (T : Set -> Set) : Set1 where
  field
    -- OPERATIONS ----------------------------------------------
    traverse  : forall {F} -> Applicative F ->
                forall {A B} -> (A -> F B) -> T A -> F (T B)
    -- LAWS ----------------------------------------------------
    -- maybe later
