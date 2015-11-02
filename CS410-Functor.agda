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
    identity     : forall {X}(v : T X) ->

                      pure id <*> v == v
                      
    composition  : forall {X Y Z}(u : T (Y -> Z))(v : T (X -> Y))(w : T X) ->
    
                      pure (\ f g x -> f (g x)) <*> u <*> v <*> w == u <*> (v <*> w)
                      
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
          pure (\ x -> f (g x)) <*> x == pure f <*> (pure g <*> x)
    lem {X}{Y}{Z} f g x rewrite
        (sym (composition (pure f) (pure g) x))
      | (sym (homomorphism (\ (f : Y -> Z)(g : X -> Y) x -> f (g x)) f))
      | (sym (homomorphism (\ (g : X -> Y) x -> f (g x)) g))
      = refl

record Traversable (T : Set -> Set) : Set1 where
  field
    -- OPERATIONS ----------------------------------------------
    traverse  : forall {F} -> Applicative F ->
                forall {A B} -> (A -> F B) -> T A -> F (T B)
    -- LAWS ----------------------------------------------------
    -- maybe later

record Monad (T : Set -> Set) : Set1 where
  field
    -- OPERATIONS ----------------------------------------------
    return       : forall {X} -> X -> T X
    _>>=_        : forall {X Y} -> T X -> (X -> T Y) -> T Y
    -- LAWS ----------------------------------------------------
    law1 : forall {X Y}(x : X)(f : X -> T Y) -> return x >>= f == f x
    law2 : forall {X}(t : T X) -> t >>= return == t
    law3 : forall {X Y Z}(f : X -> T Y)(g : Y -> T Z)(t : T X) ->
           (t >>= f) >>= g == t >>= (\ x -> f x >>= g)  
  -- DERIVED OPERATIONS
  _<=<_ : {X Y Z : Set} -> (Y -> T Z) -> (X -> T Y) -> (X -> T Z)
  (f <=< g) x = g x >>= f

    
  infixr 5 _>>=_

record Monad-Alg {T : Set -> Set}(M : Monad T) : Set1 where
  field
    -- OPERATIONS ----------------------------------------------
    A : Set
    A-map : forall {X} -> (X -> A) -> T X -> A
  open Monad M
     -- LAWS ----------------------------------------------------   
  field
    A-law1 : forall {X}(f : X -> A)(x : X) -> A-map f (return x) == f x
    A-law2 : forall {X Y}(g : X -> T Y)(f : Y -> A)(t : T X) ->
             A-map (A-map f o g) t == A-map f (t >>= g)
