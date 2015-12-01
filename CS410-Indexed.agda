{-# OPTIONS --copatterns #-}

module CS410-Indexed where

open import CS410-Prelude
open import CS410-Nat

-- some notation for working with indexed sets

_-:>_ _*:_ _+:_ : {I : Set}(S T : I -> Set) -> I -> Set

(S -:> T) i = S i -> T i   -- index-respecting functions
(S *: T) i = S i * T i     -- index-matching pairs
(S +: T) i = S i + T i     -- index-consistent choice

infixr 3 _-:>_
infixr 5 _*:_

-- wrapping in the brackets means "works for all indices"

[_] : {I : Set}(X : I -> Set) -> Set
[ X ] = forall {i} -> X i


-- each set I gives us a category, I -> Set, whose objects are
-- indexed sets A : I -> Set, and whose arrows are
-- things in [ A -:> B ]

-- what is a functor between categories of indexed sets?

record FunctorIx {I J : Set}(F : (I -> Set) -> (J -> Set)) : Set1 where
  field
    mapIx : {A B : I -> Set} -> [ A -:> B ] -> [ F A -:> F B ]

-- what is a monad on indexed sets?
-- it's the usual kit for monads, instantiated for the kinds of
-- "arrows" that we use for indexed sets, the index-respecting functions

record MonadIx {W : Set}(F : (W -> Set) -> (W -> Set)) : Set1 where
  field
    retIx : forall {P} -> [ P -:> F P ]
    extendIx : forall {P Q} -> [ P -:> F Q ] -> [ F P -:> F Q ]
  _?>=_ : forall {P Q w} ->
          F P w -> (forall {v} -> P v -> F Q v) -> F Q w
  fp ?>= k = extendIx k fp

-- every MonadIx gives a FunctorIx

monadFunctorIx : forall {W}{F} -> MonadIx {W} F -> FunctorIx {W}{W} F
monadFunctorIx M = record { mapIx = \ f -> extendIx (retIx o f) }
  where open MonadIx M

-- indexed containers, also known as interaction strutures, give us
-- functors

record _=>_ (I J : Set) : Set1 where
  constructor _<!_/_
  field
    Shape     : J -> Set
    Position  : (j : J) -> Shape j -> Set
    index     : (j : J)(s : Shape j) -> Position j s -> I

IC : forall {I J} -> I => J -> (I -> Set) -> (J -> Set)
IC {I}{J} C X j = Sg (Shape j) \ s -> (p : Position j s) -> X (index j s p)
  where open _=>_ C

icFunctorIx : forall {I J}(C : I => J) -> FunctorIx (IC C)
icFunctorIx C = record { mapIx = \ {f (s , k) -> s , \ p -> f (k p) }  }
  where open _=>_ C

-- iterating an indexed container whose input (child) and output (parent) index
-- types are the same gives us "strategy trees"

data FreeIx {I}(C : I => I)(X : I -> Set)(i : I) : Set where
  ret : (X -:> FreeIx C X) i
  do  : (IC C (FreeIx C X) -:> FreeIx C X) i

-- and they're monadic

freeMonadIx : forall {I}(C : I => I) -> MonadIx (FreeIx C)
freeMonadIx C = record { retIx = ret ; extendIx = graft } where
  graft : forall {P Q} -> [ P -:> FreeIx C Q ] -> [ FreeIx C P -:> FreeIx C Q ]
  graft k (ret p) = k p
  graft k (do (s , f)) = do (s , \ p -> graft k (f p))

-- potentially infinite strategies

data Iterating {I}(C : I => I)(X : I -> Set)(i : I) : Set

record IterIx {I}(C : I => I)(X : I -> Set)(i : I) : Set where
  coinductive
  constructor step
  field
    force : Iterating C X i
open IterIx public

data Iterating {i} C X i where
  ret : (X -:> Iterating C X) i
  do  : (IC C (IterIx C X) -:> Iterating C X) i

iterMonadIx : forall {I}(C : I => I) -> MonadIx (IterIx C)
iterMonadIx C = record { retIx = retHelp ; extendIx = extHelp } where
  open _=>_ C
  retHelp : forall {P} -> [ P -:> IterIx C P ]
  force (retHelp p) = ret p
  extHelp : forall {P Q} -> [ P -:> IterIx C Q ] -> [ IterIx C P -:> IterIx C Q ]
  force (extHelp k t) with force t
  force (extHelp k t) | ret p = force (k p)
  force (extHelp k t) | do (s , f)  = do (s , \ p -> extHelp k (f p))
