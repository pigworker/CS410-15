module CS410-Prelude where

open import Agda.Primitive


----------------------------------------------------------------------------
-- Zero -- the empty type (logically, a false proposition)
----------------------------------------------------------------------------

data Zero : Set where

magic : forall {l}{A : Set l} -> Zero -> A
magic ()


----------------------------------------------------------------------------
-- One -- the type with one value (logically, a true proposition)
----------------------------------------------------------------------------

record One : Set where
  constructor <>
open One public
{-# COMPILED_DATA One () () #-}

----------------------------------------------------------------------------
-- Two -- the type of Boolean values
----------------------------------------------------------------------------

data Two : Set where tt ff : Two
{-# BUILTIN BOOL Two #-}
{-# BUILTIN TRUE tt #-}
{-# BUILTIN FALSE ff #-}
{-# COMPILED_DATA Two Bool True False #-}

-- nondependent conditional with traditional syntax
if_then_else_ : {l : Level}{X : Set l} -> Two -> X -> X -> X
if tt then t else e = t
if ff then t else e = e

-- dependent conditional cooked for partial application
caseTwo : forall {l}{P : Two -> Set l} -> P tt -> P ff -> (b : Two) -> P b
caseTwo t f tt = t
caseTwo t f ff = f


----------------------------------------------------------------------------
-- "Sigma" -- the type of dependent pairs, giving binary products and sums
----------------------------------------------------------------------------

record Sg {l : Level}(S : Set l)(T : S -> Set l) : Set l where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg public
_*_ : {l : Level} -> Set l -> Set l -> Set l
S * T = Sg S \ _ -> T
infixr 4 _,_ _*_

_+_ : Set -> Set -> Set
S + T = Sg Two (caseTwo S T)

pattern inl s = tt , s
pattern inr t = ff , t


----------------------------------------------------------------------------
-- "Equality" -- the type of evidence that things are the same
----------------------------------------------------------------------------

data _==_ {l}{X : Set l}(x : X) : X -> Set l where
  refl : x == x
infix 1 _==_
{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}

sym : forall {l}{X : Set l}{x y : X} -> x == y -> y == x
sym refl = refl

-- this proof principle is useful for proving laws, don't use it for
-- fixing type problems in your programs

postulate ext : forall {l m}{A : Set l}{B : Set m}{f g : A -> B} ->
            (forall a -> f a == g a) -> f == g

----------------------------------------------------------------------------
-- functional plumbing
----------------------------------------------------------------------------

id : forall {l}{X : Set l} -> X -> X
id x = x

-- the type of composition can be generalized further
_o_ : forall {l}{X Y Z : Set l} -> (Y -> Z) -> (X -> Y) -> X -> Z
(f o g) x = f (g x)

_$_ : forall{l}{X Y : Set l} -> (X -> Y) -> X -> Y
f $ x = f x


----------------------------------------------------------------------------
-- lists
----------------------------------------------------------------------------

data List (X : Set) : Set where  -- X scopes over the whole declaration...
  []    : List X                 -- ...so you can use it here...
  _::_  : X -> List X -> List X  -- ...and here.
infixr 3 _::_
{-# COMPILED_DATA List [] [] (:) #-}
{-# BUILTIN LIST List #-}
{-# BUILTIN NIL [] #-}
{-# BUILTIN CONS _::_ #-}

----------------------------------------------------------------------------
-- chars and strings
----------------------------------------------------------------------------

postulate       -- this means that we just suppose the following things exist...
  Char : Set
  String : Set
{-# BUILTIN CHAR Char #-}
{-# COMPILED_TYPE Char Char #-}      -- ...and by the time we reach Haskell...
{-# BUILTIN STRING String #-}
{-# COMPILED_TYPE String String #-}  -- ...they *do* exist!

primitive       -- these are baked in; they even work!
  primCharEquality    : Char -> Char -> Two
  primStringAppend    : String -> String -> String
  primStringToList    : String -> List Char
  primStringFromList  : List Char -> String


---------------------------------------------------------------------------
-- COLOURS
---------------------------------------------------------------------------

-- We're going to be making displays from coloured text.

data Colour : Set where
  black red green yellow blue magenta cyan white : Colour
{-# COMPILED_DATA Colour HaskellSetup.Colour
      HaskellSetup.Black HaskellSetup.Red HaskellSetup.Green
      HaskellSetup.Yellow HaskellSetup.Blue HaskellSetup.Magenta
      HaskellSetup.Cyan HaskellSetup.White #-}

