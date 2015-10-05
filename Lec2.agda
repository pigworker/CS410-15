module Lec2 where

data Zero : Set where

{-
cannaeMake : Zero
cannaeMake = cannaeMake
-}

magic : {X : Set} -> Zero -> X
magic ()

record One : Set where
  constructor <>

tryit : One
tryit = <>

tryit2 : One
tryit2 = record {}

data List (X : Set) : Set where
  [] : List X
  _::_ : X -> List X -> List X

NonEmpty : {X : Set} -> List X -> Set
NonEmpty [] = Zero
NonEmpty (x :: xs) = One

head : {X : Set} -> (xs : List X) -> NonEmpty xs -> X
head [] ()
head (x :: xs) _ = x

{-
examples : List Zero
examples = {!-l!}

examples2 : List One
examples2 = {!-l!}
-}

data Two : Set where
  tt : Two
  ff : Two

if_then_else_ : {X : Set} -> Two -> X -> X -> X
if b then t else e = e
-- if ff then t else e = t

caseTwo : {P : Two -> Set} -> P tt -> P ff -> (b : Two) -> P b
caseTwo pt pf tt = pt
caseTwo pt pf ff = pf

not : Two -> Two
not tt = ff
not ff = tt

xor : Two -> Two -> Two
xor x y with not y
xor tt y | tt = tt
xor ff y | tt = ff
xor tt y | ff = ff
xor ff y | ff = tt
