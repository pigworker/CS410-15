module CS410-Vec where

open import CS410-Prelude
open import CS410-Nat

data Vec (X : Set) : Nat -> Set where
  []   : Vec X 0
  _::_ : forall {n} ->
         X -> Vec X n -> Vec X (suc n)
infixr 3 _::_

_+V_ : forall {X m n} -> Vec X m -> Vec X n -> Vec X (m +N n)
[] +V ys = ys
(x :: xs) +V ys = x :: xs +V ys
infixr 3 _+V_

data Choppable {X : Set}(m n : Nat) : Vec X (m +N n) -> Set where
  chopTo : (xs : Vec X m)(ys : Vec X n) -> Choppable m n (xs +V ys)

chop : {X : Set}(m n : Nat)(xs : Vec X (m +N n)) -> Choppable m n xs
chop zero n xs = chopTo [] xs
chop (suc m) n (x :: xs) with chop m n xs
chop (suc m) n (x :: .(xs +V ys)) | chopTo xs ys = chopTo (x :: xs) ys

chopParts : {X : Set}(m n : Nat)(xs : Vec X (m +N n)) -> Vec X m * Vec X n
chopParts m n xs with chop m n xs
chopParts m n .(xs +V ys) | chopTo xs ys = xs , ys

vec : forall {n X} -> X -> Vec X n
vec {zero}   x = []
vec {suc n}  x = x :: vec x

vapp : forall {n X Y} -> Vec (X -> Y) n -> Vec X n -> Vec Y n
vapp [] [] = []
vapp (f :: fs) (x :: xs) = f x :: vapp fs xs
