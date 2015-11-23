module LecDiff where

open import CS410-Prelude
open import CS410-Nat
open import LecSigma

data Data : Set1 where
  _+D_ _*D_  : Data -> Data -> Data
  label      : Set -> Data
  rec        : Data

infixr 4 _+D_
infixr 5 _*D_

[[_]] : Data -> Set -> Set
[[ S +D T ]]   R  = [[ S ]] R + [[ T ]] R
[[ S *D T ]]   R  = [[ S ]] R * [[ T ]] R
[[ label X ]]  R  = X
[[ rec ]]      R  = R

data Mu (D : Data) : Set where
  <_> : [[ D ]] (Mu D) -> Mu D

-- example: Natural Numbers

NAT : Data
NAT = label One +D rec

pattern ZERO  = < inl <> >
pattern SUC n = < inr n >

#_ : Nat -> Mu NAT
# zero = ZERO
# (suc n) = SUC (# n)

_+DN_ : Mu NAT -> Mu NAT -> Mu NAT
ZERO  +DN n  = n
SUC m +DN n  = SUC (m +DN n)

_<=DN_ : Mu NAT -> Mu NAT -> Two
ZERO   <=DN  n      =  tt
SUC m  <=DN  ZERO   =  ff
SUC m  <=DN  SUC n  =  m <=DN n

-- example: binary trees with nodes labelled by numbers

BST : Data
BST = label One  +D  rec *D label (Mu NAT) *D rec

pattern LEAF = < inl <> >
pattern NODE l n r = < inr (l , n , r) >

insert : Mu NAT -> Mu BST -> Mu BST
insert x LEAF          = NODE LEAF x LEAF
insert x (NODE l y r)  with x <=DN y
insert x (NODE l y r)  | tt = NODE (insert x l) y r
insert x (NODE l y r)  | ff = NODE l y (insert x r)

myBST : Mu BST
myBST = NODE (NODE (NODE LEAF (# 1) LEAF) (# 2) LEAF)
             (# 4)
             (NODE (NODE LEAF (# 5) LEAF) (# 7) LEAF)

myBST' : Mu BST
myBST' = insert (# 3) myBST

------------------------

Diff : Data -> Data
Diff (S +D T)   = Diff S +D Diff T
Diff (S *D T)   = Diff S *D T  +D  S *D Diff T
Diff (label X)  = label Zero
Diff rec        = label One

plug : {R : Set}(D : Data) -> [[ Diff D ]] R -> R -> [[ D ]] R
plug (S +D T) (inl s') r = inl (plug S s' r)
plug (S +D T) (inr t') r = inr (plug T t' r)
plug (S *D T) (inl (s' , t)) r = plug S s' r , t
plug (S *D T) (inr (s , t')) r = s , plug T t' r
plug (label X) () r
plug rec       <> r = r

Shape : Data -> Set
Shape D = [[ D ]] One

Positions : (D : Data) -> Shape D -> Set
Positions (D +D E) (inl d) = Positions D d
Positions (D +D E) (inr e) = Positions E e
Positions (D *D E) (d , e) = Positions D d + Positions E e
Positions (label X) x = Zero
Positions rec <> = One

