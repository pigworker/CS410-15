{-# OPTIONS --copatterns #-}

module LecStr where

open import CS410-Prelude
open import CS410-Nat
open import CS410-Functor

record Stream (X : Set) : Set where
  coinductive
  field
    head : X
    tail : Stream X
open Stream

count : Nat -> Stream Nat
head (count n) = n
tail (count n) = count (suc n)

nats : Stream Nat
nats = count zero

poke : Nat
poke = head (tail (tail (tail nats)))

repeat : {X : Set} -> X -> Stream X
head (repeat x) = x
tail (repeat x) = repeat x

strApp : {S T : Set} -> Stream (S -> T) -> Stream S -> Stream T
head (strApp fs ss) = (head fs) (head ss)
tail (strApp fs ss) = strApp (tail fs) (tail ss)

strMap : {S T : Set} -> (S -> T) -> Stream S -> Stream T
strMap f ss = strApp (repeat f) ss

diagonal : {X : Set} -> Stream (Stream X) -> Stream X
head (diagonal xss) = head (head xss)
tail (diagonal xss) = diagonal (strMap tail (tail xss))

{- productivity checker rejects
fibo : Stream Nat
head fibo = 1
head (tail fibo) = 1
tail (tail fibo) = strApp (strApp (repeat _+N_) (tail fibo)) fibo
-}

data CoList' (X : Set) : Set
record CoList (X : Set) : Set where
  coinductive
  constructor thunk
  field
    force : CoList' X
data CoList' X where
  [] : CoList' X
  _::_ : X -> CoList X -> CoList' X

module CoListExamples where
  open CoList

  short : CoList Nat
  short = thunk (0 :: thunk (1 :: thunk (2 :: thunk [])))

  long : forall {X} -> Stream X -> CoList X
  force (long s) = head s :: long (tail s)

  _++_ : forall {X} -> CoList X -> CoList X -> CoList X
  force (xs ++ ys) with force xs
  force (xs ++ ys) | [] = force ys
  force (xs ++ ys) | x :: xs' = x :: (xs' ++ ys)

{-
  concat : forall {X} -> CoList (CoList X) -> CoList X
  force (concat xss) with force xss
  force (concat xss) | [] = []
  force (concat xss) | xs :: xss' with force xs
  force (concat xss) | xs :: xss' | [] = ? -- oops force (concat xss')
  force (concat xss) | xs :: xss' | x :: xs' = x :: concat (thunk (xs' :: xss'))
-}

-- nonempty CoLists
-- tails for Streams
-- " n.e. CoLists
