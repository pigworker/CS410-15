module LecIC where

open import CS410-Prelude
open import CS410-Nat


_-:>_ : {I : Set}(S T : I -> Set) -> I -> Set
(S -:> T) i = S i -> T i
infixr 3 _-:>_

-- notation for indexed sets

[_] : {I : Set}(X : I -> Set) -> Set
[ X ] = forall {i} -> X i

record MonadIx {W : Set}(F : (W -> Set) -> (W -> Set)) : Set1 where
  field
    retIx : forall {P} -> [ P -:> F P ]
    extendIx : forall {P Q} -> [ P -:> F Q ] -> [ F P -:> F Q ]
  _?>=_ : forall {P Q w} ->
          F P w -> (forall {v} -> P v -> F Q v) -> F Q w
  fp ?>= k = extendIx k fp
    
IC : (W : Set)
     (C : W -> Set)
     (R : (w : W) -> C w -> Set)
     (n : (w : W)(c : C w)(r : R w c) -> W)
     -> (W -> Set) -> (W -> Set)
IC W C R n G w = Sg (C w) \ c -> (r : R w c) -> G (n w c r)

data FreeIx (W : Set)
            (C : W -> Set)
            (R : (w : W) -> C w -> Set)
            (n : (w : W)(c : C w)(r : R w c) -> W)
            (G : W -> Set)
            (w : W)
            : Set
            where
  ret : G w -> FreeIx W C R n G w
  do  : IC W C R n (FreeIx W C R n G) w -> FreeIx W C R n G w

postulate
  FileName : Set
  Char : Set
  foo : FileName
  blah : Char

data WriteFileW : Set where
  opened closed : WriteFileW

data WriteFileC : WriteFileW -> Set where
  write : Char -> WriteFileC opened
  openW : FileName -> WriteFileC closed
  closeW : WriteFileC opened

WriteFileR : (w : WriteFileW)(c : WriteFileC w) -> Set
WriteFileR .opened (write x) = One
WriteFileR .closed (openW x) = WriteFileW
WriteFileR .opened closeW = One

WriteFileN : (w : WriteFileW)(c : WriteFileC w)(r : WriteFileR w c) -> WriteFileW
WriteFileN .opened (write x) <> = opened
WriteFileN .closed (openW x) r = r
WriteFileN .opened closeW <> = closed

WRITE : (WriteFileW -> Set) -> (WriteFileW -> Set)
WRITE = FreeIx WriteFileW WriteFileC WriteFileR WriteFileN

Goal : WriteFileW -> Set
Goal opened = Zero
Goal closed = One

play : WRITE Goal closed
play = do (openW foo , \
  { opened  -> do (write blah , (\ _ -> do (closeW , (\ _ -> ret <>))))
  ; closed  -> ret <>
  })

FreeMonadIx : (W : Set)
     (C : W -> Set)
     (R : (w : W) -> C w -> Set)
     (n : (w : W)(c : C w)(r : R w c) -> W)
     -> MonadIx (FreeIx W C R n)
FreeMonadIx W C R n =
  record { retIx = ret
         ; extendIx = help
         } where
  help : {P Q : W → Set} ->
         [ P -:> FreeIx W C R n Q ] ->
         [ FreeIx W C R n P -:> FreeIx W C R n Q ]
  help k (ret p) = k p
  help k (do (c , j)) = do (c , \ r -> help k (j r))


data HType : Set where hTwo hNat : HType

-- mapping names for types to real types.

THVal : HType -> Set
THVal hTwo = Two
THVal hNat = Nat

-- A syntax for types expressions, indexed by typed variables. Compare
-- with the untyped HExp and fill in the missing expression formers,
-- we have shown you the way with _+H_. think: what can be guaranteed?

data THExp (X : HType -> Set) : HType -> Set where
  var : forall {T} -> X T -> THExp X T
  val : forall {T} -> THVal T -> THExp X T
  _+H_ : THExp X hNat -> THExp X hNat -> THExp X hNat
  -- ??? fill in the other two constructs, typed appropriately
  -- (remember that "if then else" can compute values at any type)

THExpMonadIx : MonadIx THExp
THExpMonadIx = record
  {  retIx    = var
  ;  extendIx = help
  }  where
  help : forall {P Q} -> [ P -:> THExp Q ] -> [ THExp P -:> THExp Q ]
  help f (var x) = f x
  help f (val v) = val v
  help f (e1 +H e2) = help f e1 +H help f e2

WH : Set
WH = Nat * Nat

data Tiling (X : WH -> Set)(wh : WH) : Set where
  ! : X wh -> Tiling X wh
  joinH : (wl wr : Nat)(wq : wl +N wr == fst wh) ->
          Tiling X (wl , snd wh) ->  Tiling X (wr , snd wh) -> Tiling X wh
  joinV : (ht hb : Nat)(hq : ht +N hb == snd wh) ->
          Tiling X (fst wh , ht) ->  Tiling X (fst wh , hb) -> Tiling X wh

TilingMonadIx : MonadIx Tiling
TilingMonadIx = record
  { retIx = !
  ; extendIx = help
  } where
  help : {P Q : WH -> Set} -> [ P -:> Tiling Q ] -> [ Tiling P -:> Tiling Q ]
  help f (! p) = f p
  help f (joinH wl wr wq t-l t-r) = joinH wl wr wq (help f t-l) (help f t-r)
  help f (joinV ht hb hq t-t t-b) = joinV ht hb hq (help f t-t) (help f t-b)

IsZero : Nat -> Set
IsZero zero = One
IsZero (suc n) = Zero

CanCons : Set -> Nat -> Set
CanCons X zero = Zero
CanCons X (suc n) = X

afterCons : {X : Set}(n : Nat) -> CanCons X n -> One -> Nat
afterCons zero () <>
afterCons (suc n) c <> = n


VEC : Set -> Nat -> Set
VEC X = FreeIx Nat (CanCons X) (\ _ _ -> One) afterCons IsZero
