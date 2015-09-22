module Hello where

-- Oh, you made it! Well done! This line is a comment.

-- In the beginning, Agda knows nothing, but we can teach it about numbers.

data Nat : Set where
  zero  :  Nat
  suc   :  Nat -> Nat

-- data Nat = Zero | Suc Nat -- in Haskell

-- Now we can say how to add numbers.

_+N_ : Nat -> Nat -> Nat
m +N zero = m
m +N suc n = suc (m +N n)

-- Now we can try adding some numbers.

four : Nat
four = (suc (suc zero)) +N (suc (suc zero))

-- To make it go, select "Evaluate term to normal form" from the
-- Agda menu, then type "four", without the quotes, and press return.

-- Hopefully, you should get a response
--   suc (suc (suc (suc zero)))

-- Done?

-- Now you can start Ex1.agda

-- WARNING Ex1.agda requires you to give a definition of addition.
-- There are lots of ways to define addition, and by the end of the
-- exercise, it will matter which you choose. If you start just by
-- copying the above definition, you will reach a point where you
-- may wish to reconsider it, and hopefully learn something useful
-- about the way Agda works.
