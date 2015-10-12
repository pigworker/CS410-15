module Ex1-blah where

----------------------------------------------------------------------------
-- EXERCISE 1 -- NUMBERS, LISTS, VECTORS (a driving lesson)
--
-- VALUE:     15%
-- DEADLINE:  5pm, Friday 2 October (week 2)
--
-- DON'T SUBMIT, COMMIT! Create your own private version of the CS410 repo,
-- hosted somewhere like BitBucket, and invite users "pigworker" and
-- "jmchapman" to collaborate with you on the project. The last version of
-- your repo committed before the deadline is the "official" version, for
-- marking purposes, but we're unlikely to penalise submission over the
-- weekend. You can trust us not to look until Monday!
--
-- The purpose of this exercise is to get you used to using Agda and its
-- emacs interface.
----------------------------------------------------------------------------

open import CS410-Prelude

-- HINT: your tasks are heralded with the eminently searchable tag, "???"

-- TIP: when you load this file, you should see 11 open goals, which is
-- too many to think about at once; use comments {- .. -} to switch off the
-- parts of the file you haven't reached yet.


----------------------------------------------------------------------------
-- "Nat" -- the type of unary natural numbers
----------------------------------------------------------------------------

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat
{-# BUILTIN NATURAL Nat #-} -- means we can write 2 for suc (suc zero)

-- TERMINOLOGY Set and "type". By "type", I mean anything you can put to
-- the right of : to classify the thing to the left of :, so "Set" is a
-- type, as in Nat : Set, and Nat is a type, as in zero : Nat. Being a
-- Set is *one* way of being a type, but it is not the only way. In
-- particular, try uncommenting this (and then change your mind).

{-+}
mySet : Set
mySet = Set
{+-}

-- SPOT THE DIFFERENCE: in Haskell, we'd write
--
-- data Nat = Zero | Suc Nat
--
-- saying what the type is called and what is in it, and then we'd find
-- that Zero :: Nat and Suc :: Nat -> Nat. Also, constructors live in a
-- separate namespace, with capital initial letters.
--
-- In Agda, we say what type each thing belongs to. Everything lives in
-- the same namespace. Capitalisation is only a social convention. I tend
-- to use capitals for typey things and lower case for valuey things.
-- And we use just the one colon for typing, not two, because types are
-- more important than lists.

----------------------------------------------------------------------------
-- ??? 1.1 addition (score: ? / 1)
--
-- There are lots of ways to add two numbers together. Do you inspect the
-- first? Do you inspect the second? Make sure you get the correct numerical
-- answer, whatever you do. You may need to revisit this problem later, when
-- the way addition works has a significant impact on types.
----------------------------------------------------------------------------

_+N_ : Nat -> Nat -> Nat
zero +N n = n
suc m +N n = suc (m +N n)
infixr 3 _+N_

{-
-- NOTATION: a name _+N_ with underscores in it serves double duty.
-- (1) it is a perfectly sensible PREFIX operator, so _+N_ 2 2 makes sense
-- (2) it describes the INFIX usage of the operator, with the underscores
--       showing where the arguments go, with EXTRA SPACING, so the infix
--       version of _+N_ 2 2 is 2 +N 2.

-- When you think you're done, uncomment these unit tests, e.g., by turning
-- {-+} to {-(-} and {+-} to {-)-}. They should typecheck ok.
{-+}
testPlus1 : 2 +N 2 == 4
testPlus1 = refl

testPlus2 : 0 +N 5 == 5
testPlus2 = refl

testPlus3 : 5 +N 0 == 5
testPlus3 = refl
{+-}


----------------------------------------------------------------------------
-- ??? 1.2 multiplication (score: ? / 1)
--
-- There's also a lot of choice in how to multiply, but they all rely on
-- repeated addition. Find a way to do it.
----------------------------------------------------------------------------

_*N_ : Nat -> Nat -> Nat
m *N n  =  {!!}
infixr 4 _*N_

-- unit tests
{-+}
testMult1 : 2 *N 2 == 4
testMult1 = refl

testMult2 : 0 *N 5 == 0
testMult2 = refl

testMult3 : 5 *N 0 == 0
testMult3 = refl

testMult4 : 1 *N 5 == 5
testMult4 = refl

testMult5 : 5 *N 1 == 5
testMult5 = refl

testMult6 : 2 *N 3 == 6
testMult6 = refl
{+-}


----------------------------------------------------------------------------
-- ??? 1.3 subtraction I (score: ? / 1)
--
-- Subtraction is a nuisance. How do you take a big number away from a
-- smaller one? Give the closest answer you can to the correct answer.
----------------------------------------------------------------------------

_-N1_ : Nat -> Nat -> Nat
m -N1 n  =  {!!}

-- unit tests
{-+}
testSubN1-1 : 4 -N1 2 == 2
testSubN1-1 = refl

testSubN1-2 : 42 -N1 37 == 5
testSubN1-2 = refl
{+-}

----------------------------------------------------------------------------
-- "Maybe" allows for the possibility of errors
----------------------------------------------------------------------------
-}
data Maybe (X : Set) : Set where
  yes  : X -> Maybe X
  no   : Maybe X
{-
-- SPOT THE DIFFERENCE: in Haskell, these are "Just" and "Nothing"

-- LATER, we'll revisit Maybe and define it in terms of more basic ideas.


----------------------------------------------------------------------------
-- ??? 1.4 subtraction II (score: ? / 1)
--
-- Implement subtraction with a type acknowledging that failure can happen.
----------------------------------------------------------------------------

_-N2_ : Nat -> Nat -> Maybe Nat
m -N2 n  =  {!!}

-- unit tests
{-+}
testSubN2-1 : 4 -N2 2 == yes 2
testSubN2-1 = refl

testSubN2-2 : 42 -N2 37 == yes 5
testSubN2-2 = refl

testSubN2-3 : 37 -N2 42 == no
testSubN2-3 = refl
{+-}

-}
----------------------------------------------------------------------------
-- _N>=_ as a relation, not a test
----------------------------------------------------------------------------

_N>=_ : Nat -> Nat -> Set      -- not Two (a.k.a. Bool), but Set
                               -- the set of "ways it can be true"
                               -- i.e., what counts as EVIDENCE
m      N>=  zero   =  One      -- anything is at least zero in a boring way
zero   N>=  suc n  =  Zero     -- no way is zero bigger than a successor
suc m  N>=  suc n  =  m N>= n  -- the way to compare successors

-- What's funny is that it's just an ordinary program, computing by
-- pattern matching and recursion.


----------------------------------------------------------------------------
-- ??? 1.5 subtraction III (score: ? / 1)
--
-- Implement subtraction with explicit evidence that the inputs are
-- amenable to subtraction.
----------------------------------------------------------------------------

_-N3_-:_ : (m : Nat) -> (n : Nat) -> m N>= n -> Nat
m     -N3 zero  -: <>  = m
zero  -N3 suc n -: ()
suc m -N3 suc n -: p   = m -N3 n -: p

-- DON'T PANIC about the syntax (m : Nat) -> (n : Nat) ->
-- The type of both those arguments is Nat. However, when we write the
-- type this way, we can name those arguments for use further along in
-- the type, i.e. in the third argument. That's an example of a *dependent*
-- type. In fact, the regular syntax Nat -> is short for (_ : Nat) -> where
-- we don't bother naming the thing.

-- NOTICE that we can have fancy multi-place operators.

-- HINT: you will need to learn about the "absurd" pattern, written ().

-- unit tests
{-+}
testSubN3-1 : 4 -N3 2 -: <> == 2
testSubN3-1 = refl

testSubN3-2 : 42 -N3 37 -: <> == 5
testSubN3-2 = refl
{+-}

-- Uncomment this test and try to fill in the missing bits to make it work.
{-+}
testSubN3-3 : 37 -N3 42 -: {!!} == {!!}
testSubN3-3 = refl
{+-}
-- HAHA! YA CANNAE! So comment it out again.

-- EXTRA! You can
-- write     (m : Nat) -> (n : Nat) ->
-- as        (m : Nat)(n : Nat) ->        -- omitting all but the last ->
-- or as     (m n : Nat) ->               -- two named args sharing a type.

-- NOTICE how the defining equations for _N>=_ play a crucial role in the
-- typechecking of the above.

-- NOTICE that attempts II and III take contrasting approaches to the
-- problem with I. II broadens the output to allow failure. III narrows the
-- input to ensure success.

-- LATER, we'll see how to make the proof-plumbing less explicit

-- SUSPICIOUS: why aren't they asking us to define division?


----------------------------------------------------------------------------
-- List -- the thing that was [ .. ] in Haskell
----------------------------------------------------------------------------

data List (X : Set) : Set where  -- X scopes over the whole declaration...
  []    : List X                 -- ...so you can use it here...
  _::_  : X -> List X -> List X  -- ...and here.
infixr 3 _::_


----------------------------------------------------------------------------
-- ??? 1.6 concatenation (score: ? / 1)
----------------------------------------------------------------------------

_+L_ : {X : Set} -> List X -> List X -> List X
[] +L ys = ys
(x :: xs) +L ys = x :: xs +L ys
infixr 3 _+L_

-- DON'T PANIC about the "curly braces" syntax. It's very similar to the
-- (m : Nat) -> syntax we saw, above. It describes an argument by giving
-- its type, Set, and a name X to allow dependency. All the braces do is
-- set the default usage convention that X is by default INVISIBLE. Any
-- time you use the function _+L_, Agda will try to figure out what is
-- the appropriate thing to put for the invisible argument, which is the
-- element type for the lists. She will usually succeed, because the types
-- of the lists you feed in will be a dead giveaway.

-- SPOT THE DIFFERENCE: back when you learned Haskell, you learned about
-- TWO ideas, FUNCTIONS and POLYMORPHISM. Now you can see that there was
-- only ONE IDEA, after all. This sort of collapse will keep happening.
-- The world is simpler, made of a smaller number of better articulated
-- parts.

-- unit test
{-+}
testConcL  :   (0 :: 1 :: 2 :: []) +L (3 :: 4 :: [])
           ==   0 :: 1 :: 2 ::         3 :: 4 :: []
testConcL = refl
{+-}


----------------------------------------------------------------------------
-- ??? 1.7 take I (score: ? / 1)
--
-- Given a number, n, and a list, xs, compute the first n elements of xs.
-- Of course, there will be a tiny little problem if the caller asks for
-- more elements than are available, hence the name of the function.
-- You must ensure that the list returned is indeed a prefix of the list
-- supplied, and that it has the requested length if possible, and at most
-- that length if not.
----------------------------------------------------------------------------
{-
mis-take : {X : Set} -> Nat -> List X -> List X
mis-take n xs  =  {!!}
-}
-- unit test
{-+}
testMisTake  :   mis-take 3 (0 :: 1 :: 2 :: 3 :: 4 :: [])
             ==              0 :: 1 :: 2 :: []
testMisTake = refl
{+-}



----------------------------------------------------------------------------
-- ??? 1.8 take II (score: ? / 2)
--
-- Fix mis-take by acknowledging the possibility of error. Ensure that your
-- function returns "yes" with a list of exactly the right length if
-- possible, or says "no". You may need to use the "with" construct to
-- inspect the result of the recursive call.
----------------------------------------------------------------------------

may-take : {X : Set} -> Nat -> List X -> Maybe (List X)
may-take zero xs = yes []
may-take (suc n) [] = no
may-take (suc n) (x :: xs) with may-take n xs
may-take (suc n) (x :: xs) | yes ys = yes (x :: ys)
may-take (suc n) (x :: xs) | no = no

{-
-- unit test
{-+}
testMayTake1  :   may-take 3 (0 :: 1 :: 2 :: 3 :: 4 :: [])
              ==         yes (0 :: 1 :: 2 :: [])
testMayTake1 = refl

testMayTake2  :   may-take 6 (0 :: 1 :: 2 :: 3 :: 4 :: [])
              ==  no
testMayTake2 = refl

testMayTake3  :   may-take 5 (0 :: 1 :: 2 :: 3 :: 4 :: [])
              ==         yes (0 :: 1 :: 2 :: 3 :: 4 :: [])
testMayTake3 = refl
{+-}


----------------------------------------------------------------------------
-- ??? 1.9 length (score: ? / 1)
----------------------------------------------------------------------------

-- Show how to compute the length of a list.

length : {X : Set} -> List X -> Nat
length xs = {!!}

-- unit test
{-+}
testLength  :  length (0 :: 1 :: 2 :: 3 :: 4 :: [])  ==  5
testLength  =  refl
{+-}

-}
----------------------------------------------------------------------------
-- "Vectors" -- Lists indexed by length
----------------------------------------------------------------------------

-- We seem to be troubled by things fouling up when lists have the wrong
-- length. Here's a way to make list-like structures whose types let us
-- keep tabs on length: the "vectors".

data Vec (X : Set) : (n : Nat) -> Set where -- n's not in scope after "where"
  []    : Vec X zero                                  -- it's zero here,...
  _::_  : {n : Nat} -> X -> Vec X n -> Vec X (suc n)  -- ...successor, there

-- DON'T PANIC
-- Vec X is not a Set, but rather an INDEXED FAMILY of sets. For each n in
-- Nat, Vec X n is a Set. The index, n, is the length. The constructors are
-- just like those of List, except that their types also tell the truth
-- about length, via the index.

-- NOTICE that when we write a "cons", x :: xs, the length of the tail, xs,
-- is an invisible argument.

-- DON'T PANIC about the reuse of constructor names. We're usually starting
-- with types and working towards code, so it is almost always clear which
-- type's constructors we mean.

-- SUSPICION: we declared List, then wrote length, then invented Vec.
-- Perhaps there is some way to say "Vec is List indexed by length" and
-- have it invented for us.


----------------------------------------------------------------------------
-- ??? 1.10 concatenation (score: ? / 1)
----------------------------------------------------------------------------

-- When we concatenate vectors, we add their lengths.

_+V_ : {X : Set}{m n : Nat} -> Vec X m -> Vec X n -> Vec X (m +N n)
[] +V ys = ys
(x :: xs) +V ys = x :: xs +V ys
infixr 3 _+V_

-- NOTICE that even though m and n are numbers, not types, they can
-- still be invisible.

-- DON'T PANIC if this doesn't work out to be just as easy (or even easier)
-- than for lists. You may need to tinker with your definition of _+N_ to
-- make _+V_ typecheck smoothly. That's because the defining equations for
-- _+N_ are all the typechecker has to go on when seeing that your code
-- here fits together properly.

-- unit test
{-+}
testConcV  :   (0 :: 1 :: 2 :: []) +V (3 :: 4 :: [])
           ==   0 :: 1 :: 2 ::         3 :: 4 :: []
testConcV = refl
{+-}


----------------------------------------------------------------------------
-- ??? 1.11 take (score: ? / 2)
----------------------------------------------------------------------------

-- Now we know the lengths, we can give a PRECONDITION for taking.

take : {X : Set}{m : Nat}(n : Nat) -> m N>= n -> Vec X m -> Vec X n
take zero p xs = []
take (suc n) () []
take (suc n) p (x :: xs) = x :: take n p xs

{-
-- unit test
{-+}
testTake1  :  take 3 <> (0 :: 1 :: 2 :: 3 :: 4 :: [])
              ==         0 :: 1 :: 2 :: []
testTake1 = refl

testTake3  :  take 5 <> (0 :: 1 :: 2 :: 3 :: 4 :: [])
              ==         0 :: 1 :: 2 :: 3 :: 4 :: []
testTake3 = refl
{+-}

-- check you can't finish this
{-+}
testTake2  :  take 6 {!!} (0 :: 1 :: 2 :: 3 :: 4 :: [])
              ==  {!!}
testTake2 = refl
{+-}


----------------------------------------------------------------------------
-- Chopping: one last wild weird new thing
----------------------------------------------------------------------------

-- Here's a thing you'd struggle to do in Haskell. It's really about seeing.
-- A vector of length m +N n is "Choppable" if you can show how it is given
-- by concatenating a vector of length m and a vector of length n.

data Choppable {X : Set}(m n : Nat) : Vec X (m +N n) -> Set where
  chopTo : (xs : Vec X m)(ys : Vec X n) -> Choppable m n (xs +V ys)

----------------------------------------------------------------------------
-- ??? 1.12 chop (score: ? / 2)
----------------------------------------------------------------------------

chop : {X : Set}(m n : Nat)(xs : Vec X (m +N n)) -> Choppable m n xs
chop m n xs = {!!}

-- DON'T PANIC if you can't pattern match on the vector right away, because
-- the fact is that without looking at WHERE TO CHOP, you don't know if you
-- need to.

-- HINT You can access vectors only from the "left end", which is a big
-- clue about which number you should inspect.

-- HINT Much like in -N2 and may-take, you will probably benefit from using
-- the "with" feature to allow you to match on the outcome of a recursive
-- call.

-- DON'T PANIC if dotty things appear spontaneously in your patterns. That's
-- knowledge for free: the pattern checker is saying "you don't need to ask,
-- because I know that the only thing which goes here is such-and-such".

-- unit test

{-+}
testChop  :   chop 3 2 (0 :: 1 :: 2 :: 3 :: 4 :: [])
          ==  chopTo (0 :: 1 :: 2 :: []) (3 :: 4 :: [])
testChop = refl
{+-}

-- SUSPICION: unit tests may, in this case, be a little beside the point

-- TERMINOLOGY: we call this method "constructing a view" of vectors. The
-- datatype Choppable explains how we would like to be able to look at
-- vectors. The chop function *proves* that we always can. We get for free
-- that we can look at vectors as being made by [] and _::_, but now we
-- can PROGRAM new ways of looking: vectors as made by _+V_.

-- Welcome to the new programming.
-}
