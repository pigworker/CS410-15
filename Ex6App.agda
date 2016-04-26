module Ex6App where

open import CS410-Prelude
open import CS410-Nat
open import CS410-Vec
open import CS410-Indexed
open import CS410-Monoid
open import Ex6AgdaSetup
open import Ex5Sol
-- open import Ex5

open MonadIx TilingMonadIx
open FunctorIx (monadFunctorIx TilingMonadIx)


---------------------------------------------------------------------------
-- CURSES DISPLAY FOR APPLICATIONS (5 marks)                             --
---------------------------------------------------------------------------

-- You may need to look at the Ex6AgdaSetup file to find some of the relevant
-- kit for this episode, and it's worth looking there for goodies, anyway.
-- We start from the idea of a main loop.

{- This is the bit of code I wrote in Haskell to animate your code. -}
postulate
  mainAppLoop : {S : Set} ->             -- program state
    -- INITIALIZER
    S ->                              -- initial state
    -- EVENT HANDLER
    (Event -> S ->                    -- event and state in
     S ** List Action) ->             -- new state and screen actions out
    -- PUT 'EM TOGETHER AND YOU'VE GOT AN APPLICATION!
    IO One
{-# COMPILED mainAppLoop (\ _ -> HaskellSetup.mainAppLoop) #-}

-- The type S ** T is a type of pairs that the compiler can share with
-- Haskell. Its constructor is _,_ just as for S * T.

-- To make a thing you can run, you need to
--   (i)    choose a type to represent the program's internal state S
--   (ii)   give the initial state
--   (iii)  explain how, given an event and the current state, to
--            produce a new state and a list of actions to update the
--            display.

-- Let me show you an example...

-- To run this program, start a terminal, then
--
--    make app
--
-- You should be able to press keys and resize the thing and see sensible
-- stuff happen. Ctrl-C quits.

-- When you're bored of green rectangles, comment out the above main
-- function, so you can move on to the actual work. There are other
-- main functions further down the file which you can comment in as you
-- need them. Of course, you can have at most one main at a time.

-- Now your turn. Making use of the equipment you developed in exercise 5,
-- get us from a Painting to a List Action in two hops. Note that you will
-- have to decide how to render a Hole: some bland background stuff, please.
-- (1 mark)

layerMatrix : [ Layer -:> Matrix Cell ]
layerMatrix p = paste matrixPaste (mapIx fill p) where
  fill : [ HoleOr (Matrix Cell) -:> Matrix Cell ]
  fill h = {!!}

vecFoldR : {X Y : Set} -> (X -> Y -> Y) -> Y -> {n : Nat} -> Vec X n -> Y
vecFoldR c n [] = n
vecFoldR c n (x :: xs) = c x (vecFoldR c n xs)

matrixAction : forall {wh} -> Matrix Cell wh -> List Action
matrixAction = vecFoldR (vecFoldR {!!} id) []


---------------------------------------------------------------------------
-- APPLICATIONS                                                          --
---------------------------------------------------------------------------

-- Here's a general idea of what it means to be an "application".
-- You need to choose some sort of size-dependent state, then provide these
-- bits and pieces. We need to know how the state is updated according to
-- events, with resizing potentially affecting the state's type. We must
-- be able to paint the state. The state should propose a cursor position.
-- (Keen students may modify this definition to ensure the cursor must be
-- within the bounds of the application.)

record Application (S : Nat * Nat -> Set) : Set where
  field
    handleKey     : Key -> [ S -:> S ]
    handleResize  : {w h : Nat}(w' h' : Nat) -> S (w , h) -> S (w' , h')
    paintMe       : [ S -:> Layer ]
    cursorMe      : {w h : Nat} -> S (w , h) -> Nat * Nat  -- x,y coords
open Application public

-- Now your turn. Build the appropriate handler to connect these
-- applications with mainLoop. Again, work in two stages, first
-- figuring out how to do the right actions, then managing the
-- state properly. (1 mark)

AppState : (S : Nat * Nat -> Set) -> Set
AppState S = Sg Nat \ w -> Sg Nat \ h -> S (w , h)

appPaint : {S : Nat * Nat -> Set}{w h : Nat} ->
           Application S -> S (w , h) -> List Action
appPaint app s =
  goRowCol 0 0 :: matrixAction (layerMatrix p)
  ++ (goRowCol (snd xy) (fst xy) :: [])
  where
    p  = paintMe app s
    xy = cursorMe app s

appHandler : {S : Nat * Nat -> Set} ->
           Application S ->
           Event -> AppState S -> AppState S ** List Action
appHandler app (key k) (w , h , s) = (w , h , s') , appPaint app s'
  where s' = handleKey app k s
appHandler app (resize w' h') (w , h , s) = (w' , h' , s') , appPaint app s'
  where s' = handleResize app w' h' s

-- Your code turns into a main function, as follows.

appMain : {S : Nat * Nat -> Set} -> Application S -> S (0 , 0) -> IO One
appMain app s = mainAppLoop (0 , 0 , s) (appHandler app) 


---------------------------------------------------------------------------
-- A DEMO APPLICATION                                                    --
---------------------------------------------------------------------------

sillyChar : Char -> {w h : Nat} -> Layer (w , h)
sillyChar c = ! (block (vec (vec (green - c / black))))

sillyApp : Application \ _ -> Char
sillyApp = record
  {  handleKey     = \ { (char c) _ -> c ; _ c -> c }
  ;  handleResize  = \ _ _ c -> c
  ;  paintMe       = \
       { {suc (suc w) , suc (suc h)} c ->
          joinV 1 (suc h) refl
            (sillyChar c)
            (joinV h 1 (sym (plusCommFact 1 h))
              (joinH 1 (suc w) refl (sillyChar c)
               (joinH w 1 (sym (plusCommFact 1 w)) (sillyChar ' ') (sillyChar c))
               )
              (sillyChar c) )
       ; c -> sillyChar c
       }
  ;  cursorMe      = \ _ -> 0 , 0
  }

{- -}
main : IO One
main = appMain sillyApp '*'
{- -}


---------------------------------------------------------------------------
-- COMPARING TWO NUMBERS                                                 --
---------------------------------------------------------------------------

-- You've done the tricky part in exercise 5, comparing two splittings of
-- the same number. Here's an easy way to reuse that code just to compare
-- two numbers. It may help in what is to come.

Compare : Nat -> Nat -> Set
Compare x y = CutComparable x y y x (x +N y)

compare : (x y : Nat) -> Compare x y
compare x y = cutCompare x y y x (x +N y) refl (sym (plusCommFact x y))

-- To make sure you've got the message, try writing these things
-- "with compare" to resize paintings. If you need to make a painting
-- bigger, pad its right or bottom with a hole. If you need to make it
-- smaller, trim off the right or bottom excess. You have all the gadgets
-- you need! I'm not giving marks for these, but they'll be useful in
-- the next bit.

cropPadLR : (w h w' : Nat) -> Layer (w , h) -> Layer (w' , h)
cropPadLR w h w' p = {!!}

cropPadTB : (w h h' : Nat) -> Layer (w , h) -> Layer (w , h')
cropPadTB w h h' p = {!!}

---------------------------------------------------------------------------
-- THE MOVING RECTANGLE                                                  --
---------------------------------------------------------------------------

-- This is the crux of this episode. Please build me an application which
-- displays a movable resizeable rectangle drawn with ascii art as follows
--
--           +--------------+
--           |              |
--           |              |
--           +--------------+
--
-- The "size" of the application is the terminal size: the rectangle should
-- be freely resizable *within* the terminal, so you should pad out the
-- rectangle to the size of the screen using Hole.
-- That is, only the rectangle is opaque; the rest is transparent.
-- The background colour of the rectangle should be given as an argument.
-- The foreground colour of the rectangle should be white.
-- The rectangle should have an interior consisting of opaque space with
-- the given background colour.
--
-- The arrow keys should move the rectangle around inside the terminal
-- window, preserving its size (like when you drag a window around).
-- Shifted arrow keys should resize the rectangle by moving its bottom
-- right corner (again, like you might do with a mouse).
-- You do not need to ensure that the rectangle fits inside the terminal.
-- The cursor should sit at the bottom right corner of the rectangle.
--
-- Mac users: the Terminal application which ships with OS X does NOT
-- give the correct treatment to shift-up and shift-down. You can get a
-- suitable alternative from http://iterm2.com/ (Thank @sigfpe for the tip!)
--
-- (2 marks, one for key handling, one for painting)

record RectState : Set where
  constructor rect
  field
    gapL rectW : Nat
    gapT rectH : Nat

rectKey : Key -> RectState -> RectState
rectKey k s = {!!}

rectApp : Colour -> Application \ _ -> RectState
rectApp c = record
  {  handleKey     = \ k -> rectKey k
  ;  handleResize  = \ _ _ -> id
  ;  paintMe = {!!}
  ;  cursorMe = {!!}
  } where
  -- helper functions can go here

{- -
main : IO One
main = appMain (rectApp blue) (rect 10 40 3 15)
- -}


---------------------------------------------------------------------------
-- TWO BECOME ONE                                                        --
---------------------------------------------------------------------------

-- Write a function which turns two sub-applications into one main
-- application by layering them.
--
-- For some S and T, you get an Application S and an Application T
-- You should choose a suitable state representation so that you know
--   (i)   which of the two applications is at the front, and which behind
--   (ii)  the states of both.
--
-- The Tab key should swap which sub-application is at the front, as if you had
-- clicked on the one at the back. All other keys should be handled by
-- whichever action is in front at the time. Also, the cursor position
-- should be chosen by the sub-application at the front.
--
-- The overall application size will be used as the size for both
-- sub-application sizes, which means you should be able to compute the
-- Layer, using equipment from exercise 5. Crucially, we should be
-- able to see through the holes in the front sub-application to stuff from
-- the back sub-application.
--
-- (1 mark)

frontBack : {S T : Nat * Nat -> Set} ->
  Application S ->
  Application T ->
  Application \ wh -> {!!}
frontBack appS appT = record
  { handleKey = {!!}
  ; handleResize = {!!}
  ; paintMe = {!!}
  ; cursorMe = {!!}
  }

-- By way of example, let's have a blue rectangle and a red rectangle.

{- -
main : IO One
main = appMain (frontBack (rectApp blue) (rectApp red))
  (inl (rect 10 40 3 15 , rect 20 40 8 15))
- -}

---------------------------------------------------------------------------
-- IF YOU WANT MORE...                                                   --
---------------------------------------------------------------------------

-- Figure out how to reduce flicker.
-- Put editors in the rectangles.
