{-# OPTIONS --copatterns #-}
{-# IMPORT Ex4Haskell #-}
{-# IMPORT System.IO #-}

module Ex4 where

{- I'm sorry I haven't quite finished setting this exercise yet, but by
   the joy of version control, the rest of it can be merged in later
   (quite soon). At least you can get cracking: I promise not to break
   anything, just to add a bit more on the end.

   The deadline for this is Friday of Week 12 (11 Dec).
   It'd be good to get the marks in before Christmas, but if the end of
   term is looking deadlinetastic, please open negotiations.

   UPDATE: I had to work around a bug in Agda to get this finished, so
   it took longer than I had hoped. I apologise, and will be flexible
   with deadlines, consequently. Also, I had to tweak the setup for
   cp a little, asking you to abstract out your definition of the
   FinalState of cp. I need to refer to it in the later code. That may
   cause a wee merge conflict, easily rectified with cut and paste.
-}

open import CS410-Prelude
open import CS410-Indexed

data List (X : Set) : Set where  -- X scopes over the whole declaration...
  []    : List X                 -- ...so you can use it here...
  _::_  : X -> List X -> List X  -- ...and here.
infixr 3 _::_

{-# BUILTIN BOOL Two #-}
{-# BUILTIN TRUE tt #-}
{-# BUILTIN FALSE ff #-}
{-# BUILTIN LIST List #-}
{-# BUILTIN NIL [] #-}
{-# BUILTIN CONS _::_ #-}
{-# COMPILED_DATA List [] [] (:) #-}

postulate -- this means that we just suppose the following things exist...
  Char : Set
  String : Set
{-# BUILTIN CHAR Char #-}
{-# COMPILED_TYPE Char Char #-}
{-# BUILTIN STRING String #-}
{-# COMPILED_TYPE String String #-}

primitive -- these are baked in; they even work!
  primCharEquality : Char -> Char -> Two
  primStringAppend : String -> String -> String
  primStringToList : String -> List Char
  primStringFromList : List Char -> String


---------------------------------------------------------------------------
-- WRITING FILES, AN INTERFACE
---------------------------------------------------------------------------

{- If you possess the ability to open a file for writing, you might
   have the following interface. -}

-- States
data WriteState : Set where
  opened closed : WriteState  -- do you currently have a file open or not?

-- Commands
data WriteC : WriteState -> Set where
  openWrite   : (fileName : String)  -> WriteC closed
  writeChar   : Char                 -> WriteC opened
  closeWrite  :                         WriteC opened

-- Responses
WriteR : (j : WriteState)(c : WriteC j) -> Set
WriteR .closed (openWrite fileName)  = WriteState  -- we get told whether it worked
WriteR .opened (writeChar x)         = One  -- always works
WriteR .opened closeWrite            = One  -- always works

{- 4.1 Implement the following operation which determines the next
   state. You should ensure that you can write characters only to
   a successfully opened file, and that you can write as many as
   you want. It should also be possible to insist that a process
   closes its file. -}

writeNext : (j : WriteState)(c : WriteC j) -> WriteR j c -> WriteState
writeNext j c r = {!!}

-- the file writing interface, assembled as an indexed container
WRITE : WriteState => WriteState
WRITE = WriteC <! WriteR / writeNext


---------------------------------------------------------------------------
-- READING FILES, AN INTERFACE
---------------------------------------------------------------------------

{- To read from a file, it should be open, and you shouldn't be at the
   end of it. -}

-- States
data ReadState : Set where
  opened : (eof : Two) -> ReadState    -- eof is tt if we're at end of file
  closed : ReadState

{- 4.2 Finish the READ implementation, in accordance with the description. -}

-- Commands
data ReadC : ReadState -> Set where
  openRead    : {- your stuff -} ReadC {!!}   -- needs a filename; might not open successfully;
                                              -- might open an empty file
  readChar    : {- your stuff -} ReadC {!!}   -- makes sense only if we're not at end of file
                                              -- and might take us to end of file
  closeRead   : {- your stuff -} ReadC {!!}   -- makes sense only if the file is open

-- Responses
ReadR : (j : ReadState)(c : ReadC j) -> Set
ReadR j c = {!!}

-- next State; you need to make sure the response gives enough info
readNext : (j : ReadState)(c : ReadC j) -> ReadR j c -> ReadState
readNext j c r = {!!}

READ : ReadState => ReadState
READ = ReadC <! ReadR / readNext


---------------------------------------------------------------------------
-- COMBINING TWO INTERFACES WITH SHARED STATE
---------------------------------------------------------------------------

{- 4.3 Let's suppose we have two command-response interfaces which offer
       different functionality for the same system. Correspondingly, we'll
       have two indexed containers for the same index set. Show that you
       can combine them into one indexed container which lets you choose a
       command from either menu and evolves the state as specified by
       whichever interface offered the chosen command.
-}

_=+=_ : {I : Set} -> I => I -> I => I -> I => I
CRn0 =+= CRn1 = {!!}


---------------------------------------------------------------------------
-- WHEN IGNORANCE IS BLISS, BIS
---------------------------------------------------------------------------

{- 4.4 If we have a command-response interface with index I representing
       states of the system, show that we can index basically the same
       commands and responses over a state, I * J, where the J is just
       useless information which never changes. (This operation isn't
       super-useful on its own, but it's handy in combination with other
       things. -}

GrowR : {I J : Set} -> I => I -> (I * J) => (I * J)
GrowR CRn = {!!}

-- do the same for "growing the index on the left"

GrowL : {I J : Set} -> I => I -> (J * I) => (J * I)
GrowL CRn = {!!}


---------------------------------------------------------------------------
-- COMBINING TWO INTERFACES WITH SEPARATE STATE
---------------------------------------------------------------------------

{- 4.5 Making use of 4.3 and 4.4, show how to combine two interfaces which
       operate independently on separate state: commands from one should
       not affect the state of the other.
-}

_<+>_ : {I0 I1 : Set} -> I0 => I0 -> I1 => I1 -> (I0 * I1) => (I0 * I1)
CRn0 <+> CRn1 = {!!}


---------------------------------------------------------------------------
-- ERROR REPORTING, AN INTERFACE
---------------------------------------------------------------------------

{- I'm building the next bit for you.

   When things go wrong, we need to trigger an error condition and abort
   mission. However, if we have other stuff going on (open files, etc),
   it may not always be ok to drop everything and run away. There will
   be some states in which it is safe to escape (and deliver a suitable
   error message, perhaps) and other states in which escape should be
   impossible.

   If it is safe to issue an error message, we should be able to do so
   without fear of any response from the environment that would oblige
   us to carry on.
-}

data ErrorC {I : Set}(SafeMessage : I -> Set)(i : I) : Set where
  error : SafeMessage i -> ErrorC SafeMessage i
    -- the SafeMessage parameter tells us what is an acceptable
    -- error message in any given state; in states where this gives
    -- Zero, it will be impossible to trigger an error!

ErrorR : {I : Set}{SafeMessage : I -> Set}(i : I)(c : ErrorC SafeMessage i) -> Set
ErrorR _ _ = Zero  -- there's no comeback

errorNext : {I : Set}{SafeMessage : I -> Set}
            (i : I)(c : ErrorC SafeMessage i) -> ErrorR i c -> I
errorNext i c ()  -- so we don't have to say how the state will evolve

ERROR : {I : Set}(SafeMessage : I -> Set) -> I => I
ERROR SafeMessage = ErrorC SafeMessage <! ErrorR / errorNext


---------------------------------------------------------------------------
-- COPY A FILE
---------------------------------------------------------------------------

{- 4.6 Implement a process which, given access to suitable interfaces, will
       give the process for copying a named source file to a named target
       file. This goes in two phases.
-}

{- 4.6.1 Firstly, you should identify the command-reponse interface within
   which you need to work. You will need to be able to read and write files,
   but also to signal errors (in case a file fails to open for some reason).
   You must ensure that it is impossible for any process using your interface
   to escape with an error leaving a file open. You must also make it
   possible to guarantee that your copying process will, error or not, leave
   all files closed.
-}

CPState : Set
CPState = {!!}

CPInterface : CPState => CPState
CPInterface = {!!}

{- 4.6.2 Secondly, you should implement your copying process, working to your
   interface.
-}

FinalState : CPState -> Set
FinalState c = {!!}

cp : (sourceFile targetFile : String) -> IterIx CPInterface {!!} {!!}
cp sourceFile targetFile = {!!}

{- HINTS
  You will certainly need to build some extra bits and pieces.

  You have the components for reading, writing and error handling, and
  suitable kit with which to combine them. Reading and writing don't
  interfere with each other, but it's important to make sure that you
  can't bomb out with an error, so some shared state seems important.

  There are really two phases to the process:
    (1) getting the files open  -- this may go wrong
    (2) copying from one to the other  -- this will work if we reach it
  You might want to split these phases apart.
-}

---------------------------------------------------------------
-- TO BE CONTINUED... 
---------------------------------------------------------------

-- The rest of the exercise is to fill selected gaps in code that
-- gets your cp process to the stage where it actually compiles.

-- Agda version 2.4.2.4 is needed t compile the "copatterns" involved
-- in the code, but you should be able to complete the exercise
-- without upgrading, if you are currently using an earlier version.
-- It is only the business of generating a standalone executable that
-- needs the upgrade. Still, it'd be nice to see it go, wouldn't it?

-- The key is to build a device driver between your carefully
-- designed command-response system and "scripts" built from
-- low-level Haskell commands, maintaining the file handles
-- involved as you go.

-- Then you'll need to explain how to run the low-level script.

---------------------------------------------------------------
-- What's a Device Driver? (My bit. Do read.)
---------------------------------------------------------------

open _=>_ public

Driver :
  {I J : Set}              -- I is "high-level state" ; J, "low"
  (Sync : I -> J -> Set)   -- when are states "in sync"?
  (Hi : I => I)            -- high-level command-response system
  (Lo : J => J)            -- low-level command-response system
  -> Set
  
Driver {I}{J} Sync Hi Lo =
  forall i j -> Sync i j ->     -- whenever we're in sync,
  (c : Shape Hi i) ->           -- we can take a high-level command
  Sg (Shape Lo j) \ c' ->       -- and give the low-level version,
  (r' : Position Lo j c') ->    -- then take the low-level response
  Sg (Position Hi i c) \ r ->   -- and give the high-level version,
  Sync (index Hi i c r) (index Lo j c' r')  -- and stay in sync!


drive : forall  {I J}{Sync : I -> J -> Set}
                {Hi : I => I}{Lo : J => J}
                (D : Driver Sync Hi Lo)
                {X : I -> Set}
                (i : I)(j : J)
                (ij : Sync i j) ->  -- if we're in sync and have
                IC Hi X i ->        -- a high-level way to get an X
                IC Lo (\ j -> Sg I \ i -> Sync i j * X i) j
                  -- then we have a low-level plan to
                  -- stay in sync and get an X
drive D i j ij (c , k) =
  let x = D i j ij c ; c' = fst x ; D' = snd x
  in  c' , \ r' ->  -- issue low-level command c', get response r'
      let y = D' r' ; r = fst y ; s = snd y
      in  _ , s , k r  -- choose sync state from driver, call continuation


---------------------------------------------------------------
-- SCRIPTING COMMANDS (your bit)
---------------------------------------------------------------

{- 4.7 Complete the definition of the command response system
   for scripting commands built from another command response system,
   C. A scripted command is a whole strategy for interacting with C,
   the way you can write shell scripts which give strategies for
   issuing commands at a terminal. Your job is to give the type
   for responses (which should pack up all the responses to the
   commands) and compute the next state (which should be the state
   the system reaches when the script stops).

   Then you should construct the function which translates
   one SCRIPT C interaction to many C interactions. That's to say,
   implement the "script interpreter".
-}

SCRIPT : forall {I} -> (I => I) -> (I => I)
SCRIPT {I} C = FreeIx C (\ _ -> One) <! ScriptR / ScriptN where
  ScriptR : (i : I) -> FreeIx C (\ _ -> One) i -> Set
  ScriptR i cs = {!!}
  ScriptN : (i : I)(c : FreeIx C (\ _ -> One) i) -> ScriptR i c -> I
  ScriptN i cs rs = {!!}
  
unscript : forall {I}{X : I -> Set}(C : I => I) ->
           [ IC (SCRIPT C) X -:> FreeIx C X ]
unscript {I}{X} C (c , k) = help c k where
  help : {i : I}(c : FreeIx C (\ _ -> One) i)
         (k : (p : Position (SCRIPT C) i c) ->
                X (index (SCRIPT C) i c p)) ->
         FreeIx C X i
  help cs k = {!!}


---------------------------------------------------------------
-- An Interface to Haskell IO (also my bit)
---------------------------------------------------------------

-- an Agda Maybe-type which connects to Haskell's
data Maybe (X : Set) : Set where
  yes : X -> Maybe X
  no  : Maybe X
{-# COMPILED_DATA Maybe Maybe Just Nothing #-}

-- an Agda Either-type which connects to Haskell's
data Either (S T : Set) : Set where
  left  : S -> Either S T
  right : T -> Either S T
{-# COMPILED_DATA Either Either Left Right #-}

-- a copy of Haskell's file access more datatype
data IOMode : Set where
  readMode writeMode appendMode readWriteMode : IOMode
{-# COMPILED_DATA IOMode System.IO.IOMode System.IO.ReadMode System.IO.WriteMode System.IO.AppendMode System.IO.ReadWriteMode #-}

-- Haskell's file handles imported abstractly
postulate Handle : Set
{-# COMPILED_TYPE Handle System.IO.Handle #-}

-- The Low-Level Haskell Command-Response System. Please use wisely.

data HaskellIOCommand : Set where
  hOpen                   : String  -> IOMode  -> HaskellIOCommand
  hClose hIsEOF hGetChar  : Handle             -> HaskellIOCommand
  hPutChar                : Handle  -> Char    -> HaskellIOCommand
  hError                  : String             -> HaskellIOCommand

HaskellIOResponse : HaskellIOCommand -> Set
HaskellIOResponse (hOpen f m)     = Maybe Handle
HaskellIOResponse (hClose h)      = One
HaskellIOResponse (hIsEOF h)      = Two
HaskellIOResponse (hGetChar h)    = Char
HaskellIOResponse (hPutChar h c)  = One
HaskellIOResponse (hError e)      = Zero

HASKELLIO : One => One
HASKELLIO = (\ _ -> HaskellIOCommand) <! (\ _ -> HaskellIOResponse) / _

postulate       -- Haskell has a monad for doing IO, which we use at the top level
  IO      : Set -> Set
  return  : {A : Set} -> A -> IO A
  _>>=_   : {A B : Set} -> IO A -> (A -> IO B) -> IO B
  hOpenIO : String -> IOMode -> IO (Maybe Handle)
  hCloseIO : Handle -> IO One
  hIsEOFIO : Handle -> IO Two
  hGetCharIO : Handle -> IO Char
  hPutCharIO : Handle -> Char -> IO One
  hErrorIO : {X : Set} -> String -> IO X
  mainLoop : {S : Set} -> (S -> Either String (IO S)) -> (String -> String -> S) -> IO One
infixl 1 _>>=_
{-# BUILTIN IO IO #-}
{-# COMPILED_TYPE IO IO #-}
{-# COMPILED return (\ _ -> return)    #-}
{-# COMPILED _>>=_  (\ _ _ -> (>>=)) #-}
{-# COMPILED hOpenIO Ex4Haskell.hOpenIO #-}
{-# COMPILED hCloseIO Ex4Haskell.hCloseIO #-}
{-# COMPILED hIsEOFIO Ex4Haskell.hIsEOFIO #-}
{-# COMPILED hGetCharIO Ex4Haskell.hGetCharIO #-}
{-# COMPILED hPutCharIO Ex4Haskell.hPutCharIO #-}
{-# COMPILED hErrorIO (\ _ -> Ex4Haskell.hErrorIO) #-}
{-# COMPILED mainLoop (\ _ -> Ex4Haskell.mainLoop) #-}

-- We explain how to do one command.

doHaskellCommand : (c : HaskellIOCommand) -> IO (HaskellIOResponse c)
doHaskellCommand (hOpen n m) = hOpenIO n m
doHaskellCommand (hClose h)       = hCloseIO h
doHaskellCommand (hIsEOF h)       = hIsEOFIO h
doHaskellCommand (hGetChar h)     = hGetCharIO h
doHaskellCommand (hPutChar h c)   = hPutCharIO h c
doHaskellCommand (hError e)       = hErrorIO e

-- We need a MONAD MORPHISM to translate our HASKELLIO monad to
-- Haskell's IO Monad. A monad morphism is a function between monads
-- which respects return and >>=. Every monad morphism from a FREE
-- monad is given by explaining how to do one command.

haskellIO : forall {X} -> FreeIx HASKELLIO (\ _ -> X) <> -> IO X
haskellIO (ret x)        = return x
haskellIO (do (c , k))   = doHaskellCommand c >>= \ v -> haskellIO (k v)


---------------------------------------------------------------
-- The Driver (your bit)
---------------------------------------------------------------

-- Due to an annoying bug in Agda (which I reported and which has
-- been fixed in the head version), I had to resort to making
-- a rubbish version of One, called Dull.

postulate
  Dull : Set       -- it's a unit type
  dull : Dull      -- see? it has one thing in it?
                   -- you can't pattern match on it

-- For read and write states, we can say which handles we need to
-- know. We should know handles only when files are open.

RH : ReadState -> Set
RH (opened eof)  = Handle
RH closed        = Dull

WH : WriteState -> Set
WH opened        = Handle
WH closed        = Dull

{- 4.8 Define the appropriate notion of Sync for your notion of
   CPState. It should be a collection of the handles appropriate
   for the files currently open, built using RH and WH.

   Then build the driver, carefully. Remember, when reading, to
   check the end-of-file status as required.
-}

HANDLES : CPState -> One -> Set
HANDLES cps = {!!}

haskellDriver : Driver HANDLES CPInterface (SCRIPT HASKELLIO)
haskellDriver i j s c = {!!}


---------------------------------------------------------------
-- Putting it all together
---------------------------------------------------------------

-- A concrete STATE is some CPState for which we have
--   (i)   the right handles, and
--   (ii)  a plan for how to make progress with copying.

STATE : Set
STATE = Sg CPState \ i ->
        HANDLES i <> * IterIx CPInterface FinalState i

{- 4.9 For your chosen final state, you need to explain how to
   issue a message signalling successful completion. The empty
   string will do, but perhaps you want more. -}

finalMessage : (i : CPState) -> FinalState i -> String
finalMessage i x = {!!}

-- Now, in each state, we will either discover we're done, or
-- we'll learn the next bunch of Haskell commands to do.

runCP : STATE -> Either String (IO STATE)
runCP (i , h , cp) with force cp
runCP (i , h , cp)  | ret x  = left (finalMessage i x)
runCP (i , h , cp)  | do c   = right
  (haskellIO (unscript HASKELLIO
    (drive haskellDriver {IterIx CPInterface FinalState} i <> h c)))

{- 4.10 To complete the main program, fill in the starting
   CPState and its associated handle information. -}
   
main : IO One
main = mainLoop runCP \ src trg ->
         {!!} , {!!} , cp src trg

-- Now, to compile this (using Agda 2.4.2.4), grab a terminal and
-- issue the command
--
--   agda --compile Ex4.agda
--
-- and if you're very lucky, you should be able to issue commands
--
--   ./Ex4 <sourceFile> <targetFile>
--
-- Be careful not to overwrite your homework.
--
-- PS if in doubt about Agda versions, try
--
--   agda -V
