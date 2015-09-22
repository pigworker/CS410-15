\exercise{Numbers, Lists, Vectors}

\newcommand{\marky}[2]{\hfill\raisebox{0.2in}[0in][0in]{\textbf{(#1 mark#2)}}\vspace*{ -0.2in}}
\newcommand{\onemark}{\marky{1}{}}
\newcommand{\twomarks}{\marky{2}{s}}

This is Conor telling the story.

The exercise lives in the repository as file {\tt Ex1.agda}.

%format Ex1 = "\mbox{\tt Ex1}"
%format CS410-Prelude = "\mbox{\tt CS410-Prelude}"
\begin{code}
module Ex1 where
\end{code}

It imports |Two|, |One|, |Zero| and |==| from this file of stuff.

\begin{code}
open import CS410-Prelude
\end{code}

%format Nat = "\D{Nat}"
%format zero = "\C{zero}"
%format suc = "\C{suc}"

\section{|Nat|, the type of natural numbers}

\begin{code}
data Nat : Set where
  zero  :  Nat
  suc   :  Nat -> Nat
{-# BUILTIN NATURAL Nat #-} -- means we can write 2 for |suc (suc zero)|
\end{code}

%if False
\begin{code}
postulate HOLE : Nat -> {X : Set} -> X
\end{code}
%endif

\textbf{Terminology}~ Set and ``type''. By ``type'', I mean anything you can put to
the right of : to classify the thing to the left of :, so |Set| is a
type, as in |Nat : Set|, and |Nat| is a type, as in |zero : Nat|. Being a
|Set| is \emph{one} way of being a type, but it is not the only way. In
particular, try this (and then change your mind).

%format mySet = "\F{mySet}"
\begin{spec}
mySet : Set
mySet = Set  -- doesn't typecheck
\end{spec}

\textbf{Spot the difference} ~ In Haskell, we'd write
\begin{verbatim}
data Nat = Zero | Suc Nat
\end{verbatim}
saying what the type is called and what is in it, and then we'd find
that \verb$Zero :: Nat$ and \verb$Suc :: Nat -> Nat$. Also, constructors live in a
separate namespace, with capital initial letters.

In Agda, we say what type each thing belongs to. Everything lives in
the same namespace. Capitalism is only a social convention. I tend
to use capitals for typey things and lower case for valuey things.
And we use just the one colon for typing, not two, because types are
more important than lists.

\begin{task}[addition]
There are lots of ways to add two numbers together. Do you inspect the
first? Do you inspect the second? Make sure you get the correct numerical
answer, whatever you do. You may need to revisit this problem later, when
the way addition works has a significant impact on types.
%format +N = "\F{+N}"
%format _+N_ = "\_" +N "\_"
\begin{code}
_+N_ : Nat -> Nat -> Nat
m +N n  = (HOLE 0)
infixr 3 _+N_
\end{code}
\onemark
\end{task}

\textbf{Notation} ~
A name |_+N_| with underscores in it serves double duty.
\begin{enumerate}
\item it is a perfectly sensible \emph{prefix} operator, so |_+N_ 2 2| makes sense,
  as does |_+N_ 2|, the function which adds two
\item it describes the \emph{infix} usage of the operator, with the underscores
showing where the arguments go, with \emph{extra spacing}, so the infix
version of |_+N_ 2 2| is |2 +N 2|.
\end{enumerate}

\textbf{Notation} ~ The |infixr| declaration adds more detail to the infix usage of
|+N|. Specifically, it gives |+N| a \emph{precedence} level of 3 and ensures that
it associates to the right, so that the parser reads |1 +N 2 +N 3| as |1 +N (2 +N 3)|.

When you think you're done, see if these unit tests
typecheck.
%format testPlus1 = "\F{testPlus1}"
%format testPlus2 = "\F{testPlus2}"
%format testPlus3 = "\F{testPlus3}"
\begin{spec}
testPlus1 : 2 +N 2 == 4
testPlus1 = refl

testPlus2 : 0 +N 5 == 5
testPlus2 = refl

testPlus3 : 5 +N 0 == 5
testPlus3 = refl
\end{spec}

\begin{task}[multiplication]
There's also a lot of choice in how to multiply, but they all rely on
repeated addition. Find a way to do it.
%format *N = "\F{*N}"
%format _*N_ = "\_" *N "\_"
\begin{code}
_*N_ : Nat -> Nat -> Nat
m *N n  =  (HOLE 1)
infixr 4 _*N_
\end{code}
\onemark
\end{task}

Let me just list some unit tests. You know how to implement them.
\[\begin{array}{c}
|2 *N 2 == 4| \qquad
|0 *N 5 == 0| \qquad
|5 *N 0 == 0| \\
|1 *N 5 == 5| \qquad
|5 *N 1 == 5| \qquad
|2 *N 3 == 6|
\end{array}\]


\begin{task}[subtraction I]
Subtraction is a nuisance. How do you take a big number away from a
smaller one? Give the closest answer you can to the correct answer.
%format -N1 = "\F{{}-\!N}_{\F{1}}"
%format _-N1_ = "\_" -N1 "\_"
\begin{code}
_-N1_ : Nat -> Nat -> Nat
m -N1 n  =  (HOLE 2)
\end{code}
\onemark
\end{task}

\textbf{Unit tests}
\(\qquad
|4 -N1 2 == 2| \qquad |42 -N1 37 == 5|
\)


%format Maybe = "\D{Maybe}"
%format yes = "\C{yes}"
%format no = "\C{no}"
\section{|Maybe|}

We can allow for the possibility of failure with the |Maybe| type constructor.

\begin{code}
data Maybe (X : Set) : Set where
  yes  : X -> Maybe X
  no   : Maybe X
\end{code}

The idea is that |yes| represents computations which sucessfully deliver a value,
while |no| represents failure. It's a more principled way of dealing with garbage
input that just giving garbage output.

\textbf{Spot the difference} ~ In Haskell, |yes| is {\tt Just} and |no| is {\tt Nothing}.

\textbf{Later} ~ we'll revisit |Maybe| and define it in terms of more basic ideas.


\begin{task}[subtraction II]
Implement subtraction with a type acknowledging that failure can happen.
%format -N2 = "\F{{}-\!N}_{\F{2}}"
%format _-N2_ = "\_" -N2 "\_"
\begin{code}
_-N2_ : Nat -> Nat -> Maybe Nat
m -N2 n  =  (HOLE 3)
\end{code}
\onemark
\end{task}

\textbf{Unit tests}
\(\qquad
|4 -N2 2 == yes 2|    \qquad
|42 -N2 37 == yes 5|  \qquad
|37 -N2 42 == no|
\)



%format N>= = "\F{N\!\!>\!=}"
%format _N>=_ = "\_" N>= "\_"
\section{|N>=| as a relation, not a test}

We can define a \emph{type} |m N>= n| which answers the question
`In what way can |m| be greater than or equal to |n|?'. That is,
we are not saying how to \emph{test} the inequality, just what we
would accept as \emph{evidence} for the inequality. Evidence of
inequality (however obtained) can then be used as a guarantee that
subtraction will be error-free.

\begin{code}
_N>=_ : Nat -> Nat -> Set      -- not |Two|, but |Set|
                               -- the set of `ways it can be true'
                               -- i.e., what counts as \emph{evidence}
m      N>=  zero   =  One      -- anything is at least zero in a boring way
zero   N>=  suc n  =  Zero     -- no way is zero bigger than a successor
suc m  N>=  suc n  =  m N>= n  -- successors compare as their predecessors
\end{code}

What's funny is that it's just an ordinary program, computing by
pattern matching and recursion.

\begin{task}[subtraction III]
Implement subtraction with explicit evidence that the inputs are
amenable to subtraction. You should use the `impossible' pattern,
written |()|, to dismiss the case which should not be permitted.
%format -: = "\F{{}-\!:}"
%format -N3 = "\F{{}-\!N}_{\F{3}}"
%format _-N3_-:_ = "\_" -N3 "\_" =: "\_"
\begin{code}
_-N3_-:_ : (m : Nat) -> (n : Nat) -> m N>= n -> Nat
m -N3 n -: p  = (HOLE 4)
\end{code}
\onemark
\end{task}

\textbf{Reminder} ~ about the syntax |(m : Nat) -> (n : Nat) -> ...|
The type of both those arguments is |Nat|. However, when we write the
type this way, we can name those arguments for use further along in
the type, i.e. in the third argument. That's your first exercise with a \emph{dependent}
type. In fact, the regular syntax |Nat ->| is short for |(_ : Nat) ->| where
we don't bother naming the thing.

\textbf{Notice} ~ that we can have fancy multi-place operators.

\textbf{Unit tests}
\(\qquad
|4 -N3 2 -: <> == 2| \qquad
|42 -N3 37 -: <> == 5|
\)


\textbf{Fool's errand} ~ Fill in the missing bits to make this work:
%format testSubN3-3 = "\F{testSubN3-3}"
\begin{spec}
testSubN3-3 : 37 -N3 42 -: ? == ?
testSubN3-3 = refl
\end{spec}
Haha! Ya cannae! So comment it out.

\textbf{Reminder} ~ You can\\
\begin{tabular}{@@{}ll@@{~ ~ ~}l}
write   &  |(m : Nat) -> (n : Nat) ->| \\
as      &  |(m : Nat)(n : Nat) ->|  &  omitting all but the last |->| \\
or as   &  |(m n : Nat) ->|         &  two named args sharing a type.
\end{tabular}

\textbf{Notice} ~ how the defining equations for |N>=| play a crucial role in the
typechecking of the above.

\textbf{Notice} ~ that attempts II and III take contrasting approaches to the
problem with I. II broadens the output to allow failure. III narrows the
input to ensure success.

\textbf{Later} ~ we'll see how to make the proof-plumbing less explicit

\textbf{Suspicion} ~ Why isn't he asking us to define division?

%format List = "\D{List}"
%format [] = "\C{[]}"
%format :: = "\C{::}"
%format _::_ = "\_" :: "\_"

\section{|List|}

In Haskell, we had list types type {\tt [a]}. In Agda, we can have

\begin{code}
data List (X : Set) : Set where  -- |X| scopes over the whole declaration...
  []    : List X                 -- ...so you can use it here...
  _::_  : X -> List X -> List X  -- ...and here.
infixr 3 _::_
\end{code}

\begin{task}[concatenation]
Implement concatenation for |List|.
%format +L = "\F{+L}"
%format _+L_ = "\_" +L "\_"
\begin{code}
_+L_ : {X : Set} -> List X -> List X -> List X
xs +L ys  =  (HOLE 5)
infixr 3 _+L_
\end{code}
\onemark
\end{task}

\textbf{Reminder} ~ about the `curly braces' syntax. It's very similar to the
|(m : Nat) ->| syntax we saw, above. It describes an argument by giving
its type, |Set|, and a name |X| to allow dependency. All the braces do is
set the default usage convention that |X| is by default \emph{invisible}. Any
time you use the function |+L|, Agda will try to figure out what is
the appropriate thing to put for the invisible argument, which is the
element type for the lists. She will usually succeed, because the types
of the lists you feed in will be a dead giveaway.

\textbf{Spot the difference} ~ back when you learned Haskell, you learned about
\emph{two} ideas, \emph{functions} and \emph{polymorphism}. Now you can see that there was
only \emph{one idea}, after all. This sort of collapse will keep happening.
The world is simpler, made of a smaller number of better articulated
parts.

\textbf{Unit test} ~
\(\quad
|(0 :: 1 :: 2 :: []) +L (3 :: 4 :: [])  ==   0 :: 1 :: 2 :: 3 :: 4 :: []|
\)


\begin{task}[take I]
Given a number, |n|, and a list, |xs|, compute the first n elements of xs.
Of course, there will be a tiny little problem if the caller asks for
more elements than are available, hence the name of the function.
You must ensure that the list returned is indeed a prefix of the list
supplied, and that it has the requested length if possible, and at most
that length if not.
%format mis-take = "\F{mis\!-\!take}"
\begin{code}
mis-take : {X : Set} -> Nat -> List X -> List X
mis-take n xs  =  (HOLE 6)
\end{code}
\onemark
\end{task}


\textbf{Unit test} ~
\(\quad
|mis-take 3 (0 :: 1 :: 2 :: 3 :: 4 :: []) == 0 :: 1 :: 2 :: []|
\)




\begin{task}[take II]
Fix mis-take by acknowledging the possibility of error. Ensure that your
function returns |yes| with a list of exactly the right length if
possible, or says |no|. You may need the |with| construct to inspect the
result of the recursive call.
%format may-take = "\F{may\!-\!take}"
\begin{code}
may-take : {X : Set} -> Nat -> List X -> Maybe (List X)
may-take n xs  =  (HOLE 7)
\end{code}
\twomarks
\end{task}

\begin{tabular}{@@{}l@@{$\qquad$}l}
\textbf{Unit tests} &|may-take 3 (0 :: 1 :: 2 :: 3 :: 4 :: [])  ==  yes (0 :: 1 :: 2 :: [])|\\
&|may-take 6 (0 :: 1 :: 2 :: 3 :: 4 :: [])  ==  no|\\
&|may-take 5 (0 :: 1 :: 2 :: 3 :: 4 :: [])  ==  yes (0 :: 1 :: 2 :: 3 :: 4 :: [])|
\end{tabular}


%format length = "\F{length}"
\begin{task}[|length|]
Show how to compute the length of a list.
\begin{code}
length : {X : Set} -> List X -> Nat
length xs = (HOLE 8)
\end{code}
\onemark
\end{task}

\textbf{Unit test} ~ ~ |length (0 :: 1 :: 2 :: 3 :: 4 :: [])  ==  5|

\textbf{Head scratch} ~ What information is in a list that isn't in its length?

%format Vec = "\D{Vec}"
\section{|Vec|tors -- |List|s indexed by length}

We seem to be troubled by things fouling up when lists have the wrong
length. Here's a way to make list-like structures whose types let us
keep tabs on length: the `vectors'.

\begin{code}
data Vec (X : Set) : (n : Nat) -> Set where -- |n|'s not in scope after |where|
  []    : Vec X zero                                  -- it's |zero| here,...
  _::_  : {n : Nat} -> X -> Vec X n -> Vec X (suc n)  -- ...|suc|cessor, there
\end{code}

\textbf{Don't panic} ~
|Vec X| is not a |Set|, but rather an \emph{indexed family} of sets. For each |n : Nat|,
|Vec X n| is a |Set|. The index, |n|, is the length. The constructors are
just like those of |List|, except that their types also tell the truth
about length, via the index.

\textbf{Notice} ~ that when we write a `cons', |x :: xs|, the length of the tail, |xs|,
is an invisible argument.

\textbf{Don't panic} ~ about the reuse of constructor names. We're usually starting
with types and working towards code, so it is almost always clear which
type's constructors we mean.

\textbf{Suspicion} ~ We declared |List|, then wrote |length|, then invented |Vec|.
Perhaps there is some way to say |Vec| is |List| indexed by |length| and
have it invented for us.


\begin{task}[concatenation]
When we concatenate vectors, we add their lengths.
%format +V = "\F{+V}"
%format _+V_ = "\_" +V "\_"
\begin{code}
_+V_ : {X : Set}{m n : Nat} -> Vec X m -> Vec X n -> Vec X (m +N n)
xs +V ys  = (HOLE 9)
infixr 3 _+V_
\end{code}
\onemark
\end{task}

\textbf{Notice} ~  that even though |m| and |n| are numbers, not types, they can
still be invisible.

\textbf{Don't panic} ~ if this doesn't work out to be just as easy (or even easier)
than for lists. You may need to tinker with your definition of |+N| to
make |+V| typecheck smoothly. That's because the defining equations for
|+N| are all the typechecker has to go on when seeing that your code
here fits together properly.

\textbf{Comedy} ~ See how much of this program you can persuade Agda to write
for you, using the {\tt C-c C-a} variations.

\textbf{Unit test} ~
\(\quad
|(0 :: 1 :: 2 :: []) +V (3 :: 4 :: [])  ==   0 :: 1 :: 2 :: 3 :: 4 :: []|
\)

%format take = "\F{take}"
\begin{task}[|take|]
Now we know the lengths, we can give a \emph{precondition} for taking.
\begin{code}
take : {X : Set}{m : Nat}(n : Nat) -> m N>= n -> Vec X m -> Vec X n
take n p xs = (HOLE 10)
\end{code}
\twomarks
\end{task}

\begin{tabular}{@@{}l@@{$\qquad$}l}
\textbf{Unit tests} &|take 3 <> (0 :: 1 :: 2 :: 3 :: 4 :: [])  ==  0 :: 1 :: 2 :: []|\\
&|take <> 5 (0 :: 1 :: 2 :: 3 :: 4 :: [])  ==  0 :: 1 :: 2 :: 3 :: 4 :: []|
\end{tabular}

\textbf{Fool's errand} ~ ~ |take 6 ? (0 :: 1 :: 2 :: 3 :: 4 :: []) ==  ?|


\section{Chopping}

%format Choppable = "\D{Choppable}"
Here's a thing you'd struggle to do in Haskell. It's really about seeing.
A vector of length |m +N n| is |Choppable| if you can show how it is given
by concatenating a vector of length |m| and a vector of length |n|.
%format chopTo = "\C{chopTo}"
\begin{code}
data Choppable {X : Set}(m n : Nat) : Vec X (m +N n) -> Set where
  chopTo : (xs : Vec X m)(ys : Vec X n) -> Choppable m n (xs +V ys)
\end{code}

%format chop = "\F{chop}"
\begin{task}[|chop|]
Show that vectors are |Choppable|.
\begin{code}
chop : {X : Set}(m n : Nat)(xs : Vec X (m +N n)) -> Choppable m n xs
chop m n xs = (HOLE 11)
\end{code}
\twomarks
\end{task}

\textbf{Don't panic} ~ if you can't pattern match on the vector right away, because
the fact is that without looking at \emph{where to chop}, you don't know if you
need to.

\textbf{Hint} ~  You can access vectors only from the `left end', which is a big
clue about which number you should inspect.

\textbf{Hint} ~  Much like in |-N2| and |may-take|, you will probably benefit from using
the |with| feature to allow you to match on the outcome of a recursive
call.

\textbf{Remember} ~  if dotty things appear spontaneously in your patterns. That's
knowledge for free: the pattern checker is saying `you don't need to ask,
because I know that the only thing which goes here is such-and-such'.

\textbf{Unit test} ~ ~ |chop 3 2 (0 :: 1 :: 2 :: 3 :: 4 :: []) ==  chopTo (0 :: 1 :: 2 :: []) (3 :: 4 :: [])|

\textbf{Suspicion} ~ Unit tests may, in this case, be a little beside the point.

\textbf{Terminology} ~ we call this method `constructing a view' of vectors. The
|data| type Choppable explains how we would like to be able to look at
vectors. The chop function \emph{proves} that we always can. We get for free
that we can look at vectors as being made by |[]| and |::|, but now we
can \emph{program} new ways of looking: vectors as made by |+V|.

Welcome to the new programming.
