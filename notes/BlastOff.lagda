%format Zero = "\D{Zero}"
%format One = "\D{One}"
%format Two = "\D{Two}"
%format == = "\D{\texttt{==}}"
%format _==_ = "\_" == "\_"
%format refl = "\C{refl}"
%format Set = "\D{Set}"

\chapter{|Two|, |One|, |Zero|, Blast Off!}

%if False
\begin{code}
module BlastOff where

data _==_ {l}{X : Set l}(x : X) : X -> Set l where
  refl : x == x
infix 1 _==_
{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}
\end{code}
%endif


The repository file {\tt CS410-Prelude.agda} contains quite a lot of
stuff that we'll need as we go along. Let us visit it selectively.
In this chapter, we'll look at the types |Two|, |One| and |Zero|,
which are each named after the number of values they contain.


\section{|Two|, the type of Boolean values}

The type |Two| represents a choice between exactly two things, i.e.,
one bit of information.
It is declared as follows.\nudge{Agda's |:| means
`is in', just like Haskell's |::|, but shorter, except that space
around |:| is essential.}
%format tt = "\C{tt}"
%format ff = "\C{ff}"
\begin{code}
data Two : Set where
  tt : Two
  ff : Two
\end{code}

In Agda, we declare a data type with the keyword `|data|', followed by
an assertion which brings a \emph{type constructor} into existence,
in this case, |Two|. Specifically, we say |Two : Set| to mean `|Two|
is in |Set|'. |Set|\nudge{|Set| is not an ordinary type. |Set| also has a type.}
is a built-in type in Agda: it is the type of
`ordinary' types.
The keyword `|where|' introduces an indented
block of further declarations, this time of \emph{data constructors},
explaining which values exist in |Two|, namely |tt| and |ff|.
In Haskell, this type is called Bool and has values True and False. I call
the type |Two| to remind you how big it is, and I use ancient abbreviations
for the constructors. We can see, clearly stated, what each of the new things
is called and what types they have.

We can give more than one name the same type by listing them left of |:|,
separated by spaces, so the whole declaration can fit on one line:
\begin{spec}
data Two : Set where tt ff : Two
\end{spec}

Agda's cunning `mixfix' syntax is not just for binary operators: it lets you
rebuild familiar notations. We can write
%format if = "\F{if}"
%format then = "\F{then}"
%format else = "\F{else}"
%format if_then_else_ = if _ then _ else _
\begin{spec}
if_then_else_ : {X : Set} -> Two -> X -> X -> X
if b then t else f = ?
\end{spec}
What have we done? We have declared the type and layout of the
if-then-else construct, then given an incomplete definition of it. As
in Haskell, |->| associates to the right. Correspondingly, the type
says that we expect to receive four inputs, an invisible |Set| called
|X|, a visible element of |Two|, then two visible elements of |X|,
before returning a value of type |X|. The invisibility of |X| is
indicated by the \emph{braces} in the type.
The underscores in the name of the operator show us the places where
the \emph{visible} arguments go, and sure enough, there are three of
them in our incomplete definition. Naming |X| allows us to
refer to |X| later in the type: we say that the rest of the type
\emph{depends} on |X|. We could have named everything, writing
\begin{spec}
if_then_else_ : {X : Set} -> (b : Two) -> (t f : X) -> X
\end{spec}
but it is often tidier to name only what is depended on.


Now hit {\tt C-c C-l} to load the file.
We see that |?| turns into a pair of
highlighted braces (a `hole'\nudge{Sometimes I call a hole a `shed' because
it's a private workspace.}) labelled 0,
\begin{spec}
if b then t else f = (HOLE 0)
\end{spec}
and that the other window shows the \emph{goal}.
\[
  |?0 : .X|
\]
It's telling us that we must explain how to fill the braces with a value
of type |X|: the \emph{dot} is to remind us that |X| is not in scope. If you
click between the braces and hit {\tt C-c C-comma}, you will get information specific
to that goal:
\[\begin{array}{l@@{\;:\;}l}
\multicolumn{2}{l}{\mbox{Goal: |.X|}}\\
\hline
|f| & |.X|\\
|t| & |.X|\\
|b| & |Two|\\
|.X| & |Set|\\
\end{array}\]
We see the \emph{goal} above the line, and the \emph{context} below. The variables
in scope, |b|, |f| and |t|, are given their types in the context. Meanwhile, we cannot
see |X| on the left, so it is not in scope, hence its dot, but it is in the context,
so types can refer to it. That tallies with the visibility information we gave in the
type.

%format MINUSL = "\mbox{\tt -l}"
%format MINUSS = "\mbox{\tt -s}"
%format MINUSC = "\mbox{\tt -c}"
So, we need a value of type |X| and we have two to choose from: |t| and |f|. We can
just guess. Try typing |t| in the hole
\begin{spec}
if b then t else f = (HOLEC t 0)
\end{spec}
and hit {\tt C-c C-space} to say `give the answer'. We get a completed program
\begin{spec}
if b then t else f = t
\end{spec}
but it probably doesn't do what we expect of if-then-else. Retreat by turning
that answer back into |?| and let's think again.

The role of a value in |Two| is to inform choices, so let us consider the
value of |b| case by case. To inspect |b|, type |b| in the goal
\begin{spec}
if b then t else f = (HOLEC b 0)
\end{spec}
and hit {\tt C-c C-c}.
Now we have
\begin{spec}
if tt then t else f = (HOLE 0)
if ff then t else f = (HOLE 1)
\end{spec}
One line has become two, and in each, |b| has been replaced by one of its possible values.
If you click in the lower hole, you can try another trick: hit {\tt C-c C-a}. Suddenly,
Agda writes some code for you.
\begin{spec}
if tt then t else f = (HOLE 0)
if ff then t else f = f
\end{spec}
That keystroke is a bit like `I feel lucky' on Google: it gives you the first well typed
thing the system can find. Sadly, if you do the same thing in the top hole, you also get |f|.
Fortunately, the {\tt C-c C-a} technology can be persuaded to work a little
harder~\cite{DBLP:conf/types/LindbladB04}. Try
typing {\tt -l}\nudge{{\tt l} for `list'} in the hole
\begin{spec}
if tt then t else f = (HOLEC (MINUSL) 0)
\end{spec}
and hitting {\tt C-c C-a}. The other window shows a list of solutions. Now, if you
type {\tt -s1}\nudge{{\tt s} for `skip', 1 for how many to skip} in the hole
\begin{spec}
if tt then t else f = (HOLEC (MINUSS 1) 0)
\end{spec}
and hit {\tt C-c C-a}, you get the finished definition:
\begin{code}
if_then_else_ : {X : Set} -> Two -> X -> X -> X
if tt then t else f = t
if ff then t else f = f
\end{code}

Of course, you could have given the answer directly, just by typing
\begin{spec}
if tt then t else f = (HOLEC (t) 0)
\end{spec}
and hitting {\tt C-c C-space}, but in more
complex situations, type-based search can really cut down effort. Moreover,
the more precise a type, the more likely it is that type-based search will
choose good solutions.

Let's see that for real, by defining the \emph{case analysis} principle
for |Two|.
%format caseTwo = "\F{caseTwo}"
\begin{spec}
caseTwo : {P : Two -> Set} -> P tt -> P ff -> (b : Two) -> P b
caseTwo t f b = (HOLE 0)
\end{spec}
The invisible argument is a \emph{function}, |P|, from |Two| to |Set|, which means that
each of |P tt| and |P ff| is a |Set|, so they can be used as the types of the visible
arguments |t| and |f|. The rest of the function type says that whichever |b : Two| we
get, we can deliver a value in |P b|. Now, if we try
\begin{spec}
caseTwo t f b = (HOLEC (t) 0)
\end{spec}
and {\tt C-c C-space}, it does not work! To give |t|, we would need to know that |b|
is |tt|, and we do not. It seems there is no choice but to look at |b|, and no choice
about the solutions in each case when we do. So, try typing {\tt -c}\nudge{{\tt c} for `case analysis} in the hole
\begin{spec}
caseTwo t f b = (HOLEC (MINUSC) 0)
\end{spec}
and hit {\tt C-c C-a}. Literally, Agda writes the program at a stroke.
\begin{code}
caseTwo : {P : Two -> Set} -> P tt -> P ff -> (b : Two) -> P b
caseTwo t f tt = t
caseTwo t f ff = f
\end{code}

Think for a moment about what just happened. The type of |if_then_else_|
did not distinguish the type of `what to do with |tt|' from `what to do
with |ff|', but the whole point of |tt| and |ff| is to be different from
each other. Moreover, the types of the branches are the same as the types
of the whole application, when the point of a conditional construct is
to learn something useful. It is a type preserving transformation to swap over
the `then' and `else' branches of every conditional in a program, or to
replace the whole conditional by one of its branches: type preserving but
meaning destroying! By contrast, the type of |caseTwo| says `if we have a
problem involving some |b : Two|, it is enough to consider two special
cases where \emph{we know what |b| is}'.


\section{|One|, the dullest type in the universe}

The type which Haskell calls |()| is what we will call |One|. Let us declare it:
%format <> = "\C{\langle\rangle}"
%format One = "\D{One}"
\begin{code}
record One : Set where
  constructor <>
\end{code}

Agda has a special syntax to declare a data type with \emph{exactly one} constructor:
it is not compulsory to name the |constructor|, but here I have done so.
We think of such a type as a |record|. |One| is the degenerate case of records where
there are \emph{no fields}. We shall have more interesting records later. The syntax
|record {}| is also permitted for the value in |One|.

Now, you might well be wondering why we don't use this variant:
%format OneD = "\D{OneD}"
\begin{code}
data OneD : Set where <> : OneD
\end{code}
and the reason is a little bit subtle.

We are permitted to write
%format caseOne = "\F{caseOne}"
\begin{code}
caseOne : {P : One -> Set} -> P <> -> (x : One) -> P x
caseOne p x = p
\end{code}
but it is forbidden to write
%format caseOneD = "\F{caseOneD}"
\begin{spec}
caseOneD : {P : OneD -> Set} -> P <> -> (x : OneD) -> P x
caseOneD p x = p  -- error |<>| != |x| of type |OneD|
\end{spec}
When the typechecker tests equality between expressions in a |data| type, it compares
their normal forms: above in |OneD|, both |<>| and |x| cannot compute any further, and
they are different, so we have a mismatch. But when the typechecker tests equality
between expressions in a |record| type, it compares the normal forms of each field
separately: |One| has no fields, so all the fields match! That is, we choose a |record|
type over a |data| type whenever we can, because the typechecker is more generous when
testing that records match. It is essential that |Two| is a |data| type, because the whole
point is that its values may vary, but for |One|, we can treat all \emph{expressions} as
equal because we know there is only one \emph{value} they can take.


\section{|Zero|, the type of the impossible}

%format Zero = "\D{Zero}"
You have seen a |record| type with no fields, where
it is easy to give a value to each field: your work is over as soon as
it starts. You might wonder whether it makes sense to define a |data|
type with no constructors, like this:
\begin{code}
data Zero : Set where
\end{code}
That definition is accepted, provided you remember to write the `|where|',
even though you put nothing there. We have given no constructors, so it is
\emph{impossible} to construct a value in |Zero|. Why is this useful?

If you're given a value in the |Zero| type, you are a very lucky person.
You can trade it in for a value in any type you want. Let's try it.
%format magic = "\F{magic}"
\begin{spec}
magic : {X : Set} -> Zero -> X
magic z = (HOLE 0)
\end{spec}
Now what happens if we do case analysis on |z|. Type |z| in the hole
\begin{spec}
magic z = (HOLEC (z) 0)
\end{spec}
and hit {\tt C-c C-c}. When we did case analysis on |Two|, one line turned
into two, so we might perhaps expect one line to vanish, but that would
make the program invisible. What actually happens is this:\nudge{In Haskell,
() is the one value in the one-valued type, also (). Agda's |()| is rather the opposite.}
\begin{code}
magic : {X : Set} -> Zero -> X
magic ()
\end{code}
The program has no right-hand side! Instead, the symbol |()|, which you can
pronounce `impossible'\nudge{Say `impossible' or blow a raspberry!}, points out why there is \emph{no problem to solve}.
Instead of explaining how to make an output, we explain why the function will
never need to: nobody can produce its input!

You will find |Zero| useful in Exercise 1, to get out of tricky situations
unscathed. You just say `This can't be happening to me!', and all of a sudden,
it isn't.


\section{Equality and unit testing}

When you have two expressions, |a : X| and |b : X| in the same type,
you can form the type |a == b| of \emph{evidence that |a| and |b| are
the same}. We'll see its declaration later, but we can start using it
before then. For the time being, the key is that |a == b| has \emph{at
most one} constructor.

If the typechecker can see why |a| and |b| are
the same, then |refl| is the constructor.

%format testIf = "\F{testIf}"
\begin{code}
testIf : if tt then ff else tt == ff
testIf = refl
\end{code}
Computing by the rules we have given,
the typechecker gets |ff| for both sides of the equation, so |refl| is
accepted as a value of the given equality type---a \emph{proof} of the
equation. This method allows us to embed unit tests directly into our
code. The unit tests must pass for the code to typecheck.

If the typechecker can see why
|a| and |b| are definitely different, then there is definitely no
constructor, so we can use `impossible'.
%format trueIsn'tFalse = "\F{trueIsn'tFalse}"
\begin{code}
trueIsn'tFalse : tt == ff -> Zero
trueIsn'tFalse ()
\end{code}

Of course, some equations might be too weird for the typechecker either
to rule them in or to rule them out. Fortunately, we can write programs
which compute evidence, just as we can write programs which compute
values. E.g., we might like to check that
\[
  |if b then tt else ff == b|
\]
but the pattern matching rules we gave for |if_then_else_| don't make that
so, just by computing. Correspondingly, we can try to implement this:
%format ifTrueFalse = "\F{ifTrueFalse}"
\begin{spec}
ifTrueFalse : (b : Two) -> if b then tt else ff == b
ifTrueFalse b = (HOLEC (refl) 0)
\end{spec}
but |refl| will not typecheck. Instead, however, we can use case analysis
to split |b| into its two possibilities. Once we know |b|'s \emph{value}
in each case, |if_then_else_| computes and we can complete the proof.
\begin{code}
ifTrueFalse : (b : Two) -> if b then tt else ff == b
ifTrueFalse  tt  = refl
ifTrueFalse  ff  = refl
\end{code}

Proving things and functional programming turn out to be remarkably similar!
