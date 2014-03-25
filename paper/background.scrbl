#lang scribble/base

@(require "util.rkt" scriblib/footnote)

@title[#:tag "sec:background"]{Warming up to Dependent Typing in Coq}

This section works through an example with the goal of bringing
across just enough Coq to be able to read the code fragments
in the rest of the paper.

One way to think about Coq's dependent type system is to start with a
type system much like that of ML or OCaml, and then layer in the
ability for types to refer not just to types in the surrounding
context, but also to ordinary program values. This ability brings
great power of specification (the conventional example being that
array operations' types can insist on in-bound access), but at the
cost of making the type checking problem much more complex than it is
in non-dependently typed programming languages.

@section[#:tag "sec:drop1"]{A First Dependently-Typed Function: @tt{drop}}

To get started, consider
the definition of a @tt{drop} function. It accepts a natural number @tt{n} and 
a list and it returns the list, but without its first @tt{n} elements.
@(apply inline-code (extract lwl.v "drop"))
Ignore the types and the @tt{len} argument for a moment
(@tt{len} is there only in support of the types).
The other two arguments are @tt{n}, the number of
elements to drop, and @tt{l}, the list to drop
them from. The body of the function starts
just after the @tt{:=} (the rest of the unexplained
parts of the header are types) and it compares
@tt{n} to @tt{0}. If they are equal, the result of
the function is just @tt{l}. If they aren't equal,
then the @tt{match} expression destructures the
list. If the list is empty, then @tt{drop} is being
asked to drop more elements than there are in the list,
so we just return the empty list. If the list isn't empty,
then we recur with the tail of the list and @tt{n-1}.

In a language like ML that supported
a natural number type @tt{nat}, the type of
@tt{drop} would be something like
@centered{@tt{drop : nat -> list 'a -> list 'a}.}
Using Coq's dependent types, however, we can
establish a relationship between the length of the input
list, the length of the output list, and the number
@tt{n}. This is what the type annotations do. Specifically,
the type of the @tt{l} argument is @tt{list_with_len len},
promising that @tt{l}'s length is @tt{len}. Using
dependency we can then promise that the result list's
length is the @tt{if} expression:
@centered{@tt{if (le_dec n len) then (len - n) else 0}}
or, in English, that @tt{drop} returns a list whose 
length is @tt{len - n}, as long as @tt{n} is less than or 
equal to @tt{len}, and @tt{0} otherwise.

Which brings us to the remaining argument: @tt{len}. It is
there just to be able to state the type of @tt{l} --- without
it, the reference to @tt{len} in the type of @tt{l} would
be a free variable, which is not allowed. This rationale is
unsatisfactory, however, and it is arguments like this
that the work in this paper aims to avoid.

@section{Type Checking in Coq: Some Assembly Required}

Before we can try to remove that argument, however, we still
have the problem of how to actually check the types for @tt{drop}. 
As you might expect, being able to mix values and types like
this can lead to thorny type-checking problems
where even decidability seems unattainable. And, indeed,
Coq is not able to type-check this program without help.
Instead it establishes some basic properties of
the function (e.g. that @tt{drop} is called with the
right number of arguments) and then drops you into a
theorem proving system with particular theorems to
be proven in order to finish type checking.

In this case, there are four. The simplest one is the one
for the @tt{empty} case in the @tt{match} expression:
@(apply inline-code (extract lwl.v "obligation2"))
This corresponds to proving that the length of the
result list (@tt{0} since it is @tt{empty}) is equal
to the declared length in @tt{drop}'s header, where
we get to assume that @tt{len} is equal to @tt{0}. 
The assumption comes from the @tt{match} expression:
we are in the @tt{empty} case so that means @tt{l}
is @tt{empty}, which means that @tt{l}'s length is
@tt{0}. To prove this, consider the two possible
outcomes of the @tt{if} expression. The @tt{else} case is immediate,
and the @tt{then} case follows from the test of the
conditional. The test says that @tt{n} is less than or equal to 
@tt{0}, so that means that @tt{n} must be exactly 0 
(since we're using the natural number type, not integers)
and since we know that @tt{len} is 0, this case simplifies
to just @tt{0 = 0 - 0}.

The other three correspond to the @tt{then} branch of the
@tt{if} in the body of @tt{drop},
that the arguments
to the recursive call match up, and
the result of the
@tt{cons} case at the end of @tt{drop}.
The most complex of these is the last one. Here's what
Coq asks you to prove, and it holds by very similar 
reasoning to the case above, just with a few more situations
to consider:
@centered{@(apply inline-code (extract lwl.v "obligation4"))}

@section[#:tag "sec:extraction-tmi"]{Extraction: Too Much Information}

Coq supports a way to extract programs with these rich
types into OCaml in order to efficiently run programs that have
been proven correct. Unfortunately, when applied to our
@tt{drop} function, we get a function that still accepts
the @tt{len} argument, even though it is not actually
used to compute the result. Indeed, the extracted code
never does anything with that value; it just pipes it
around in the function and lets it pollute 
@tt{drop}'s interface.

Even worse, however, is that these extra arguments are
not just in @tt{drop}, but they are built into the 
list data structure too, for very similar reasons. Here's the 
definition of @tt{list_with_len}:
@(apply inline-code (extract lwl.v "list_with_len"))
The keyword @tt{Inductive} is Coq's version of ML's
@tt{datatype} declaration and the corresponding ML
datatype (but without the list length information) is
@inline-code{
  datatype 'a list = 
    empty
  | cons of 'a * 'a list
}

In keeping with Coq's dependency,
an @tt{Inductive} can be parameterized over more than just types.
In this case, the first line declares that it is parameterized
over a natural number, which we use to represent the length of the list.
To support such a parameterization, Coq requires that each of the 
constructors be annotated with its return type (in ML, this annotation
is not necessary as it can always be inferred from the header). So, 
the @tt{empty} constructor is given the type @tt{list_with_len 0} to
say that it constructs lists whose lengths are @tt{0}. The 
@tt{cons} constructor similarly declares that it builds lists
whose lengths are @tt{tl_len + 1}. To do so, it must be supplied
with the length of the tail of the list, an element for the head of the list,
and the actual tail. As before, the presence of @tt{tl_len} is
disappointing. 

Coq supports declarations that tell it which arguments should be
dropped in the extracted code, but it cannot always tell when it
is sound to do so. In our example, Coq can tell that the @tt{tl_len}
argument to @tt{cons} is sound to eliminate, but not the @tt{len} argument
to @tt{drop}. 

@section[#:tag "sec:conventional"]{Dependently-typed Datastructures: Proofs as Values}

The conventional work-around to avoid the extra arguments in the extracted
code is to define two @tt{Inductive}s. 
One is a match for the extracted version of the code and thus
does not include any dependency and the other
describes only the lengths of the lists and thus can be used
in auxiliary theorems that describe how @tt{drop} treats lists.

Separating the theorems from the function, however, typically requires
longer and more complex proofs because the proof essentially has to
mimic the structure of the function. 
Still, the combination of dependent types and 
data definitions is remarkably expressive and an important part of our 
approach. Our library combines this power with expressive types directly on 
functions. For now, however, lets see how the separation plays out for @tt{drop}.

Fundamentally, the combination of dependent types and data structure definitions
gives us the power to define a datatype whose elements
correspond to proofs and whose types correspond to facts. To see how
this works, lets start with the definition of @tt{list}:
@(apply inline-code (extract l.v "list"))
It has no dependency and is a one-for-one match with the earlier ML fragment
that defines lists. Accordingly, it will extract directly into the ordinary
OCaml list type.

Here's the @tt{Inductive} definition that captures the length of a list:
@(apply inline-code (extract l.v "list_has_len"))
The first line doesn't just say @tt{list_len : Type} like the @tt{list} declaration
did. Instead, it indicates that in order to get a type, @tt{list_len} must 
first be supplied with two arguments, a @tt{list} and a @tt{nat}. Our goal
is to restrict the pairs of arguments such that @tt{(list_len empty 0)} is
a type of a tree that we can actually construct, but @tt{(list_len empty 2)} is not.

We can control which trees we allow by controlling the types of the constructors
of @tt{list_len}. That is, with an ordinary data-type definition, the only way to 
make values of the given type is by combinations of constructors. The same is true 
in Coq, but since the constructors can be given dependent types, we can encode 
much more interesting restrictions. So interesting, in fact, that we can consider
the elements of the datatype to be proofs and the types to be propositions, only 
some of which will be provable, since only some of the trees we can 
build will be well-typed. Put another way, we can read a judgment form definition
from the declaration of @tt{list_len}; it defines a relation on pairs of lists and
natural numbers that holds only when the list has the corresponding length.

The simplest tree is just to write @tt{L_empty}. This constructor
has the type @tt{list_len empty 0}, as it is written in the second line
of the definition of @tt{list_len}. And thus we know that the empty list
is considered to have length @tt{0}. 

If we want to use @tt{L_cons}, then that constructor is going to build us
a value of type @tt{(list_len (cons hd tl) (tl_len + 1))}, but only if
we can supply well-typed arguments according to the types written as
arguments to @tt{L_cons}. And, unsurprisingly, we need to supply all of 
the values whose types correspond to the restrictions you'd expect, the
key one being a value that tells us that @tt{tl} has length @tt{tl_len}.
As an example, we can write 
@inline-code{
  (L_cons 0 true empty L_Empty) :
  (list_len (cons true empty) 1)
}
to demonstrate that the singleton list containing @tt{true} has length
@tt{1}.

Once we have @tt{list_len} defined, proving the same property of @tt{drop}
corresponds to this @tt{Theorem} declaration in Coq:
@(apply inline-code (extract l.v "drop_lengths"))
This version of @tt{drop} and @tt{list} are easily extractable, producing
the expected code without any extra declarations to guide Coq.

Unfortunately, the proof that @tt{drop} behaves properly is now significantly
longer. In the version from @secref["sec:drop1"], there were four
proofs, each of which requires only one line of Coq code. The
corresponding proof for this version of the function is 20 non-trivial
lines. Perhaps unsurprisingly the proof for the current version of
@tt{drop} has the previous version's proof embedded inside it. Most of the
extra is boilerplate proof manipulation to mimic the case dispatching
that the function itself does.@note{See @tt{l.v} and @tt{lwl.v} at
  @url{https://github.com/rfindler/395-2013/tree/master/paper}
  for the fully worked examples from this section using
  both approaches.}
