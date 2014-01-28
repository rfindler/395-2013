#lang scribble/sigplan

@(require "util.rkt")

@title{Putting Dependent Types to Work
       @subtitle{A Coq Library That Enforces Correct Running-Times via Type-Checking}}
@doi{}

@authorinfo["Jay McCarthy"
            "Brigham Young University"
            "jay@cs.byu.edu"]
@authorinfo["Burke Fetscher"
            "Northwestern University"
            "burke.fetscher@eecs.northwestern.edu"]
@authorinfo["Max New"
            "Northwestern University"
            "max.new@eecs.northwestern.edu"]
@authorinfo["Robert Bruce Findler"
            "Northwestern University"
            "robby@eecs.northwestern.edu"]

@section{Introduction}

Running times! Whoo hoo!

@section{Warming up to Dependent Typing in Coq}

One way to think about Coq's dependent type system is
to just start with type system much like
ML's or OCaml's type system, and then layer in the 
ability for types to refer not just to types in the surrounding
context, but also to ordinary program values. 

This section works through an examples with the goal of bringing
across just enough Coq to be able to read the code fragments
in the rest of the paper.

@subsection{A First Dependently-Typed Function: @tt{drop}}

To get started, consider
the definition of a @tt{drop} function that removes
the first @tt{n} elements from a list.

@(apply verbatim (extract lwl.v "drop"))

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
the type of the @tt{l} argument is @tt{list len},
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

@subsection{Typing Checkin Coq: Help Wanted}

Before we can try to remove that argument, however, we still
have the problem of how to actually check the types for @tt{drop}. 
As you might expect, being able to mix values and types like
this can lead to thorny type-checking problems
where even decidability seems unattainable. And, indeed,
Coq is not able to type-check this program without help.
Instead what it does is establish some basic properties of
the function (e.g. that @tt{drop} is called with the
right number of arguments) and then drops you into a
theorem proving system with particular theorems to
be proven in order to finish type checking.

In this case, there are four. The simplest one is the one
for the @tt{empty} case in the @tt{match} expression:
@(apply verbatim (extract lwl.v "obligation2"))
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
@tt{0}, so that means that @tt{n} must be exactly 
(since we're using the natural number type, not integers)
and since we know that @tt{len} is 0, this case simplifies
to just @tt{0 = 0 - 0}.

The other three correspond to the @tt{then} branch of the
@tt{if} in the body of @tt{bind}, 
that the arguments
to the recursive call match up, and
the result of the
@tt{cons} case at the end of @tt{bind}. 
The most complex of these is the last one. Here's what
Coq asks you to prove, and it holds by very similar 
reasoning to the case above, just with more situations
to consider:
@centered{@(apply verbatim (extract lwl.v "obligation4")).}

@subsection{Extraction: Too Much Information}

Coq supports a way to extract programs with these rich
types into OCaml. Unfortunately, when applied to our
@tt{drop} function, we get a function that still accepts
the @tt{len} argument, even though it is not actually
used to compute the result. Indeed, the extracted code
never does anything with that value; it just pipes it
around in the function and lets it pollute 
@tt{drop}'s interface.

Even worse, however, is that these extra arguments are
not just in @tt{drop}, but they are built into the list
list data-structure, too, for very similar reasons. Here's the 
definition of @tt{list_with_len}:

@(apply verbatim (extract lwl.v "list_with_len"))

The keyword @tt{Inductive} is Coq's version of ML's
@tt{datatype} declaration and the corresponding ML
datatype is
@verbatim{
  datatype 'a list = 
    empty
  | cons of 'a * 'a list
}

In keeping with Coq' dependency,
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

The standard work-around for these is to define two @tt{Inductive}s,
one that is a match for the extracted version of the code and thus
does not include any dependency, and one
that describes only the lengths of the lists and thus can be used
in auxiliary theorems that describe how @tt{drop} treats lists.

This work, however, aims to combine these two techniques via a
monad so that we can still specify sophisticated properties in
the type of the function and get functions that extract without
extra, useless arguments.
