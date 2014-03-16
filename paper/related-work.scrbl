#lang scribble/base
@(require "cite.rkt" scribble/core)
@title{Related Work}

The most closely related work to our is 
@citet[lightweight-semiformal-time-complexity-analysis-for-purely-functional-data-structures].
He presents a monad that, like ours, carries a
notion of abstract time. Unlike our monad, his
does not also carry an invariant -- in our terms
his monad construction does not have the @tt{P} argument.
This means that it is not possible to specify the
running time of many of the Braun functions, since
the size information is not available without the
additional assumption of Braunness.
Also, his monad would leave natural numbers in the
extracted code; avoiding that is a major goal
of this work. 

@citet[a-machine-checked-proof-of-the-average-case-complexity-of-quicksort-in-coq]
give a proof of the average case complexity of Quicksort
in Coq. They too use monads, but design a monad that is 
specially tailored to counting only comparison operations.
They side-step the extraction problem by abstracting the
implementation over a monad transformer and use one monad
for proving the correct running times and another for
extraction.

Xi and Pfenning first seriously studied the
idea of using dependent types to describe invariants of
data structures in practical programming 
languages@~cite[dependently-typed-datastructures
                dependent-types-in-practical-programming-diss
                dependent-types-in-practical-programming-popl]
and, indeed, even used Braun trees as 
an example in the DML language, which could
automatically prove that, for example, @tt{size_log_sq} is
correct.

@citet[functors-for-proofs-and-programs] implemented a number of
balanced binary tree implementations in Coq with proofs of 
correctness (but not running time), with the goal of high-quality 
extraction. They use the technique described in @secref["sec:conventional"].

@citet[hoare-logic-state-monad]'s Hoare state monad is like our
monad in that it exploits monadic structure to 
make proof obligations visible at just the right moments. However,
the state used in their monad has computational content and thus
is not intended to be erased during extraction.

@citet[characteristic-formulae-for-mechanized-program-verification]'s
characteristic formula generator seems to produce Coq
code with obligations similar to what our monad produces, but
it does not consider running time.

Our code builds heavily on @citet[Program-cite]'s @tt{Program} facility in Coq.

@; is this related?
@;@citet[correct-by-construction-model-transformations]


@(element (style "noindent" '()) '())
@bold{Acknowledgments.} Thanks to
Neil Toronto for help with the properties
of integer logarithms (including efficient
implementations of them).
This work grew out of a PL seminar at Northwestern;
thanks to 
Benjamin English, 
Michael Hueschen,
Daniel Lieberman,
Yuchen Liu
Kevin Schwarz,
Zach Smith, and
Lei Wang
for their feedback on early versions of the work.
