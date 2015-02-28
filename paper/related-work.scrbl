#lang scribble/base
@(require "cite.rkt" scribble/core)
@title{Related Work}

@;{

Some related work to explore:

http://www.cs.yale.edu/homes/hoffmann/publications.html

}


The most closely related work to ours is 
@citet[lightweight-semiformal-time-complexity-analysis-for-purely-functional-data-structures].
He presents a monad that, like ours, carries a
notion of abstract time. Unlike our monad, his
does not also carry an invariant -- in our terms
his monad construction does not have the @tt{P} argument.
In our opinion, figuring out the design of monad
operations that support the @tt{P} argument is
the major technical advance here.
Accordingly, 
@citet[lightweight-semiformal-time-complexity-analysis-for-purely-functional-data-structures]'s
system cannot specify the
running time of many of the Braun functions, since
the size information is not available without the
additional assumption of Braunness.
Also, his monad would leave natural numbers in the
extracted code; avoiding that is a major goal
of this work.

While @citet[resource-bound-certification]'s work does not
leverage the full expressiveness of a theorem proving system
like Coq's, it does share a similar resemblance to our approach.
Also like 
@citet[lightweight-semiformal-time-complexity-analysis-for-purely-functional-data-structures]'s
and unlike ours, it does not provide a place to carry an
invariant of the data structures that can be used to
establish running times.

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
extraction. They use an ``external'' approach, where the types
do not carry the running time information, which makes the proofs
more complex.

@citet[hoare-logic-state-monad]'s Hoare state monad is like our
monad in that it exploits monadic structure to 
make proof obligations visible at just the right moments. However,
the state used in their monad has computational content and thus
is not intended to be erased during extraction.

@citet[characteristic-formulae-for-mechanized-program-verification]'s
characteristic formula generator seems to produce Coq
code with obligations similar to what our monad produces, but
it does not consider running time.

Others have explored automatic techniques for proving 
that programs have particular resource bounds using
a variety of techniques@~cite[speed auto-parallel auto-heap recursion-in-bounded-space]
These approaches are all weaker than our approach, but
provide more automation.

We have consistently used the word ``monad'' to describe 
what our library provides and believe that that is a
usefully evocative word to capture the essence of our
library. It probably is not, however, technically accurate
because the proof information changes the types of the
operations, making it some kind of generalized form of monad,
perhaps a specialization of @citet[Atkey-generalized-monad]'s
or @citet[ACU-generalized-monad]'s.

Our code builds heavily on @citet[Program-cite]'s @tt{Program} facility in Coq.

@; is this related?
@;@citet[correct-by-construction-model-transformations]


@(element (style "noindent" '()) '())
@bold{Acknowledgments.} 
Thanks to reviewers of previous versions of this paper. Thanks to
Neil Toronto for help with the properties
of integer logarithms (including efficient
implementations of them).
This work grew out of a PL seminar at Northwestern;
thanks to 
Benjamin English, 
Michael Hueschen,
Daniel Lieberman,
Yuchen Liu,
Kevin Schwarz,
Zach Smith, and
Lei Wang
for their feedback on early versions of the work.
