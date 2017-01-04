#lang scribble/base
@(require "cite.rkt" scribble/core)
@title[#:tag "sec:related-work"]{Related Work}

@;{

Some related work to explore:

http://www.cs.yale.edu/homes/hoffmann/publications.html

}


The most closely related work to ours is
@citet[lightweight-semiformal-time-complexity-analysis-for-purely-functional-data-structures],
which presents a monad that carries a notion of abstract time. Unlike
our monad, his does not carry an invariant -- in our terms his
construction does not have the @tt{P} argument.  In our opinion,
figuring out the design of monad operations that support the @tt{P}
argument is our major technical advance.  Accordingly, his system
cannot specify the running time of many of the Braun functions, since
the size information is not available without the additional
assumption of Braunness. Of course, one can bake the Braun invariants
into the Braun data-structure itself, which would provide them to his
monad via the function arguments, but this restricts the way the code
is written, leaves residue in the extracted code, and moves the
implementation away from an idiomatic style.  Also, his monad leaves
natural numbers in the extracted code; avoiding that is a major goal
of this work.

While @citet[resource-bound-certification]'s work does not leverage
the full expressiveness of a theorem proving system like Coq's, it
does share a similar resemblance to our approach in that it verifies
the bounded termination of programs but does not infer them.  Also
like
@citet[lightweight-semiformal-time-complexity-analysis-for-purely-functional-data-structures]'s
and unlike ours, it does not provide a place to carry an invariant of
the data structures that can be used to establish running times.

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
do not carry the running time information, whereas we use an ``internal'' approach. We discuss the distinction and our preference in @secref["sec:insert"].

@citet[hoare-logic-state-monad]'s Hoare state monad is like our
monad in that it exploits monadic structure to 
make proof obligations visible at the right moments. However,
the state used in their monad has computational content and thus
is not erased during extraction.

@citet[characteristic-formulae-for-mechanized-program-verification]
and @citet[machine-checked-union-find]'s characteristic formula
generator seems to produce Coq code with obligations similar to what
our monad produces, so that you may reason about the time resources
consumed by the program. They use a different notion of resources,
specifically the number of function entry points visited.

Others have explored automatic techniques for proving that programs
have particular resource bounds using a variety of
techniques@~cite[speed auto-parallel auto-heap
recursion-in-bounded-space] These approaches are all less expressive
and apply to fewer programs as compared to our approach, but provide
more automation and so, are better when they work.

Similarly, others have explored different approaches for accounting for
various resource bounds and costs, but we do not provide any
contribution in this area. Instead, we take an off-the-shelf cost
semantics (@citet[automatic-complexity-analysis]'s) and use it. We
believe our approach applies to other cost models.

We have consistently used the word ``monad'' to describe what our
library provides and believe that that is a usefully evocative word to
capture the essence of our library. However, they are not technically
monads for two reasons. First, the monad laws are written using an
equality, but we use an equivalence relation appropriate to our
type. Second, our types have more parameters than the single parameter
used in monads, due to the proof information residing in the types, so
our ``monad'' is actually a generalized form of a monad, a
specialization of @citet[Atkey-generalized-monad]'s or
@citet[ACU-generalized-monad]'s. @citet[hoare-logic-state-monad] and
@citet[dijkstra-monad] follow this same evocative naming convention.

Our code uses @citet[Program-cite]'s @tt{Program} facility in Coq for
writing dependently-typed programs by separating idiomatic code and
detail-oriented proofs in the program source. Without @tt{Program},
our programs would have to mix the running time proofs in with the
program, which would greatly obscure the code's connection to the
original algorithm, as one does in
@citet[lightweight-semiformal-time-complexity-analysis-for-purely-functional-data-structures].

@citet[machine-checked-union-find]'s work supports imperative code,
whereas we have only experimented with supporting proofs about
imperative programs by combining our monad's types with a variation of
the @citet[hoare-logic-state-monad] and @citet[dijkstra-monad]
monads. The types and proofs work out, but are considerably more
complicated, due in part to the complexity of proofs about imperative
programs. We consider it future work to study whether there is a more
elegant approach and develop a detailed case study.

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
