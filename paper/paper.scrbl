#lang scribble/sigplan

@(require "util.rkt" "cite.rkt" 
          scriblib/footnote
          scribble/core
          scribble/latex-properties)

@title[#:style (style #f (list (tex-addition #"\\usepackage{inconsolata}\n")))]{
  Putting Dependent Types to Work
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

@abstract{
 This paper presents a Coq library that lifts
 a notion of running-time into the type of a
 function and uses it to prove all nine of the algorithms
 in Okasaki's paper @italic{Three Algorithms on Braun 
  Trees} are correct and have the claimed running times.
  
 A secondary goal of this paper is to be an introduction to
 Coq. While Coq is never going to
 be as straight-forward as Logo or Scratch, it has
 has the capacity to write amazingly rich specifications
 of functions and, once you have done so, the corresponding
 proofs can be only as complex as they need to be in order
 to actually establish the specified properties. 
 This paper assumes only that its readers are familiar with
 ordinary, tree-processing functions and that they are
 willing to dig into very precise specifications of
 such functions. No familiarity with Coq itself is assumed.
}

@section{Introduction}

Running times! Whoo hoo!

@include-section["background.scrbl"]

@include-section["insert.scrbl"]

@include-section["running-time.scrbl"]

@section{The Monad}

Running-time proofs rely on an accurate static accounting
of the costs of all operations in the algorithm. However,
Coq does not provide an innate way of observing the
structure of computations, dynamically or statically.
Consider a single function application, @tt{f a} that
returns some value @tt{b}: statically, Coq will only give
us access to the type of @tt{b}, @tt{B}, and an assurance
that the @tt{b} came from @tt{f a} and dynamically, we will
only have access to the actual @tt{b}. Where comes the
cost?

One way to account for cost is to lift all actual values @tt{b} into a
pair of a @tt{B} and a natural number representing cost, then ensure
that this number is incremented appropriately at each stage of the
computation. Unfortunately, this cost would be part of the dynamic
behavior of the algorithm. In other words, @tt{insert x t} would, in
fact, return a new tree and a number. This violates our goal of having
no complexity residue in extracted programs.

In Coq parlance, the problem is that we have a pair of two @tt{Set}
values---the @tt{B} and the @tt{nat}---and @tt{Set}s are, by
definition, part of the computational content. Instead, we need to
have a @tt{Set} paired with something from the universe of truth
propositions, @tt{Prop}. The trouble is finding the right proposition.

Our model using the following lift target:

@(apply verbatim (extract monad.v "C"))

This specifies that @tt{C A P} is a dependent pair of an actual @tt{A}
value, @tt{a}, and a proof that there exists some natural @tt{an} for
which @tt{a} and @tt{an} are related by @tt{P}. The right-hand side of
this pair is a proposition, so it contribues no computational
content. On its own, a @tt{C A P} can only provide correctness proofs
about the particular @tt{a}, such as that it is Braun tree. In
particular, a @tt{C A P} makes no claim about running-times because
there is no meaning associated with the natural and there is no
constraint on how the natural is chosen.

However, once we have this lift target, we can use it as a monadic
type and build a set of operations that connect it to running-time. We
shall start with the monadic unit, @tt{ret}. Suppose an program
returns an empty list, @tt{ret nil}. Such a program takes no steps to
compute, because the value is readily available. This logic applies to
all places where a computation ends. We can reflect this in our monad
by given the following type to @tt{ret}:

@(apply verbatim (extract monad.v "ret"))

This specifies that @tt{ret} will only construct a @tt{C A P} when
given a proof, @tt{Pa0}, that the correct/runtime property holds
between the actual value return @tt{a} and the natural @tt{0}. In
practice, when we use our monad we always write @tt{ret A P a _} and
Coq produces a proof obligation to fill the @tt{_} with. In effect, we
incrementally prove that each return is valid.

This defines the leaves of running time proofs. However, we must also
provide a way of composing two computations (@tt{bind}) while
retaining the cost of each and a way to introduce a cost. The second
is simpler.

Suppose a program returns a value, @tt{a}, that takes exactly one step
to compute. We would like our proof obligation to be @tt{P a 1}. This
means that the obligation on @tt{ret}, @tt{P a 0}, will be irrelevant
or worse, wrong. However, there is a simple way out of this bind: what
if the property for the @tt{ret} were different than the property for
the entire program? In code, what if the obligation were @tt{P' a 0}?
At worse, such a change would be irrelevant because there may not be a
connection between @tt{P'} and @tt{P}. But, with this in mind we can
choose a @tt{P'} such that @tt{P' a 0} @emph{is} @tt{P a 1}. 

We previously described @tt{P} as relation between @tt{A}s and
@tt{nat}s, but in Coq this is just a function that accepts a @tt{A}
and @tt{nat} and returns a proposition. Thus, we can make @tt{P'} be
the function: @tt{fun a an => P a (an+1)}. This has the effect of
transforming the runtime obligation on @tt{ret} from above: as more
steps take cost, the property itself acrues the cost so the proof that
the verifier must provide that @tt{0} is an appropriate cost is
transformed into whatever the actual cost along that path was.

We enapsulate this logic into a simple extra-monadic operator,
@tt{inc}, that introduces a unit of cost:

@(apply verbatim (extract monad.v "inc"))

In principle, the logic for @tt{bind} is very similar. A @tt{bind}
represents a composition of two computations: an @tt{A}-producing one
and an @tt{A}-consuming, @tt{B}-producing one. If we assume that
property for @tt{A} is @tt{PA} and @tt{PB} for @tt{B}, then the type
of @tt{bind} is:

@(apply verbatim (extract monad.v "bind1"))

But, this definition is incorrect from the perspective of cost,
because it misses the key point of ensuring that whatever the cost was
for producing the @tt{A}, it is accounted for along with the cost of
producing the @tt{B}.

Suppose that the cost of generating the @tt{A} were @tt{7}, then we
should transform the property of the @tt{B} computation to be @tt{fun
b bn => PB b (bn+7)}.

However, we cannot "look inside" the @tt{A} computation to know that
it cost 7 units. Instead, we have to show that @emph{whatever} the
cost for @tt{A} was, the cost of @tt{B} is still as expected. This is
reflected in the type of @tt{bind} with:

@(apply verbatim (extract monad.v "bind2"))

Unfortunately, this is far too strong of a statement because there are
some costs @tt{an} that are too much. The only @tt{an} costs that our
proof about an application of @tt{bind} must be concerned with are
those that respect the @tt{PA} property given the @emph{actual} value
of @tt{a} that the @tt{A} computation produced. This is reflected as a
dependent type for @tt{bf}:

@(apply verbatim (extract monad.v "bind3"))

This version of @tt{bind} is complete from a cost perspective but has
one problem for practical theorem proving. The body of the function
@tt{bf} has access to the value @tt{a}, but it does not have access to
the correctness part of the property @tt{PA}. At first blush, this
doesn't matter because the proof of correctness for the result of
@tt{bf} @emph{does} have access through the hypothesis @tt{PA a
an}. But, that proof context is not available when producing the
@tt{b} result. Instead, it assumes that @tt{b} has already been
computed. This means that if the proof of @tt{PA} is necessary to
compute @tt{b}, then it will not be present. The simplest case where
this occurs is when @tt{bf} performs non-structural recursion and must
construct a well-foundness proof to perform the recursive call and
this proof relies on the correctness of the @tt{a} value. This occurs
in the Braun tree functions @tt{copy_linear}, @tt{copy_fib},
@tt{copy2}, and @tt{make_array_td} because they split a natural or a
list in half for each recursive call.

It is trivial to incorporate this information into the type of @tt{bf}
by adding an additional proposition argument that corresponds to the
right-hand side of the @tt{C A PA} value @tt{am}:

@(apply verbatim (extract monad.v "bind"))

As expected, these three operators (@tt{ret}, @tt{inc}, and @tt{bind})
extract to the identity monad, so they leave no residue in the dynamic
code. Furthermore, we have proven that the obey variants of the monad
laws that incorporate the proof obligations. The only oddity is that
the proof of @tt{bind}'s associativity relies on the verifier proving
the associativity of the correctness properties as well.

In summary, the monad works by requiring the verifier to predict the
running-time with the @tt{PA} property and then provide evidence that
the actual cost (that starts at @tt{0} and is incremented as the
property passes down) is the same as this prediction.

@section{Evaluation}

We did all of Chris's paper. See git repo.

Found a few other things:

Fold.

The bonus argument to bind.

Other things?

@section{Related Work}

@section{Conclusion}

@generate-bibliography[]