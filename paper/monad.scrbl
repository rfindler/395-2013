#lang scribble/base
@(require "util.rkt")

@title{The Monad}

One way to account for cost is to use the monad to pair an actual
value (of type @tt{B}) with a natural number representing the
computations current cost, and then ensure that this number is
incremented appropriately at each stage of the computation.
Unfortunately, this cost would be part of the dynamic behavior of the
algorithm. In other words, @tt{insert x bt} would return a new tree
and a number, violating our goal of having no complexity residue in
extracted programs.

In Coq parlance, the problem is that we have a pair of two @tt{Set}
values---the @tt{B} and the @tt{nat}---and @tt{Set}s are, by
definition, part of the computational content. Instead, we need to
have a @tt{Set} paired with something from the universe of truth
propositions, @tt{Prop}. The trouble is finding the right proposition.

We use a new function @tt{C} that consumes a type and a proposition
that is parameterized over values of the type and numbers. Specifically,
we define @tt{C}:

@(apply inline-code (extract monad.v "C"))

For a given @tt{A} and @tt{P}, @tt{C A P} is a dependent
pair of @tt{a}, a value of type @tt{A}, and a proof that
there exists some natural number @tt{an} for which @tt{a}
and @tt{an} are related by @tt{P}. The intention is to think
of the natural number as the running time and @tt{P} as
some function-specific specification of running time
(and possibly also correctness). Importantly, the right-hand side of
this pair is a proposition, so it contributes no
computational content when extracted into OCaml. 

For our @tt{insert} function, we write the result type as:
@inline-code|{
: {! res !:! @bin_tree A !<! c !>!
     (forall n, 
        Braun b n ->
        (Braun res (n+1) /\
         c = fl_log n + 1)) !}
}|

@raw-latex{\newpage}

This is a shorthand (using Coq's @tt{notation} construct) for the
following call to @tt{C}, in order to avoid duplicating the type
between @tt{!:!} and @tt{!<!}:
@inline-code|{
(C (@bin_tree A)
   (fun (res:@bin_tree A) (c:nat) =>
     (forall n, 
        Braun b n ->
        (Braun res (n+1) /\
         c = fl_log n + 1))))
}|

One important aspect of the @tt{C} type is that the @tt{nat} is bound
only by an existential, and thus is not connected to the value or the
computation. That is, when we know an expression has the type @tt{C A
P}, we do not know that its running time is correct since the proof
that the expression is that type can supply any @tt{nat} to satisfy
the existential.

Thus, in order to guarantee the correct running times,
we treat types of the form @tt{C A P} as private to the
definition of the monad and built a set of operations that
can be combined in arbitrary ways but such that their combination
ensures that the @tt{nat} used must be the running time.

The first of these operations is the monadic unit, @tt{ret}. Suppose a program
returns an empty list, @tt{<== nil}. Such a program takes no steps to
compute, because the value is readily available. This logic applies to
all places where a computation ends. To do this, we define @tt{<== x}
to be @tt{ret _ _ x _}, a use of the monad operator @tt{ret}. The 
underscores ask Coq to fill in well-typed arguments (resorting to
asking the user to provide proofs if necessary, as we saw in 
@secref["sec:insert"]).

This is the type of @tt{ret}:
@(apply inline-code (extract monad.v "ret"))

This specifies that @tt{ret} will construct a @tt{C A P} only when
given a proof, @tt{Pa0}, that the correctness/runtime property holds
between the actual value return @tt{a} and the natural number
@tt{0}. In other words, when @tt{P} predicts the running time @tt{0}.

There are two other operations in our monad: @tt{bind} that combines
two computations in the monad, summing their running times, and
@tt{inc} that adds to the count of the running time. We tackle
@tt{inc} next.

Suppose a program returns a value, @tt{a} with property @tt{P}, 
that takes exactly one step to compute. We write this using the expression:
@inline-code{
 += 1;
<== a
}
We would like our proof obligation for this expression to be @tt{P a 1}. 
We know, however that the obligation on @tt{<==}, namely @tt{P a 0}, is irrelevant
or worse, wrong. There is a simple way out of this bind, however: what
if the @tt{P} for the @tt{ret} were different than the property for
of the entire expression? In code, what if the obligation were @tt{P' a 0}?
At worse, such a change would be irrelevant because there may not be a
connection between @tt{P'} and @tt{P}. But, with this in mind we can
choose a @tt{P'} such that @tt{P' a 0} is the same as @tt{P a 1}. 

We previously described @tt{P} as relation between @tt{A}s and
@tt{nat}s, but in Coq this is just a function that accepts a @tt{A}
and @tt{nat} and returns a proposition. Thus, we can make @tt{P'} be
the function: @tt{fun a an => P a (an+1)}. This has the effect of
transforming the runtime obligation on @tt{ret} from above: as more
steps take cost, the property itself accrues the cost so the proof that
the verifier must prove that the provided @tt{0} is an appropriate cost is
transformed into whatever the actual cost along that path was.

We encapsulate this logic into a simple monadic operator,
@tt{inc}, that introduces @tt{k} units of cost:
@(apply inline-code (extract monad.v "inc"))
In programs using our monad, we write @tt{+= k; e}, a
shorthand for @tt{inc _ k _ e}.

The key point in the definition is that the property in @tt{x}'s type
is @emph{not} @tt{PA}, but a modified function that ensures the
argument is at least @tt{k}.

@raw-latex{\newpage}

In principle, the logic for @tt{bind} is very similar. A @tt{bind}
represents a composition of two computations: an @tt{A}-producing one
and an @tt{A}-consuming, @tt{B}-producing one. If we assume that
property for @tt{A} is @tt{PA} and @tt{PB} for @tt{B}, then a first
attempt at a type for @tt{bind} is:
@(apply inline-code (extract binds.v "bind1"))

This definition is incorrect from the perspective of cost,
because it misses the key point of ensuring that whatever the cost was
for producing the @tt{A}, it is accounted for along with the cost of
producing the @tt{B}.

Suppose that the cost of generating the @tt{A} were @tt{7}, then we
should transform the property of the @tt{B} computation to be @tt{fun
b bn => PB b (bn+7)}. Unfortunately, we cannot ``look inside'' the @tt{A} 
computation to know that it cost 7 units. Instead, we have to show that
@emph{whatever} the cost for @tt{A} was, the cost of @tt{B} is still as 
expected. This suggests a second attempt at a definition of @tt{bind}:
@(apply inline-code (extract binds.v "bind2"))

Unfortunately, this is far too strong of a statement because there are
some costs @tt{an} that are too much. The only @tt{an} costs that our
proof about an application of @tt{bind} must be concerned with are
those that respect the @tt{PA} property given the @emph{actual} value
of @tt{a} that the @tt{A} computation produced. 
We can use a dependent type on @tt{bf} to capture the connection
between the costs in a third attempt at the type for @tt{bind}.

@(apply inline-code (extract binds.v "bind3"))

This version of @tt{bind} is complete from a cost perspective but has
one problem for practical theorem proving. The body of the function
@tt{bf} has access to the value @tt{a}, but it does not have access to
the correctness part of the property @tt{PA}. At first blush, this
doesn't matter because the proof of correctness for the result of
@tt{bf} @emph{does} have access through the hypothesis @tt{PA a
an}. But, that proof context is not available when producing the
@tt{b} result. Instead, it assumes that @tt{b} has already been
computed. This means that if the proof of @tt{PA} is necessary to
compute @tt{b}, then we will be stuck. The simplest case where
this occurs is when @tt{bf} performs non-structural recursion and must
construct a well-foundness proof to perform the recursive call and
this proof relies on the correctness of the @tt{a} value. This occurs
in some of the functions we discuss in our case study in @secref["sec:case-study"].

It is simple to incorporate this information into the type of @tt{bf},
once you realize the need for it,
by adding an additional proposition argument that corresponds to the
right-hand side of the @tt{C A PA} value @tt{am}:
@(apply inline-code (extract monad.v "bind"))

And finally, when writing programs we use the notation
@inline-code{«x» <- «expr1» ; «expr2»}
as a shorthand for
@inline-code{bind _ _ _ _ expr1 (fun (x : _) (am : _) => expr2)}

Because all of the interesting aspects of these operations happen in
their types, the extraction of these operations have no interesting
dynamic content. Specifically @tt{ret} is simply the identity
function, @tt{inc} is a function that just returns its second argument
and @tt{bind} applies its second argument to its first.  Furthermore,
we have proven that they obey variants of the monad laws that
incorporate the proof obligations (see the file @tt{monad/laws.v} in
the supplementary material).

In summary, the monad works by requiring the verifier to predict the
running-time in the @tt{PA} property and then prove that the actual
cost (starting at @tt{0} and incrementing as the property passes down)
matches the prediction.

@raw-latex{\newpage}
