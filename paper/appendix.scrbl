#lang scribble/base
@(require "util.rkt" "cite.rkt"
          "../rkt/sub1-plot.rkt"
          "../rkt/diff-sub-div-plot.rkt"
          (prefix-in : "../arith/sub1_gen.rkt")
          (prefix-in p: plot/pict)
          scriblib/figure
          scriblib/footnote
          pict 
          (prefix-in c: scribble/core))

@title[#:tag "sec:appendix"]{Accounting for Other Numeric Primitives}

Although we have proved the asymptotic time complexity of a number
of functions, we have not always properly accounted for language
primitives or implicit subtractions that arise from pattern matching
over natural numbers. In the context of the @tt{fib} function, as discussed in
@secref["sec:sub1"], we argue that the primitive operations that we do
not explicitly consider do not affect our calculations of
asymptotic complexity. Overall, our case studies present five classes of
recursion patterns, including that of @tt{fib}, involving language primitives whose running
times we have not accounted for within our monadic framework.
In this section we present an informal argument to justify the claim that these
uses of language primitives have no affect on our complexity analysis.
For the first three classes of recursion patterns we present informal proofs and for
the remaining two we discuss their complications and suggest directions that
may lead to formal proofs.


@section{Linear Addition and Subtraction}

The first of category of recursion patterns includes functions that perform a single @tt{add1} or @tt{sub1}
operation in each recursive call that count up or down in a completely
linear fashion. This pattern appears in the iterative @tt{fib} function
as discussed in @secref["sec:sub1"], where we argue that performing @tt{sub1}
on each number from @raw-latex{$n$} down to 0 takes linear time for the entire
sequence of @tt{sub1} operations and thus constant amortized time for each
individual @tt{sub1} operation. The @tt{add1} operation is dual to @tt{sub1};
on every even number adding 1 is a constant time operation whereas subtracting 1
is constant time on odd numbers. Therefore the same argument we apply to show
that @tt{sub1} takes amortized constant time applies to @tt{add1}.

@section{Operations on Braun Trees}

Examples from the second category
include functions that operate on Braun trees, such as @tt{size_linear} and
@tt{size_log_sq}. In @tt{size_linear}, reproduced below, the addition
@raw-latex{$lsize + rsize + 1$} is not obviously a constant time operation.
The Braun tree invariant, however, allows for an efficient implementation
of this addition. The invariant requires either that @raw-latex{$lsize = rsize$}
or @raw-latex{$lsize = rsize + 1$}. In the former case, the addition corresponds
to doubling followed by adding 1. If numbers are represented by lists of bits with
least significant bits at the front of the list, then this corresponds to consing
a 1 onto the front of the list. In the second case, the addition is equivalent to
doubling @raw-latex{$lsize$}, which can be implemented by consing a 0 onto the front
of the list of bits. In either situation the addition
operation can be transformed into a constant time operation and therefore does not
invalidate our calculation of the running time of the @tt{size_linear} function.

@(apply inline-code (extract size_linear_gen.v cdr))

Similarly, the @tt{size} function for Braun trees, reproduced below, performs an
addition in each recursive call that is not tracked within the monad. 
Performing the sum, @raw-latex{$1 + (2*m) + zo$}, can not always be replaced by a
constant time operation. The Braun tree invariant, however,  guarantees that @raw-latex{$zo$}
is either 0 or 1 because it is the difference in size between the left and right subtrees of a Braun tree.
Therefore, in the worst case, evaluating @raw-latex{$1 + (2*m) + zo$}
requires time proportional to @raw-latex{$\log{m}$}. Evaluating @tt{diff s m}
to compute @raw-latex{$zo$} also requires time proportional to @raw-latex{$\log{m}$}. Therefore, ignoring
the time complexity of the addition operation does not affect our analysis of the @tt{size} function's running time.

@(apply inline-code (extract size_log_sq_gen.v cdr))

@section{Subtraction and Division Together}

The copy functions, such as @tt{copy_log_sq}, exhibit a more complicated recursion pattern.
These functions apply two primitives
for each recursive call, subtraction by 1 and division by 2. It is not obvious that
this combination of operations is safe to ignore in run time calculations because whereas
@tt{div2} is a constant time operation, subtracting by 1, as we have already seen, is not.

@(apply inline-code (extract copy_log_sq_gen.v cdr))

We argue by strong induction that for any binary number, if we perform a sequence of
@tt{sub1} and @tt{div2} operations, the running time of the combination of the two
operations is amortized constant time. More strongly, we claim that the total
runtime of performing @tt{sub1} and @tt{div2} operations on a binary number
@raw-latex{$b$} until we reach 0 is @raw-latex{$3n$}, where we count iterations of
@tt{sub1} and @tt{div2} as a single unit of time and @raw-latex{$n$} is the number of
bits in @raw-latex{$b$}.

For the proof, consider a binary number @raw-latex{$b$}.
If @raw-latex{$b$} is zero the result is trivial. If @raw-latex{$b$} is odd then
there exists some @raw-latex{$b' < b$} such that @raw-latex{$b = 2*b'+1$}. As a list
of bits, @raw-latex{$b$} is represented by a 1 followed by the bits in @raw-latex{$b'$}.
We write this representation as @raw-latex{$b = 1 \cdot b'$} to make the lower order bits, upon which
subtraction and division operate, explicit. Performing a sequence of @tt{sub1} and @tt{div2} operations on
@raw-latex{$b = 1 \cdot b'$} takes 2 units of time (1 each for @tt{sub1} and @tt{div2}) to reduce to
@raw-latex{$b'$} plus the time to perform the sequence of operations on @raw-latex{$b'$}.
By induction, we have that performing @tt{sub1} and @tt{div2} operations on @raw-latex{$b'$} will take
at most @raw-latex{$3*(n-1)$} units of time. Adding these together, the sequence of operations takes
no more than @raw-latex{$3n$} units of time in total.

In the even case, for a non-zero binary number @raw-latex{$b$} of @raw-latex{$n$} bits, the
list representation of @raw-latex{$b$} must begin with some number, @raw-latex{$k$}, of zeros followed
by a 1 and then the representation of some smaller binary number. Therefore, there exists a
@raw-latex{$b'$} such that @raw-latex{$b = 0 \cdots 0 \cdot 1 \cdot b'$} with @raw-latex{$k \leq n$}
zeros at the front of the number. Subtracting 1 from this number takes @raw-latex{$k+1$} units of time,
therefore one combination of subtraction and division takes @raw-latex{$k+2$} units of time and results
in a number of the form @raw-latex{$1 \cdots 1 \cdot 0 \cdot b'$} with @raw-latex{$k-1$} ones at the front of the list.
It is clear that the next @raw-latex{$k-1$} iterations will each take 2 units of time. Thus,
to reduce to the number @raw-latex{$0 \cdot b'$} of length @raw-latex{$n-k$} takes @raw-latex{$3k$} units of time.
Finally, applying the induction hypothesis to the smaller number @raw-latex{$0 \cdot b'$} completes the proof.
	
This proof shows that repeatedly subtracting by 1 and dividing by 2 in each recursive call and terminating at 0
requires time that is linear in the number of recursive calls. Therefore, each use of subtraction followed by
division takes amortized constant time in functions such as @tt{copy_log_sq}, and ignoring these
primitive operations does not affect our analysis of their running time.

@figure["fig:diff-sub-div"
	@list{Average running time of @tt{sub1} and @tt{div2}}
	@diff-sub/div-plot]

@section{Branching with Subtraction and Division}

The fourth problematic recursion pattern appears in the implementation of
@tt{diff}, reproduced below. In the body of the last pattern match, (@tt{bt_node x s t, S m'}),
the function branches on the parity of its input, @raw-latex{$m$}, and if the
input is even subtracts 2 then divides by 2, in the odd case we see the
recursion described above of subtracting 1 then dividing by 2. Clearly, if
control flow never reaches the even case then these operations are constant time
and we may safely ignore them. If the evaluation of @tt{diff} does reach the even
case, however, then we must be certain that the subtraction and division operations
do not change our analysis. Subtracting 1 twice from an even number takes logarithmic
time in the worst case. The first subtraction may traverse the entire number, but the second
subtraction is from an odd number and takes constant time. @Figure-ref["fig:diff-sub-div"]
presents a plot of the average@note{The average here is the toal amount of abstract time used by the
primitive operations in a call to @tt{diff} divided by the number of recursive calls.}
amount of abstract time required by subtraction and division
in each recursive call of @tt{diff}. Although the graph only extends from 0 to
1024 this pattern extends to larger numbers as well. The plot suggests that primitive operations
used by @tt{diff} require only amortized constant time and suggest that a proof of this claim should
be possible.

@(apply inline-code (extract diff_gen.v cdr))


@;{

I was wrong about the recursion pattern for copy_linear, so that is still unaddressed,
I need to think a bit more about whether or not it is covered by one of the cases
discussed here, if not bringing back the plot and discussion from the old prims section
might be the best thing to do

The following is the old paragraph about copy_linear.
}

@figure["fig:copy_linear-input"
        @list{Running time of @tt{copy_linear}}
        (parameterize ([p:plot-width 275]
                       [p:plot-height 275]
                       [p:plot-x-label "Copy_linear's Input"]
                       [p:plot-y-label "Sub1 Calls' Running Time"])
          ;; this plot takes a long time, but I like that last steep jump...
          (plot-with-bound 10000
                           copy_linear_sub1_points
                           copy_linear_sub1_bound))]

@section{A Tree of Subtraction and Division}

Finally, the most complicated pattern is that used by @tt{copy_linear},
which recursively calls itself on @tt{n/2} and
@tt{(n-1)/2}. @Figure-ref["fig:copy_linear-input"] is a plot of the
running time of the @tt{sub1} calls that @tt{copy_linear} makes. In
gray is a plot of @raw-latex{$\lambda x. 31x + 29$}, which we believe
is an upper bound for the function. Proving that the uses of @tt{div2}
and @tt{sub1} in this function contribute only a linear factor to the
overall runtime is a significant challenge. Compared to our proof that
the primitive operations in functions like @tt{copy_log_sq} which deals with
a linear sequence of operations, a proof for the primitive operations in
@tt{copy_linear} must consider a tree of all possible sequences of the operations
that evaluate @tt{n/2} and @tt{(n-1)/2}. A similar proof should be possible with
the insight that each expensive computation of @tt{(n-1)/2} takes the same number
of operations to reach the next expensive computation regardless of the path taken
down the tree, however, we have not attempted a formal proof of this claim.

@(apply inline-code (extract copy_linear_gen.v cdr))

@section{Conclusion}

The informal analysis presented above suggests that, although we have not
accounted for all language primitives, our calculations of asymptotic run times
remain unchanged. We have presented arguments that support that it is safe to ignore
certain uses of language primitives, providing proof where possible and suggesting
directions for more formal arguments in the remaining cases.








