#lang scribble/base
@(require "util.rkt" "cite.rkt"
          "../rkt/sub1-plot.rkt"
	  "../rkt/diff-sub-div-plot.rkt"
          (prefix-in : "../arith/sub1_gen.rkt")
          (prefix-in p: plot/pict)
          scriblib/figure
          pict 
          (prefix-in c: scribble/core))


@title[#:tag "sec:appendix"]{Appendix}

Although we have proved the asymptotic complexity for a number
of functions, we have not always properly accounted for language
primitives or implicit subtractions that arise from pattern matching
over natural numbers. In the context of the @tt{fib} function in
@secref["sec:sub1"], we argue that the primitive operations we do
not explicitly consider have do not affect our calculations of
asymptotic complexity. In this section we present a conversational
argument that the primitives we do not account for have no impact on
our complexity analysis.

In our case studies there are five classes of recursion patterns using
language primitives which we do not explicitly consider. The first of
these includes functions that perform a single @tt{add1} or @tt{sub1}
operation in each recursive call that count up or down in a completely
linear fashion. This pattern shows up in the iterative @tt{fib} function
as discussed in @secref["sec:sub1"], where we argue that performing @tt{sub1}
on each number from @raw-latex{$n$} down to 0 takes linear time for the entire
sequence of @tt{sub1} operations and thus constant amortized time for each
individual @tt{sub1} operation. The @tt{add1} operation is dual to @tt{sub1},
on every even number adding 1 is a constant time operation whereas subtracting 1
is constant time on odd numbers. Therefore the same argument we apply to show
that @tt{sub1} takes amortized constant time also shows that performing @tt{add1}
operations in a linear fashion also take amortized constant time.

Examples of the second potentially problematic uses of language primitives
include functions that operate on Braun trees such as @tt{size_linear} and
@tt{size_log_sq}. In @tt{size_linear}, reproduced below, the addition
@raw-latex{$lsize + rsize + 1$} is not necessarily a constant time operation.
The Braun tree invariant, however, allows for an efficient implementation
of this addition. The invariant requires either that @raw-latex{$lsize = rsize$}
or @raw-latex{$lsize = rsize + 1$}. In the former case, the addition corresponds
to doubling followed by adding 1. If numbers are represented as lists of bits with
least significant bits at the front of the list, then this corresponds to consing
a 1 onto the front of the list. In the second case, the addition is equivalent to
doubling @raw-latex{$lsize$}, which can be implemented by consing a 0 onto the front
of the list of bits. In either situation the potentially logarithmic time addition
operation can be transformed into a constant time operation and therefore does not
invalidate our calculation of the running time of the @tt{size_linear} function.

@(apply inline-code (extract size_linear_gen.v cdr))

Similarly, the function @tt{size}, in every recursion, performs an addition of
@raw-latex{$1 + (2*m) + zo$}, where m is the size of the right subtree and
@raw-latex{$zo$} is the difference in size between the left and right subtrees.
The Braun tree invariant guarantees that @raw-latex{zo} is either 0 or 1. Our analysis
of @tt{copy_log_sq} above shows that when @raw-latex{$zo$} is 0 this addition is a constant
time operation. Unfortunately, when @raw-latex{$zo$} is 1 the addition may take time
proportional to the number of bits in @raw-latex{$m$}. At first glance, this use of
addition seems to be more problematic than the other primitives we have considered.
In the worst case, the @tt{size} function would take logarithmic time computing
this addition in each recursive call. This would add a factor of log squared time
to runtime of @tt{size} (since the recursion depth is also logarithmic), however,
even when we ignore the time taken by this addition the runtime is already on
the order of the square of the log due to the call to @tt{diff} in each recursive call.
Therefore, for the @tt{size} function, we can ignore the exact time of this addition
without it affecting the overall complexity calculations.

@(apply inline-code (extract size_log_sq_gen.v cdr))

A more complicated recursion pattern involving language primitives may be seen in
the copy functions including @tt{copy_log_sq}. These functions apply two primitives
in each recursive call, subtraction by 1 and division by 2. It is difficult to see
immediately, that we may safely ignore this combination of operations. Clearly @tt{div2}
is a constant time operation, but subtraction by 1, as we have seen already, is not
always a constant time operation.

@(apply inline-code (extract copy_log_sq_gen.v cdr))

We argue by strong induction that for any binary number if we perform a sequence of
@tt{sub1} and @tt{div2} operations that the runtime is amortized constant time
for the combination of the two operations. More strongly, we claim that the total
runtime of performing @tt{sub1} and @tt{div2} operations on a binary number
@raw-latex{$b$} until we reach 0 is @raw-latex{$3n$}, where we count iterations of
@tt{sub1} and @tt{div2} as a single unit of time and @raw-latex{$n$} is the number of
bits in @raw-latex{$b$}.

For the proof, consider a binary number @raw-latex{$b$}.
If @raw-latex{$b$} is zero the result is trivial, if @raw-latex{$b$} is odd then there exists
some @raw-latex{$b' < b$} such that @raw-latex{$b = b'\cdot1$}, that is @raw-latex{$b = 2*b'+1$}
or equivalently @raw-latex{$b$} is @raw-latex{$b'$} with a 1 appended. Performing @tt{sub1} and
@tt{div2} on @raw-latex{$b$} takes 2 units of time (1 each for @tt{sub1} and @tt{div2}) plus the
time to perform the operation on @raw-latex{$b'$}. By induction we have that performing @tt{sub1}
and @tt{div2} operations on @raw-latex{$b'$} will take at most @raw-latex{$3*(n-1)$} units of time.
Adding these together the sequence of operations takes no more than @raw-latex{$3n$} units of time
in total.

In the even case, for a non-zero binary number @raw-latex{$b$} of @raw-latex{$n$} bits, there exists a
@raw-latex{$b'$} such that @raw-latex{$b = b'\cdot1\cdot0\cdots0$} with @raw-latex{$k \leq n$}
zeros at the end of the number. Subtracting 1 from this number takes @raw-latex{$k+1$} units of time,
therefore one combination of subtraction and division takes @raw-latex{$k+2$} units of time and results
in a number of the form @raw-latex{$ b'\cdot0\cdot1\cdots1$} with @raw-latex{$k-1$} ones in the tail.
It is clear that the next @raw-latex{$k-1$} iterations will take 2 units of time each. Thus
to reduce to the number @raw-latex{$b'\cdot0$} of length @raw-latex{$n-k$} takes @raw-latex{$3k$} units of time.
Finally, applying the induction hypothesis to the smaller number @raw-latex{$b'\cdot0$} completes the proof.

This proof shows that repeatedly subtracting by 1 and dividing by 2 in each recursive call and terminating at 0
requires time that is linear in the number of recursive calls. Therefore, each use of subtraction followed by
division takes amortized constant time in functions such as @tt{copy_log_sq} and ignoring these
primitive operations does not affect our analysis of its runtime.

The fourth problematic recursion pattern shows up in the implementation of
@tt{diff}. In the body of the last pattern match, @tt{bt_node x s t, S m'},
the function branches on the parity of its input, @raw-latex{$m$}, and if the
input was even subtracts by 2 then divides by 2, in the odd case we see the
recursion described above of subtracting 1 then dividing by 2. Clearly, if the
control flow never reaches the even case then these operations are constant time
and we may safely ignore them. If evaluation of @tt{diff} does reach the even
case, however, then we must be certain that the subtraction and division operations
do not change our analysis. Subtracting 1 twice from an even number takes logarithmic
time in the worst case. The first subtraction may traverse the entire number, but the second
subtraction is from an odd number and takes constant time. @Figure-ref["fig:diff-sub-div"]
presents a plot of the average amount of abstract time required by subtraction and division
in each recursive call of @tt{diff}, that is the total abstract time taken by the primitive
operations divided by the number of recursive calls. Although the graph only extends from 0 to
1024 this pattern extends to larger numbers as well. The plot suggests that primitive operations
used by @tt{diff} require only amortized constant time and suggest that a proof of this claim should
be possible.

@(apply inline-code (extract diff_gen.v cdr))

@figure["fig:diff-sub-div"
	@list{Running time of ... }
	@diff-sub/div-plot]

@;{
I was wrong about the recursion pattern for copy_linear, so that is still unaddressed,
I need to think a bit more about whether or not it is covered by one of the cases
discussed here, if not bringing back the plot and discussion from the old prims section
might be the best thing to do

The following is the old paragraph about copy_linear
}

Finally, the most complicated is the pattern used by @tt{copy_linear},
which recursively calls itself on @tt{n/2} and
@tt{(n-1)/2}. @Figure-ref["fig:copy_linear-input"] is a plot of the
running time of the @tt{sub1} calls that @tt{copy_linear} makes. In
gray is a plot of @raw-latex{$\lambda x. 31x + 29$}, which we believe
is an upper bound for the function. Proving that the uses of @tt{div2}
and @tt{sub1} in this function contribute only a linear factor to the
overall runtime is a significant challenge. Comparing to our proof that
the primitive operations in functions like @tt{copy_log_sq} which deals with
a linear sequence of operations, a proof for the primitive operations in
@tt{copy_linear} must consider a tree of all possible sequences of the operations
that evaluate @tt{n/2} and @tt{(n-1)/2}. A similar proof should be possible with
the realization that each expensive computation of @tt{(n-1)/2} takes the same number
of operations to reach the next expensive computation regardless of the path taken
down the tree, however, we have not attempted a formal proof of this claim.

@(apply inline-code (extract copy_linear_gen.v cdr))
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



The informal analysis presented above suggests that although we have not
accounted for all language primitives our calculations of asymptotic runtimes
remain unchanged. We have presented arguments for why we believe it is safe to ignore
certain uses of language primitives, providing proof where possible and suggesting
directions for more formal arguments in the remaining cases.








