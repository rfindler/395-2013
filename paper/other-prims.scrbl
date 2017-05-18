#lang scribble/base
@(require "util.rkt" "cite.rkt"
          "../rkt/sub1-plot.rkt"
          (prefix-in p: plot/pict)
          scriblib/figure
	  scriblib/footnote
          "../rkt/diff-sub-div-plot.rkt")

@title[#:tag "sec:other-prims"]{Other Uses of Arithmetic}

Our case study contains other uses of arithmetic operations that
treat operations on BigNums as constant when they are not. This
section discusses them. None of the proofs in this section
have been formalized in Coq.

@section{The @raw-latex{$\log$}-time @tt{size} function}
 
The @raw-latex{$\log$}-time @tt{size} function for Braun trees,
reproduced below, performs an addition in each recursive
call that is not tracked within the monad. Performing the
sum, @raw-latex{$1 + (2*m) + zo$}, cannot always be
replaced by a constant time operation. The Braun tree
invariant, however, guarantees that @raw-latex{$zo$} is
either 0 or 1 because it is the difference in size between
the left and right subtrees of a Braun tree. Therefore, in
the worst case, evaluating @raw-latex{$1 + (2*m) + zo$}
requires time proportional to @raw-latex{$\log{m}$}.
Evaluating @tt{diff s m} to compute @raw-latex{$zo$} also
requires time proportional to @raw-latex{$\log{m}$}.
Therefore, ignoring the time complexity of the addition
operation does not affect our analysis of the @tt{size}
function's running time.

@(apply inline-code (extract size_log_sq_gen.v cdr))

@section{Subtraction and Division Together}

The copy functions, such as @tt{copy_log_sq}, exhibit a more complicated recursion pattern.
These functions apply two primitives
for each recursive call, subtraction by 1 and division by 2. It is not obvious that
this combination of operations is safe to ignore in run time calculations because whereas
@tt{div2} is a constant time operation, subtracting by 1, as we have already seen, is not.

@(apply inline-code (extract copy_log_sq_gen.v cdr))

We argue by strong induction that for any binary number, if we perform a sequence of
@tt{sub1} and @tt{div2} operations, the running time of the combination
is amortized constant time. More strongly, we claim that the total
run time of performing @tt{sub1} and @tt{div2} operations on a binary number
@raw-latex{$b$} until we reach 0 is @raw-latex{$3n$}, where we count iterations of
@tt{sub1} and @tt{div2} as a single unit of time and @raw-latex{$n$} is the number of
bits in @raw-latex{$b$}.

For the proof, consider a binary number @raw-latex{$b$}. If
@raw-latex{$b$} is zero the result is trivial. If
@raw-latex{$b$} is odd then there exists some @raw-latex{$b'
 < b$} such that @raw-latex{$b = 2*b'+1$}. As a list of bits,
@raw-latex{$b$} is represented by a 1 followed by the bits
in @raw-latex{$b'$}. We write this representation as
@raw-latex{$b = 1 \cdot b'$} to make the lower order bits,
upon which subtraction and division operate, explicit.
Performing a sequence of @tt{sub1} and @tt{div2} operations
on @raw-latex{$b = 1 \cdot b'$} takes 2 units of time (1
each for @tt{sub1} and @tt{div2}) to reduce to @raw-latex{
 $b'$} plus the time to perform the sequence of operations on
@raw-latex{$b'$}. By induction, we have that performing @tt{
 sub1} and @tt{div2} operations on @raw-latex{$b'$} will take
at most @raw-latex{$3*(n-1)$} units of time. Adding these
together, the sequence of operations takes no more than
@raw-latex{$3n$} units of time in total.

In the even case, for a non-zero binary number @raw-latex{
 $b$} of @raw-latex{$n$} bits, the list representation of
@raw-latex{$b$} must begin with some number, @raw-latex{
 $k$}, of zeros followed by a 1 and then the representation
of some smaller binary number. Therefore, there exists a
@raw-latex{$b'$} such that @raw-latex{$b = 0 \cdots 0 \cdot
 1 \cdot b'$} with @raw-latex{$k \leq n$} zeros at the front
of the number. Subtracting 1 from this number takes
@raw-latex{$k+1$} units of time, therefore one combination
of subtraction and division takes @raw-latex{$k+2$} units of
time and results in a number of the form @raw-latex{$1
 \cdots 1 \cdot 0 \cdot b'$} with @raw-latex{$k-1$} ones at
the front of the list. It is clear that the next @raw-latex{
 $k-1$} iterations will each take 2 units of time. Thus, to
reduce to the number @raw-latex{$0 \cdot b'$} of length
@raw-latex{$n-k$} takes @raw-latex{$3k$} units of time.
Finally, applying the induction hypothesis to the smaller
number @raw-latex{$0 \cdot b'$} completes the proof.
	
This proof shows that repeatedly subtracting by 1 and
dividing by 2 in each recursive call and terminating at 0
requires time that is linear in the number of recursive
calls. Therefore, each use of subtraction followed by
division takes amortized constant time in functions such as
@tt{copy_log_sq}, and ignoring these primitive operations
does not affect our analysis of their running time.

@figure["fig:diff-sub-div"
	@list{Average running time of @tt{sub1} and @tt{div2}}
	@diff-sub/div-plot]

@section{Branching with Subtraction and Division}

The implementation of @tt{diff}, reproduced below, exposes another
problematic recursion pattern. In the body of the last pattern
match, (@tt{bt_node x s t, S m'}), the function branches on the parity
of its input, @raw-latex{$m$}, and if the input is even subtracts 2
then divides by 2, in the odd case we see the recursion described
above of subtracting 1 then dividing by 2. Clearly, if control flow
never reaches the even case then these operations are constant time
and we may safely ignore them. If the evaluation of @tt{diff} does
reach the even case, however, then we must be certain that the
subtraction and division operations do not change our
analysis. Subtracting 1 twice from an even number takes logarithmic
time in the worst case. The first subtraction may traverse the entire
number, but the second subtraction is from an odd number and takes
constant time. @Figure-ref["fig:diff-sub-div"] presents a plot of the
average@note{The average here is the total amount of abstract time
used by the primitive operations in a call to @tt{diff} divided by the
number of recursive calls.} amount of abstract time required by
subtraction and division in each recursive call of @tt{diff}. Although
the graph only extends from 0 to 1024 this pattern extends to larger
numbers as well. The plot suggests that primitive operations used by
@tt{diff} could be characterized. The plot clearly shows it is less
than linear, and we speculate it requires only amortized constant
time. The plot suggests that a proof of this claim should be possible,
but we leave the detailed analysis and formalization to future work.

@(apply inline-code (extract diff_gen.v cdr))


@figure["fig:copy_linear-input"
        @list{Running time of @tt{copy_linear}}
        (parameterize ([p:plot-width 250]
                       [p:plot-height 250]
                       [p:plot-x-label "Copy_linear's Input"]
                       [p:plot-y-label "Sub1 Calls' Running Time"])
          ;; this plot takes a long time, but I like that last steep jump...
          (plot-with-bound 10000
                           copy_linear_sub1_points
                           copy_linear_sub1_bound))]

@section{A Tree of Subtraction and Division}
Finally, the definition of @tt{copy_linear} presents the most complicated
recursion pattern, the function recursively calls itself on @tt{n/2} and
@tt{(n-1)/2}. @Figure-ref["fig:copy_linear-input"] is a plot of the
running time of the @tt{sub1} calls that @tt{copy_linear} makes. In
gray is a plot of @raw-latex{$\lambda x. 31x + 29$}, which we believe
is an upper bound for the function. Proving that the uses of @tt{div2}
and @tt{sub1} in this function contribute only a linear factor to the
overall run time is a significant challenge. Compared to our proof that
the primitive operations in functions like @tt{copy_log_sq} which deals with
a linear sequence of operations, a proof for the primitive operations in
@tt{copy_linear} must consider a tree of all possible sequences of the operations
that evaluate @tt{n/2} and @tt{(n-1)/2}. A similar proof should be possible with
the insight that each expensive computation of @tt{(n-1)/2} takes the same number
of operations to reach the next expensive computation regardless of the path taken
down the tree, however, we have not attempted a formal proof of this claim.

@(apply inline-code (extract copy_linear_gen.v cdr))

@section{Primitive Operations Cost Recap}

The informal analysis presented above suggests that, although we have
not accounted for all language primitives, our calculations of
asymptotic run times remain unchanged. We have presented arguments
that support that it is safe to ignore certain uses of language
primitives, providing proof where possible and suggesting directions
for more formal arguments in the remaining cases.

An alternative approach is to assign a symbolic constant to the cost
of each one of these primitives following @citet[jost-carbon] and
@citet[aspinall-program]. This amounts to a vector-based cost
semantics where each element of the vector records the number of times
the corresponding operation is used. Since this is compositionally
additive, it may be used in place of our default semantics. This
approach would lend itself well to experimentally estimating the
costs, to formalize them separately, or to collapsing them into
units (as we do in the present version).
