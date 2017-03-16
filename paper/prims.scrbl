#lang scribble/base
@(require "util.rkt" "cite.rkt"
          "../rkt/sub1-plot.rkt"
          (prefix-in : "../arith/sub1_gen.rkt")
          (prefix-in p: plot/pict)
          scriblib/figure
	  scriblib/footnote
          pict 
          (prefix-in c: scribble/core)
          "../rkt/diff-sub-div-plot.rkt")

@title[#:tag "sec:prims"]{Accounting for Language Primitives}

@citet[automatic-complexity-analysis]'s cost function counts all
primitive functions as constant (simply because it counts a call as
unit time and then doesn't process the body). For most primitives,
this is the right behavior. For example, field selection
functions (e.g., @tt{car} and @tt{cdr}) are certainly constant
time. Structure allocation functions (e.g., @tt{cons}) are usually
constant time when using a two-space copying collector, as most
garbage-collected languages do. Occasionally, allocation triggers
garbage collection, which we can assume amortized constant time (but not
something our framework handles).

More interestingly, and more often overlooked, however, are
numeric primitives. In a language implementation with
BigNums, integers are generally represented as a list of
digits in some large base and grade-school arithmetic
algorithms implement the various operations. 
Most of these operations do not take constant time.

For the remainder of this discussion, we assume that the
base is a power of 2. This is certainly the case if
BigNums are represented as lists of bits, but most libraries
use a larger base. For example, OCaml's library uses
@raw-latex{$2^{30}$} as the base; GMP uses either
@raw-latex{$2^{32}$} or @raw-latex{$2^{64}$}, depending on
configuration parameters. In general, we do not know of any
BigNum library that represents integers in another way.

In such libraries, division by 2, evenness testing, and checking
to see if a number is equal to 0 are all constant-time
operations. In general, addition of BigNums is not constant
time. However, certain uses of addition can be replaced by
constant-time bit operations. For instance, doubling and
adding 1 can be replaced by a specialized operation that
conses a @tt{1} on the front of the bitstring. The remainder
of this section examines each of uses of arithmetic operations
that occur in our case study.

@section{Using Addition and Subtraction to Recur}

A common pattern for functions that consume a natural number
is to count up or count down, adding 1 or subtracting 1 at
each recursive step. For example, in the extracted OCaml
code for @tt{fib}, pattern matching against @tt{S} @tt{n}
becomes a call to the @tt{pred_big_int} function.
Subtracting 1 from a number represented in binary requires
more than constant time; @tt{sub1} may need to traverse the
entire number to compute its predecessor in the general
case.

To be certain that the non-constant run time of @tt{sub1} does not affect our
calculation of the run time, we argue that the implicit subtractions
hiding inside pattern matching take amortized constant time.
Although subtraction by 1 is not always a constant time operation, it is
constant time on half of its possible inputs. That is, on any odd number represented
in binary, subtracting by 1 is a constant time operation. It follows
that any number equivalent to 2 modulo 4 will require 2 units of time
to perform the @tt{sub1} operation because @tt{sub1} will terminate after two
iterations. In general, there is a
@(c:element (c:style "relax" '(exact-chars)) '("\\(\\frac{1}{2^n}\\)"))
chance that @tt{sub1} terminates after 
@(c:element (c:style "relax" '(exact-chars)) '("\\(n\\)"))
iterations. To account for all uses of @tt{sub1} in the implementation of
@tt{fib}, we note that we will perform the @tt{sub1} operation on each number
from 1 to @raw-latex{$n$}. This gives a cost in terms of the iterations required by
@tt{sub1} that is bounded above by
@raw-latex{$n*(\frac{1}{2} + \frac{2}{4} + \frac{3}{8} + \cdots + \frac{n}{2^n} + \cdots$)}.
One can show that this infinite sum converges to @raw-latex{$2*n$}, thus for a sequence of
@raw-latex{$n$} @tt{sub1} operations this shows
that subtraction implicit in the definition of @tt{fib} requires amortized constant time.
Overall, the run time of the additions performed by @tt{fib}
will dwarf the time required by subtraction. This justifies the fact that we do not
explicitly consider the time taken by @tt{sub1} operations.

The @tt{add1} operation is dual to @tt{sub1}; on every even
number adding 1 is a constant time operation whereas
subtracting 1 is constant time on odd numbers. Therefore the
same argument we apply to show that @tt{sub1} takes
amortized constant time applies to @tt{add1}. We have not
formalized this proof in Coq.

@section{Addition in Fib}

The uses of addition in @tt{fib} are not constant time. We
did not account for the time of additions in the recursive
implementation of @tt{fib}. We did prove (in Coq), however,
that the iterative @tt{fib} function, which requires linear
time when additions are not counted, requires quadratic time
when we properly account for primitive operations.

Addition has a run time that is linear in the
number of bits of its input. Using this fact, we can prove that
iterative @tt{fib} has a run time that is asymptotic in the square of
its input.  To prove that @tt{fib}'s run time is bounded below by
@raw-latex{$n^2$}, we first observe that for all @raw-latex{$ n \geq
6$} we have that @raw-latex{$ 2^{n/2} \leq fib(n)$}.  In the
@raw-latex{$n$}th iteration of the loop, @tt{fib} adds numbers with
@raw-latex{$\frac{n}{2}$} bits in their binary representation, which
takes time on the order of @raw-latex{$\frac{n}{2}$}.  For large
enough @raw-latex{$n$}, this implies that the run time of the
additions in the iterative @tt{fib} function are bounded below by
@raw-latex{$\frac{1}{2}(6 + 7 + \cdots + n$}). This sum has a
quadratic lower bound.  Since the other primitives used in calculating
@tt{fib} run in constant time, the run time is dominated by the
addition operations, and thus the run time of @tt{fib} is bounded
below by a factor of @raw-latex{$n^2$}.

A similar argument shows that the run time of @tt{fib} has a quadratic upper bound.
Combining these two results proves that the run time of the iterative version of @tt{fib}
is asymptotically @raw-latex{$n^2$} when we account for primitive operations.

The supplementary material contains proofs of these facts in Coq (@tt{fib/fib_iter.v}).

@section{Operations on Braun Trees}

Functions that operate on Braun trees, such as @tt{size_linear} (reproduced below) and
@tt{size_log_sq} have addition patterns like
@raw-latex{$lsize + rsize + 1$} that are not obviously constant time operations.
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

Similarly, the @tt{size} function for Braun trees,
reproduced below, performs an addition in each recursive
call that is not tracked within the monad. Performing the
sum, @raw-latex{$1 + (2*m) + zo$}, can not always be
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
runtime of performing @tt{sub1} and @tt{div2} operations on a binary number
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

This proof has not been formalized in Coq.

@figure["fig:diff-sub-div"
	@list{Average running time of @tt{sub1} and @tt{div2}}
	@diff-sub/div-plot]

@section{Branching with Subtraction and Division}

The fourth problematic recursion pattern appears in the implementation
of @tt{diff}, reproduced below. In the body of the last pattern
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
average@note{The average here is the total amount of abstract time used
by the primitive operations in a call to @tt{diff} divided by the
number of recursive calls.} amount of abstract time required by
subtraction and division in each recursive call of @tt{diff}. Although
the graph only extends from 0 to 1024 this pattern extends to larger
numbers as well. The plot suggests that primitive operations used by
@tt{diff} could be characterized. We speculate it requires only
amortized constant time, although it appears less than linear. The
plot suggests that a proof of this claim should be possible, but we
leave the detailed analysis and formalization to future work.

@(apply inline-code (extract diff_gen.v cdr))


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

@section{Primitive Operations Cost Recap}

The informal analysis presented above suggests that, although we have
not accounted for all language primitives, our calculations of
asymptotic run times remain unchanged. We have presented arguments
that support that it is safe to ignore certain uses of language
primitives, providing proof where possible and suggesting directions
for more formal arguments in the remaining cases. A goal of our future
work is to formalize these arguments in Coq.

An alternative approach is to assign a symbolic constant to the the
cost of each one of these primitives following @citet[jost-carbon] and
@citet[aspinall-program]. This amounts to a vector-based cost
semantics where each element of the vector records the number of times
the corresponding operation is used. Since this is compositionally
additive, it may be used in place of our default semantics. This
approach would lend itself well to experimentally estimating the
costs, to formalize them separated, or to collapsing them into
units (as we do in the present version).


