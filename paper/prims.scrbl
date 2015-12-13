#lang scribble/base
@(require "util.rkt" "cite.rkt"
          "../rkt/sub1-plot.rkt"
          (prefix-in : "../arith/sub1_gen.rkt")
          (prefix-in p: plot/pict)
          scriblib/figure
	  scriblib/footnote
          pict 
          (prefix-in c: scribble/core))

@title[#:tag "sec:sub1"]{Accounting for Language Primitives}

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

If we assume that the base is a power of 2@note{This is the case if BigNums are represented as lists of bits},
then division by 2, evenness testing, and checking to see if a number is equal to 0 are all
constant-time operations. The algorithms in our study use two other
numeric operations: @tt{+} and @tt{sub1}
(not counting the abstract comparison in the sorting functions).

In general, addition of BigNums is not constant time. However, certain
uses of addition can be replaced by constant-time bit operations. For
instance, doubling and adding 1 can be replaced by a specialized
operation that conses a @tt{1} on the front of the
bitstring. Fortunately, every time we use addition in one of the
functions in our Braun library, the operation can be replaced by one
of these efficient operations.
@;{in the appendix version this should point towards the appendix ...}


One of the more interesting uses is in the linear version of
@tt{size}, which has the sum @tt{lsize+rsize+1} where @tt{lsize} and
@tt{rsize} are the sizes of two subtrees of a Braun tree. This
operation, at first glance, doesn't seem to take constant-time. But
the Braun invariant tells us that @tt{lsize} and @tt{rsize} are either
equal, or that @tt{lsize} is @tt{rsize+1}. Accordingly, this operation
can be replaced with either @tt{lsize*2+1} or @tt{lsize*2}, both of
which are constant-time operations. Checking to see which case applies
is also constant time: if the numbers are the same, the digits at the
front of the respective lists will be the same and if they differ by
@tt{1}, those digits will be different.

The uses of addition in @tt{fib}, however, are not constant time. We
did not account for the time of additions in the recursive implementation
of @tt{fib}. We have proved, however, that the iterative @tt{fib} function,
which requires linear time when additions are not counted, requires
quadratic time when we properly account for primitive operations.

Our implementation of addition has a run time that is linear in the
number of bits of its input. Using this fact, we can prove
that iterative @tt{fib} has a run time that is asymptotic to the square of its input.
To prove that @tt{fib}'s run time is bounded below by @raw-latex{$n^2$}, we first observe that for all
@raw-latex{$ n \geq 6$} we have that @raw-latex{$ 2^{n/2} \leq fib(n)$}.
In the @raw-latex{$n$}th iteration of the loop, @tt{fib} adds numbers with
@raw-latex{$\frac{n}{2}$} bits in their binary representation, which
takes time on the order of @raw-latex{$\frac{n}{2}$}.
For large enough @raw-latex{$n$}, this implies that the run time of the
additions in the iterative @tt{fib} function are bounded below by
@raw-latex{$\frac{1}{2}(6 + 7 + \cdots + n$}). This sum has a quadratic lower bound.
Since the other primitives used in calculating @tt{fib}
run in constant time, the run time is dominated by the addition operations,
thus the run time of @tt{fib} is bounded below by a factor of @raw-latex{$n^2$}.

A similar argument shows that the run time of @tt{fib} has a quadratic upper bound.
Combining these two results proves that the run time of the iterative version of @tt{fib}
is asymptotically @raw-latex{$n^2$} when we account for primitive operations.
The supplementary material contains proofs of these facts in Coq (@tt{fib/fib_iter.v}).

Although our analysis of @tt{fib} properly accounts for addition, it
does not consider all language primitives. Specifically, the above analysis
of the @tt{fib} function ignores the subtraction that occurs
in each iteration of the loop. For example, in the extracted OCaml code  for
@tt{fib}, pattern matching against @tt{S n} becomes a call to
the @tt{pred_big_int} function. Subtracting 1 from a number represented in binary
requires more than constant time; @tt{sub1} may need to traverse the entire
number to compute its predecessor.

To be certain that the non-constant run time of @tt{sub1} does not affect our
calculation of @tt{fib}'s run time, we argue that the implicit subtractions
in the implementation of @tt{fib} take amortized constant time.
Although subtraction by 1 is not always a constant time operation, it does require
constant time on half of its possible inputs. On any odd number represented
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

Although we can account for the recursion pattern using @tt{sub1} described above that
counts down from @tt{n} to @tt{0}, there are several other recursive uses of @tt{sub1}
found in our library. For example, our implementations of @tt{copy2} and @tt{copy_insert}
loop by subtracting @tt{1} then dividing by @tt{2}. As for @tt{fib}, we have not explicitly
accounted for these other uses of @tt{sub1}. We do, however, believe that the overhead of
using @tt{sub1} in these functions does not change their asymptotic complexity, but we have
verified this only by testing and informal arguments.
