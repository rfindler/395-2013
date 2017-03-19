#lang scribble/base
@(require "util.rkt" "cite.rkt"
          "../rkt/sub1-plot.rkt"
          (prefix-in p: plot/pict)
          scriblib/figure
	  scriblib/footnote
          pict
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
garbage collection, which we can assume is amortized constant time (but not
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
of this section explores how BigNum arithmetic affects
the running time computations of various functions.

@section[#:tag "sec:add-and-subtract"]{Addition and Subtraction}

To get us started, here is the implementation of @tt{sub1} in
terms of constant-time BigNum operations, written in our monad:

@(apply inline-code (extract sub1_gen.v cdr))

where @tt{sub1_result} asserts that the result of
the function is one less than the input and
that the running time is a function in @raw-latex{$O(\log(n))$}.

The use of @tt{n - 1} may seem strange in the last line
of the function, but in that case we know that @tt{n} is
odd, so that operation corresponds to zeroing the last
bit of the number, a constant time operation.

Unlike the conventional implementation of on Peano arithmetic,
this function is not constant time. Specifically, if the
@tt{if} expression always takes the true branch, then
the function will traverse the entire representation of the
number. This possible path through the function is why it
takes @raw-latex{$\log$} time; the representation of the number
takes space proportional to @raw-latex{$\log$} of its value.

In addition to @tt{sub1},
our library contains implementations of @tt{add1}, addition,
and multiplication, together with proofs that
@tt{add1} is  @raw-latex{$O(\log(n))$},
addition is
@raw-latex{$\Theta(\log(\max(m,n)))$}, and
multiplication is
@raw-latex{$\Theta(\log(n)\cdot(log(m)+\log(n)))$}.

@section{Using Subtraction to Recur}

A common pattern for functions in our case study is to consume a natural number
and count down, subtracting 1 at
each recursive step. A naive analysis based on the result in
@secref["sec:add-and-subtract"] suggests that this could add
a @raw-latex{$\log$} factor to the running time, but that is
not a tight bound.

Although subtraction by 1 is not always a constant time operation, it is
constant time on half of its possible inputs. That is, on any odd number,
subtracting by 1 is a constant time operation. Similarly,
any number equivalent to 2 modulo 4 will require 2 units of time
to perform the @tt{sub1} operation because @tt{sub1} will terminate after two
iterations. In general, there is a @raw-latex{\(\frac{1}{2^n}\)}
chance that @tt{sub1} terminates after @raw-latex{\(n\)} iterations.

To account for all uses of @tt{sub1} in the implementation of a
function that counts down, we note that we perform the @tt{sub1} operation on each number
from 1 to @raw-latex{$n$}. This gives a cost in terms of the iterations required by
@tt{sub1} that is bounded above by
@raw-latex{$n*(\frac{1}{2} + \frac{2}{4} + \frac{3}{8} + \cdots + \frac{n}{2^n} + \cdots$)}.
One can show that this infinite sum converges to @raw-latex{$2*n$}, thus for a sequence of
@raw-latex{$n$} @tt{sub1} operations require amortized constant time.

We have proved this using our monad, showing that this function is linear time:

@(apply inline-code (extract sub1_linear_loop_gen.v cdr))

@section{Addition in Fib}

We did not account for the time of additions in the
recursive implementation of @tt{fib}. We did prove, however,
that the iterative @tt{fib} function, which requires linear
time when additions are considered constant time, requires
quadratic time when we properly account for primitive
operations.

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

A similar argument shows that the run time of @tt{fib} has a
quadratic upper bound. Combining these two results proves
that the run time of the iterative version of @tt{fib} is
@raw-latex{$\Theta(n^2)$} when we properly account for
primitive operations.

The supplementary material contains proofs of these facts in
Coq (@tt{fib/fib_iter.v}).


@section{The @tt{size_linear} Function}

The @tt{size_linear} function, reproduced below has the addition expression
@raw-latex{$lsize + rsize + 1$} that is not obviously a constant time operation.
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

On the left is the Okasaki's original linear time @tt{size} function, translated
into Coq and on the right is a version that uses only constant-time BigNum operations.

@tabular[(let ([lines1 (extract size_linear_gen.v cdr)]
               [lines2 (extract size_linear_bin_gen.v cdr)])
           (list
            (list
             (apply inline-code
                    "\n"
                    (append
                     lines1
                     (build-list (- (length lines2) (length lines1)) (λ (i) "\n"))))
             (apply inline-code "\n" lines2))))]

We proved both of them have the same running time (where the
primitive operations in each count as unit time) and both
compute the correct result.
