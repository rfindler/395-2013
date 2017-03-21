#lang scribble/base
@(require "util.rkt" "cite.rkt"
          "../rkt/sub1-plot.rkt"
          racket/format
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
the running time computations of various functions in our
case study.

@section[#:tag "sec:add-and-subtract"]{Addition and Subtraction}

To get us started, here is the implementation of @tt{sub1} in
terms of constant-time BigNum operations, written in our monad:

@(apply inline-code (extract sub1_gen.v cdr))
where @tt{sub1_result} asserts that the result of
the function is one less than the input and
that the running time is a function in @raw-latex{$O(\log(n))$}.

The use of @tt{n} @tt{-} @tt{1} may seem strange in the last line
of the function, but in that case we know that @tt{n} is
odd, so that operation corresponds to zeroing the last
bit of the number, a constant time operation.

Unlike the implementation of @tt{sub1} when using Peano arithmetic,
this function is not constant time. Specifically, if the
@tt{if} expression always takes the true branch, then
the function will traverse the entire representation of the
number. This possible path through the function is why it
takes @raw-latex{$\log$} time; the representation of the number
takes space proportional to @raw-latex{$\log$} of its value.

In addition to @tt{sub1},
our library contains implementations of @tt{add1}, addition,
and multiplication, along with proofs that
@tt{add1} is  @raw-latex{$O(\log(n))$},
addition is
@raw-latex{$O(\log(\max(m,n)))$} and
@raw-latex{$\Omega(\log(\min(m,n)))$},
and the
multiplication algorithm we used is
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
This infinite sum converges to @raw-latex{$2*n$}, thus any prefix of it
is in @raw-latex{O(n)} and so
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

@citet[three-algorithms-on-braun-trees]'s @tt{size_linear}
function, shown in Coq notation on the left of
@figure-ref["fig:size-linear"], has the addition expression
@tt{lsize} @tt{+} @tt{rsize} @tt{+} @tt{1} that is not
obviously a constant time operation. The Braun tree
invariant, however, allows for this expression to be
computed in constant time. The invariant guarantees that
either @tt{lsize} equals @tt{rsize} or @tt{lsize} equals
@tt{rsize} @tt{+} @tt{1}. In the former case, the addition
corresponds to doubling @tt{lsize} followed by adding 1.
If numbers are represented by lists of bits with the least
significant bits at the front of the list, then this
corresponds to @tt{cons}ing a 1 onto the front of the list.
In the latter case, the addition is equivalent to doubling
@tt{lsize}, which can be implemented by consing a 0 onto the
front of the list of bits. The right-hand side of
@figure-ref["fig:size-linear"] shows the revised version
of @tt{size_linear} that uses only constant time BigNum operations.

@figure*["fig:size-linear" @elem{Linear-time Braun Size Functions;
          the left side is Okasaki's original function and the right side
          is the same, but in terms of constant-time BigNum operations}]{
@tabular[(let ([lines1 (extract size_linear_gen.v cdr)]
               [lines2 (extract size_linear_bin_gen.v cdr)])
           (define (inline-result-definition file lines)
             (apply
              append
              (for/list ([line (in-list lines)])
                (cond
                  [(regexp-match #rx"size_linear_[^ ]*result" line)
                   (call-with-input-file file
                     (λ (port)
                       (let loop ([found-start? #f])
                         (define l (read-line port))
                         (when (eof-object? l)
                           (error 'prims.scrbl
                                  "could not get _result definition from ~a"
                                  file))
                         (cond
                           [found-start?
                            (if (regexp-match #rx"^ *$" l)
                                '()
                                (list*
                                 (regexp-replace #rx"[.]$" l " !} :=")
                                 "\n"
                                 (loop #t)))]
                           [else
                            (if (regexp-match? #rx"Definition size_linear_[^ ]*result " l)
                                (loop #t)
                                (loop #f))]))))]
                  [else
                   (list line)]))))
           (define (chop-first-line lines)
             (define first-line (car lines))
             (define m (regexp-match #rx"(Program Fixpoint size[^ ]* )(.*)" first-line))
             (define chopped-first-line first-line)
             (list* (~a (list-ref m 1) "\n")
                    (~a "   " (list-ref m 2))
                    (cdr lines)))
           (set! lines1 (inline-result-definition size_linear.v (chop-first-line lines1)))
           (set! lines2 (inline-result-definition size_linear_bin.v (chop-first-line lines2)))
           (list
            (list
             (apply inline-code
                    "\n"
                    (append
                     lines1
                     (build-list (- (length lines2) (length lines1)) (λ (i) " \n"))))
             (apply inline-code "\n" lines2))))]}

We proved both of these functions have the same running time
(where the primitive operations in each count as unit time)
and both compute the correct result.

The proof of the running time of the @tt{size_linear}
function (on the left) does not require the assumption that
the input is a Braun tree, but the proof of the version on
the right does. Without that assumption, the resulting
size may not be correct because the result is computed
purely in terms of the size of the left sub-tree, ignoring
the right. Since the running time's correctness property is
specified in terms of the result size, when the result size
is wrong, then the running time will still be linear in the
size of the tree, but may not match the result of the
function.
