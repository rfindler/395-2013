#lang scribble/base
@(require "util.rkt" "cite.rkt"
          (prefix-in : "../rkt/sub1.rkt")
          (prefix-in p: plot/pict)
          pict 
          (prefix-in c: scribble/core))

@title[#:tag "sec:sub1"]{Accounting for Language Primitives}

@citet[automatic-complexity-analysis]'s cost function
counts all primitive functions as constant (simply because
it counts a call as unit time and then doesn't process the
body). For most primitives, this exactly what you want. For
example, field selection functions (e.g., @tt{car} and
@tt{cdr}) are certainly constant time. Structure allocation
functions (e.g., @tt{cons}) are usually constant time, when
using a two-space copying collector, as most
garbage-collected languages do. Occasionally allocation
triggers garbage collection which is probably amortized
constant time but certainly something our framework does not
handle.

More interestingly and more often overlooked, however, are
the numeric primitives. In a language implementation with
bignums, numbers are generally represented as a list of
digits in some large base with grade-school arithmetic
algorithms implementing the various operations. These
operations are generally not all constant time. 

Assuming that the base is a power of 2, division by 2,
evenness testing, and checking to see if a number is equal
to 0 are all constant time operations. The algorithms
discussed in @secref["sec:case-study"] use only one
operation on numbers besides those: @tt{sub1}.

In general, @tt{sub1} is not constant time. It some situations,
it may need to traverse the entire number to compute its predecessor.
To explore its behavior, we implemented it using only constant-time
operations. Here's the result of our translation applied
to its implementation:
@(apply inline-code (extract sub1_gen.v cdr))

This function uses a number of primitive operations. 
If we think the representation of numbers as a linked 
listed of binary digits, then these are the operations
used by the function and their corresponding list operation:
@itemlist[@item{zero testing: empty list check,}
           @item{evenness testing: extract the first bit in the number}
           @item{floor of division by 2 (@tt{div2}): cdr}
           @item{double and add 1 (@tt{sd2+sd2+1}): cons @tt{1} onto the list}
           @item{@tt{n-1} in the case that n is odd: replace the lowest bit with @tt{0}}]
So while each iteration of the list runs in constant time, @tt{sub1} is recursive
and we do not know an a priori bound on the number of iterations.

We can use our implementation of @tt{sub1} above to graph its running
time against the value of its input:

@(c:element (c:style "noindent" '()) '())
@(centered
  (scale
   (p:plot-pict
    #:x-label "sub1's argument"
    #:y-label "number of abstract steps"
    (let ([the-points
           (for/list ([i (in-range 1 255)])
             (define-values (ans time) (:sub1 i))
             (vector i time))])
      (p:points
       #:y-min 0
       #:y-max (+ 2 (apply max (map (λ (x) (vector-ref x 1)) the-points)))
       the-points)))
   2/3))

Roughly what is happening is that half of the time (on odd numbers) @tt{sub1}
is cheap, terminating after only a single iteration. One quarter of the time
(when the number is 3 mod 4), @tt{sub1} terminates after two iterations. In general,
there is a 
@(c:element (c:style "relax" '(exact-chars)) '("\\(\\frac{1}{2^n}\\)"))
chance that @tt{sub1} terminates after 
@(c:element (c:style "relax" '(exact-chars)) '("\\(n\\)"))
iterations. 

In an important special case, namely when a loop uses a
natural numbers as an iteration variable,
the subtraction operation will account
for a constant overhead in total, since @tt{sub1} will be called
once for each different number in that range and those times 
sum to a fixed number, proportional to the number of iterations.

Accordingly, for this paper we just treat @tt{sub1} as constant-time primitive.
