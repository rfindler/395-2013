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
to 0 are all constant-time operations. The algorithms
discussed in @secref["sec:case-study"] use two
operations on numbers besides those: @tt{+} and @tt{sub1}.

In general, addition of bignums is not constant time. However, certain
uses of addition can be replaced by constant-time bit operations. For
instance, doubling and adding 1 can be replaced by a specialized
operation that conses a @tt{1} on the front of the
bitstring. Fortunately, every time we use addition in one of the
functions in our Braun library, the operation can be replaced by one
of these efficient operations. 

One of the more interesting uses is in the linear version of 
@tt{size}, which has the sum @tt{lsize+rsize+1} where 
@tt{lsize} and @tt{rsize} are the sizes of two subtrees
of a Braun tree. This operation, at first glance, doesn't
seem to be a constant-time. But the Braun invariant tells
us that @tt{lsize} and @tt{rsize} are either equal, or
that @tt{lsize} is @tt{rsize+1}. Accordingly, this operation
can be replaced with either @tt{lsize*2+1} or @tt{lsize*2},
both of which are constant-time operations. Also, checking
to see which case applies is a constant time operation:
if the numbers are the same the leading digits will be the same
and if they differ by @tt{1}, the leading digits will be different.

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

There are four different recursion patterns using @tt{sub1}
in our library. The first and simplest is a function with a
loop counting down from @tt{n} to @tt{0}. This pattern is
found in the functions @tt{take}, @tt{drop} and
@tt{pad-drop} in the library. In this case, @tt{sub1} will
be called once for each different number in that range and
those times sum to a fixed number, proportional to the
number of iterations.

Second is a function that loops by subtracting @tt{1} and then dividing by @tt{2}.
This pattern is found in our functions @tt{copy2} and @tt{copy_insert}, and has a logarithmic 
overhead.

Third is the pattern used by @tt{diff}, which loops by division by @tt{2} of either @tt{n-1} 
or @tt{n-2} depending on the parity of the index. This is again a logarithmic overhead to
@tt{diff}, which has logarithmic complexity.

Finally, the most complicated is the pattern used by @tt{copy_linear}, which recursively
calls itself on @tt{n/2} and @tt{(n-1)/2}. This has been observed to be a linear overhead to
@tt{copy_linear}.

Accordingly, we believe that the overhead of using
@tt{sub1} in these functions does not change their
asymptotic complexity, but we have verified this only by
testing (and, in the first case, by a pencil-and-paper
proof).
