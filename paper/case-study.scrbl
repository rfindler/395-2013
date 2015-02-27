#lang scribble/base
@(require "util.rkt" 
          "line-counts.rkt"
          "cite.rkt"
          scriblib/figure)

@title[#:tag "sec:case-study"]{Case Study}

@figure*["fig:line-counts" "Line Counts"]{@build-table[]}

To better understand how applicable our monad is, we 
implemented the search and insertion functions for 
red-black trees, insertion sort, merge sort, both
the naive recursive version of the nth Fibonacci number
function and the linear time version, and
all of the algorithms in @citet[three-algorithms-on-braun-trees]'s
paper, @italic{Three Algorithms on Braun Trees}.  Okasaki's paper contains 
several versions of each of the three functions, each with different
running times, in each case culminating with efficient versions. 
The three functions are
@itemlist[@item{@tt{size}: computes the size of a Braun tree 
                 (a linear and a log squared version)}
          @item{@tt{copy}: builds a Braun tree a given size
                 filled entirely with a given element
                 (a linear, a fib ∘ log, a log squared, and a log time version),
                 and}
          @item{@tt{make_array}: convert a list into a Braun tree
                 (two n log n versions and a linear version).}]
In total, we implemented 16 different functions using the monad.
For all of them, we proved the expected Big O running times. For
the naive fib, we proved that it is Big Ω and Big O of itself,
Big O(2@raw-latex{$^n$}), and Big Ω(2@raw-latex{$^{n/2}$}). For 
merge sort, we proved it is Big O(n log(n)) and Big Ω(n log(n)).
For all of the functions except for @tt{make_array_linear} and red-black insertion
we proved they are correct as well; for those we proved only the running times.

The supplementary material contains all of the Coq code for
the implementation and proofs of all of the functions in our case study.

@section{Line Counts}

The line counts for the various implementations of the algorithms
using our monad are shown in @figure-ref["fig:line-counts"].
The files whose names end in @tt{gen.v} are the output of the 
script that inserts @tt{+=} expressions, so they contain
the definitions of the various functions, but without the 
correctness conditions (or any of the proofs or data structure
definitions). There are more
than 15 because a number of the functions needed helper functions
that are in the monad (and thus require running time proofs).
As you can see, the functions are generally short. The
proofs are typically much longer.

We divided the line counts up into proofs that are inside obligations
(and thus correspond to establishing that the monadic types are
correct) and other lines of proofs. With the exception of the
@tt{make_array_linear} and the red-black tree insertion function, 
the proofs inside the obligations establish the correctness of the
functions and establish a basic running time result, 
but not one in terms of Big O. 

For example, @Figure-ref["fig:copy_log_sq"] is the definition of the
@tt{copy_log_sq} function, basically mirroring Okasaki's definition,
but in Coq's notation.

@figure["fig:copy_log_sq"
        @list{@tt{copy_log_sq}}
        @(apply inline-code (extract copy_log_sq_gen.v cdr))]

The monadic result type is
@(apply inline-code (extract copy_log_sq.v "copy_insert_result"))
which says that the result is a Braun tree whose size matches the
input natural number, that linearizing the resulting tree
produces the input list, and that the running time is given by
the function @tt{copy_log_sq_time}.

The running time function, however, is defined in parallel to
@tt{log_sq} itself, not as the product of the logs:
@(apply inline-code (extract copy_log_sq.v "copy_insert_time"))
This makes it straightforward to prove that the running-time
matches that function, but then leaves as a separate issue
the proof that this function is Big O of the square of the log.
That is, there are 56 lines of proof to guarantee the result 
type of the function is correct and an additional 179 lines
to prove that that @tt{copy_log_sq_time}
is Big O of the square of the log.

For the simpler functions (every one with linear running time
except @tt{make_array_linear}), the running time can
be expressed directly in the monadic result (with
precise constants). However, for most of the functions
the running time is expressed first precisely in a manner
that matches the structure of the function and then that
running time is proven to correspond to some asymptotic
complexity, as with @tt{copy_log_sq}. The precise line counts
can be read off of the columns in @figure-ref["fig:line-counts"].

The @tt{Monad} and @tt{Common} lines count the number of lines of
code in our monad's implementation (including the proofs of the monad laws)
and some libraries used in multiple algorithms, including
a Big O library, a Log library, the Braun tree definition, and
some common facts and definitions about Braun trees.

@section{Extraction}

The extracted functions naturally fall into two categories. In the first
category are functions that recur on the natural structure of their
inputs, e.g., functions that process lists by walking down the list
one element at a time, functions that process trees by processing
the children and combine the result, or functions that recursively process
numbers by counting down by ones from a given number. 
In the second category are functions that ``skip'' over some of their inputs.
For example, there  are functions consuming natural numbers that
recur by diving the number by 2 instead of subtracting one in 
Okasaki's algorithms, and merge sort recurs by dividing the list in half
at each step.

Functions in the first category extract into precisely the OCaml code
that you would expect, just like @tt{insert}, as discussed in 
@secref["sec:insert"].

Functions in the second category extract into code 
that is cluttered by Coq's support for non-simple
recursion schemes. That is, each function in Coq must
be proven to be well-defined and to terminate on all inputs.
Functions that don't simply follow the natural recursive structure
of their input get additional wrappers and useless data
structure.

The function @tt{copy_log_sq} is one such. Here is its output:
@(apply inline-code 
        (extract 
         extract.ml 
         (λ (all-lines)
           
           (define (chop-some-lines ls)
             (apply
              append
              (for/list ([l (in-list ls)])
                (cond
                  [(regexp-match #rx"n0[)][)][)] in copy_log_" l)
                   (define ls (regexp-split #rx" in " l))
                   (list (list-ref ls 0)
                         (string-append "      in " (list-ref ls 1)))]
                  [else
                   (list l)]))))
           
           (chop-some-lines
            (keep-range #rx"copy_log_sq" all-lines)))))
All of the extra pieces beyond what was written in the original
function are useless. In particular, the argument to @tt{copy_log_sq_func}
is a three-deep nested pair containing an integer (a real argument),
the value in the tree (also a real argument), 
and @tt{__} a constant that is defined at the top of the
extraction file that is never used for anything.
Similarly, the body of the function has the anonymous function that begins
@tt{fun f0 fS n ->} that is simply an extra wrapper around a conditional.
Simplifying these two away and inlining @tt{copy_log_sq_func} and
@tt{copy_log_sq0} results in this program:
@inline-code{
let rec copy_log_sq x0 n =
  if n=0 
  then Bt_mt
  else let n'=n-1 in
   let t = copy_log_sq x0 (div2 n') in
     match even_odd_dec n' with
      | false -> Bt_node (x0, t, t)
      | true -> Bt_node (x0, (insert x0 t), t))
}
which is precisely the code that we would expect (compare
with the Coq code for the same function in the previous
subsection). Similar simplifications apply to the other
functions in the second category and these changes
correspond to fairly aggressive inlining, something that we
would expect the OCaml compiler to do. (In contrast,
changing the signatures of functions to, say, remove an
abstract running-time count that is threaded throughout the
program is much more difficult and unlikely to be within the
grasp of compilers that support separate compilation like OCaml's.)
