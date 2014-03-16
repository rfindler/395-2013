#lang scribble/base
@(require "util.rkt" 
          "line-counts.rkt"
          "cite.rkt"
          scriblib/figure)

@title[#:tag "sec:case-study"]{Case Study}

@figure["fig:line-counts" "Line Counts"]{@build-table[]}

To better understand how well our monad works, we 
implemented all of the algorithms in @citet[three-algorithms-on-braun-trees]'s
paper, @italic{Three Algorithms on Braun Trees}. The
source code for our case study is on github: 
@centered{@url{https://github.com/rfindler/395-2013}.}

Okasaki's paper contains 
several versions of each of the three functions, each with different
running times, in case case culminating with efficient versions. 
The three algorithms are 
@itemlist[@item{@tt{size}: computes the size of a Braun tree 
                 (a linear and a log squared version)}
          @item{@tt{copy}: builds a Braun tree a given size
                 filled entirely with a given element
                 (a linear, a fib ∘ log, a log squared, and a log time version),
                 and}
          @item{@tt{make_array}: convert a list into a Braun tree
                 (two n log n versions and a linear version).}]

@section{Line Counts}

The line counts for the various implementations of the algorithms
using our monad are shown in @figure-ref["fig:line-counts"].
The files whose names end in @tt{gen.v} are the output of the 
script that inserts @tt{+=} expressions, so they contain
the complete definitions of the various functions and their
helper functions that we implemented. As you can see, the
functions are generally short. The proofs are typically much longer.

We divided the line counts up into proofs that are inside obligations
(and thus correspond to establishing that the monadic types are
correct) and other lines of proofs. With the exception of the
@tt{make_array_linear} files, the proofs inside the obligations
establish the correctness of the functions and establish a basic
running time result, but not one in terms of Big Oh. 

For example, this is the definition of the @tt{copy_log_sq} function,
basically mirroring Okasaki's definition, but in Coq's notation:
@(apply inline-code (extract copy_log_sq_gen.v cdr))

The monadic result type is
@(apply inline-code (extract copy_log_sq.v "copy_insert_result"))
which says that the result is a Braun whose size matches the
input natural number, that linearizing the result Braun tree
produces the input list, and that the running time is given by
the function @tt{copy_log_sq_time}.

The running time function, however, is defined in parallel to
@tt{log_sq} itself, not as the product of the logs:
@(apply inline-code (extract copy_log_sq.v "copy_insert_time"))
This makes it straightforward to prove that the running-time
matches that function, but then leaves as a separate issue
the proof that this function is Big Oh of the square of the log.
That is, there are 56 lines of proof to guarantee the result 
type of the function is correct and an additional 179 lines
to prove that that @tt{copy_log_sq_time}
is Big Oh of the product of the log.

For the simpler functions (the ones with linear running time 
except @tt{make_array_linear}), the running can
be expressed directly in the monadic result (with
precise constants), but for most of the functions,
the running time is expressed first in a manner
that matches the structure of the function and
a breakdown similar to @tt{copy_log_sq} is typical and
the precise numbers can be read off of the 
columns in @figure-ref["fig:line-counts"].

The @tt{Monad} and @tt{Common} lines count the number of lines of
code in our monad's implementation (including the proofs of the monad laws)
and some libraries used in multiple algorithms, including
a Big Oh library, a Log library, the Braun tree definition, and
some common facts and definitions about Braun trees.

@section{Extraction}

The extracted functions naturally fall into two categories. In the first
category are functions that recur on the natural structure of their
inputs, e.g., functions that process lists by walking down the list
one element at a time, functions that process trees by processing
the children and combine the result, or functions that recursively process
numbers by counting down by ones from a given number. 
In the second category are functions that ``skip'' over some of their inputs.
In our case study, the only such functions process numbers and generally
recur by diving the number by 2 instead of subtracting one.

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
           (keep-range #rx"copy_log_sq" all-lines))))
All of the extra pieces beyond what was written in the original
function are useless. In particular, the argument to @tt{copy_log_sq_func}
is a three-deep nested pair containing an integer (a real argument)
the value in the tree (also a real argument), 
and @tt{__} a constant that is defined at the top of the
extraction file that is never used for anything.
Similarly, the body of the function has the anonymous function that begins
@tt{fun f0 fS n ->} that is simply an extra wrapper around a conditional.
Simplifying these two away and inlining @tt{copy_log_sq_func} and
@tt{copy_log_sq0} this program:
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
which is precisely the code that we would expect (compare with the Coq
code for the same function in the previous subsection). Similar simplifications
apply to the other functions in the second category and these changes
correspond to fairly aggressive inlining, something that high-quality functional
language compilers tend to do.
