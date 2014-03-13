#lang scribble/base
@(require "util.rkt" 
          "line-counts.rkt"
          "cite.rkt"
          scriblib/figure)

@title[#:tag "sec:case-study"]{Case Study}

@figure["fig:line-counts" "Line Counts"]{@build-table[]}

To better understand how well our monad works, we 
implemented all of the algorithms in @citet[three-algorithms-on-braun-trees]'s
paper, @italic{Three Algorithms on Braun Trees}. The paper contains 
several versions of each of the three functions, each with different
running times, culminating in efficient versions. The three
algorithms are 
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
the function @tt{copy_insert_time}.

The running time function, however, is defined in parallel to
@tt{log_sq} itself, not as the product of the logs:
@(apply inline-code (extract copy_log_sq.v "copy_insert_result"))
This makes it straightforward to prove that the running-time
matches that function, but then leaves as a separate issue
the proof that this function is Big Oh of the square of the log.
That is, there are 56 lines of proof to guarantee the result 
type of the function is correct and an additional 179 lines
to prove that that @tt{copy_insert_result}
is Big Oh of the product of the log.

This breakdown is typical and can be read off of the columns in @figure["fig:line-count"].

The @tt{Monad} and @tt{Common} lines count the number of lines of
code in our monad's implementation (including the proofs of the monad laws)
and some libraries used in multiple algorithms, including
a Big Oh library, a Log library, the Braun tree definition, and
some common facts about Braun trees.


@section{Extraction}

@italic{TODO: discuss extraction and give some examples. Show good extraction and
show how some extraction is "polluted" by functions that are defined 
by more complex recursive schemes.}
